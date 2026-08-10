#!/usr/bin/env python3
"""
_count_steps.py -- Ground-truth proof-effort measurement for the Trocq ROI study.

Single source of truth for every tactic-step constant that appears in
_paper.tex, in the cost blocks of the bs_*.v files, in _roi*.md, and in the
figures produced by _graphs*.py.  Nothing downstream should hard-code a count.

COUNTING CONVENTION (period-terminated tactics)
-----------------------------------------------
  * One period-terminated tactic            = 1 step
  * A chained tactic  [t1; t2; t3.]         = 1 step
  * Bullet markers    [-] [+] [*] [{] [}]   = 0 steps
  * [Trocq Use ...]   vernacular commands   = counted separately, not as steps
  * Comments and whitespace                 = 0 steps

The convention is the one declared in bs_a1.v; this script makes it
mechanical so that no constant in the paper depends on a hand count.

Usage
-----
    python3 _count_steps.py                  # write _counts.csv + _counts.md
    python3 _count_steps.py --check          # verify, non-zero exit on anomaly

Outputs (written next to this script, absolute paths)
-----------------------------------------------------
    _counts.csv   one row per proof:  file, name, kind, steps, terminator, flags
    _counts.md    human-readable tables, grouped by file
"""

from __future__ import annotations

import argparse
import csv
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

HERE = Path(__file__).resolve().parent

# Vendored third-party sources.  Any file listed here is measured and
# reported for completeness but MUST NOT enter the effort totals: it is not
# authored effort of this study, so counting it would inflate every constant.
#
# Currently empty.  bs_m1_sf_maps.v (a verbatim copy of the "Maps" chapter of
# Software Foundations vol. 1) lived here until 2026-08-10; it was removed
# from the repository because nothing imported it.  The map interface it
# describes is still the basis of bs_m1.v, which cites it in its header.
THIRD_PARTY: set[str] = set()

# Vernacular that opens something a Proof block may close.
DECL_RE = re.compile(
    r"^\s*(?:Global\s+|Local\s+|#\[[^\]]*\]\s*)?"
    r"(Theorem|Lemma|Corollary|Proposition|Remark|Fact|Definition|Example|Instance|Goal)"
    r"\b\s*([A-Za-z_][A-Za-z0-9_']*)?",
    re.MULTILINE,
)

PROOF_OPEN_RE = re.compile(r"\bProof\b\s*\.")
TERMINATOR_RE = re.compile(r"\b(Qed|Defined|Admitted|Abort|Save)\b\s*\.")
TROCQ_USE_RE = re.compile(r"^\s*Trocq\s+Use\s+([A-Za-z_][A-Za-z0-9_'.]*)\s*\.", re.MULTILINE)
TROCQ_REGISTER_RE = re.compile(r"^\s*Trocq\s+Register\b", re.MULTILINE)

# A line whose first non-space content is only bullet punctuation.
BULLET_ONLY_RE = re.compile(r"^\s*(?:[-+*]+|[{}])\s*$")
BULLET_LEAD_RE = re.compile(r"^\s*(?:[-+*]{1,4}|[{}])\s+")

# Tactics that are deliberate failures / non-productive markers.
FAIL_RE = re.compile(r"\b(Fail|Abort|Admitted|admit)\b")


def strip_comments(src: str) -> str:
    """Remove Coq comments, honouring nesting and string literals.

    Replaces comment bodies with spaces so that byte offsets and line
    numbers are preserved for downstream reporting.
    """
    out = []
    depth = 0
    i = 0
    n = len(src)
    in_string = False
    while i < n:
        ch = src[i]
        nxt = src[i + 1] if i + 1 < n else ""

        if in_string:
            # Coq escapes a double quote by doubling it.
            if ch == '"':
                if nxt == '"':
                    out.append('  ' if depth else '""')
                    i += 2
                    continue
                in_string = False
            out.append(' ' if depth else ch)
            i += 1
            continue

        if depth == 0 and ch == '"':
            in_string = True
            out.append(ch)
            i += 1
            continue

        if ch == "(" and nxt == "*":
            depth += 1
            out.append("  ")
            i += 2
            continue

        if ch == "*" and nxt == ")" and depth > 0:
            depth -= 1
            out.append("  ")
            i += 2
            continue

        if depth > 0:
            # Preserve newlines so line numbering survives.
            out.append("\n" if ch == "\n" else " ")
        else:
            out.append(ch)
        i += 1

    return "".join(out)


def split_top_level_periods(body: str) -> list[str]:
    """Split a proof body into period-terminated sentences.

    A period ends a sentence only at bracket depth zero and only when it is
    followed by whitespace or end-of-input -- this keeps qualified names
    (Nat.add, Param44.Rel) and numeric literals from splitting a sentence.
    """
    sentences: list[str] = []
    depth = 0
    cur: list[str] = []
    i = 0
    n = len(body)
    while i < n:
        ch = body[i]
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth = max(0, depth - 1)

        if ch == "." and depth == 0:
            prev = body[i - 1] if i else " "
            nxt = body[i + 1] if i + 1 < n else "\n"
            # Qualified identifier: Foo.bar -- not a sentence end.
            qualified = (prev.isalnum() or prev == "_") and (nxt.isalnum() or nxt == "_")
            ellipsis = nxt == "."
            if not qualified and not ellipsis and (nxt.isspace() or i + 1 == n):
                cur.append(ch)
                sentences.append("".join(cur))
                cur = []
                i += 1
                continue
        cur.append(ch)
        i += 1

    tail = "".join(cur).strip()
    if tail:
        sentences.append(tail)
    return sentences


def count_steps(body: str) -> tuple[int, list[str]]:
    """Count period-terminated tactic steps in a (comment-free) proof body."""
    steps = 0
    flags: list[str] = []
    for raw in split_top_level_periods(body):
        s = raw.strip()
        if not s:
            continue

        # Strip any leading bullet punctuation; bullets themselves cost 0.
        stripped = s
        while True:
            m = BULLET_LEAD_RE.match(stripped)
            if not m:
                break
            stripped = stripped[m.end():]
        if BULLET_ONLY_RE.match(s) or not stripped.strip(" .-+*{}"):
            continue

        if FAIL_RE.search(stripped):
            flags.append("deliberate-failure")

        steps += 1
    return steps, flags


@dataclass
class Proof:
    file: str
    name: str
    kind: str
    steps: int
    terminator: str
    line: int
    flags: list[str] = field(default_factory=list)


def parse_file(path: Path) -> tuple[list[Proof], int, int]:
    raw = path.read_text(encoding="utf-8", errors="replace")
    src = strip_comments(raw)

    trocq_uses = len(TROCQ_USE_RE.findall(src))
    trocq_registers = len(TROCQ_REGISTER_RE.findall(src))

    proofs: list[Proof] = []
    pos = 0
    while True:
        m_open = PROOF_OPEN_RE.search(src, pos)
        if not m_open:
            break
        m_end = TERMINATOR_RE.search(src, m_open.end())
        if not m_end:
            break

        body = src[m_open.end():m_end.start()]
        steps, flags = count_steps(body)

        # Nearest preceding declaration gives the name/kind.
        head = src[:m_open.start()]
        decls = list(DECL_RE.finditer(head))
        if decls:
            kind = decls[-1].group(1)
            name = decls[-1].group(2) or "<anonymous Goal>"
        else:
            kind, name = "?", "<unknown>"

        proofs.append(
            Proof(
                file=path.name,
                name=name,
                kind=kind,
                steps=steps,
                terminator=m_end.group(1),
                line=src[:m_open.start()].count("\n") + 1,
                flags=flags,
            )
        )
        pos = m_end.end()

    return proofs, trocq_uses, trocq_registers


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--check", action="store_true", help="exit non-zero if anomalies found")
    args = ap.parse_args()

    files = sorted(HERE.glob("bs_*.v"))
    if not files:
        print(f"no bs_*.v files found under {HERE}", file=sys.stderr)
        return 2

    all_proofs: list[Proof] = []
    per_file: dict[str, tuple[int, int, int]] = {}  # name -> (steps, uses, registers)

    for path in files:
        proofs, uses, registers = parse_file(path)
        all_proofs.extend(proofs)
        per_file[path.name] = (sum(p.steps for p in proofs), uses, registers)

    csv_path = HERE / "_counts.csv"
    with csv_path.open("w", newline="", encoding="utf-8") as fh:
        w = csv.writer(fh)
        w.writerow(
            ["file", "line", "kind", "name", "steps", "terminator", "provenance", "flags"]
        )
        for p in all_proofs:
            w.writerow([
                p.file, p.line, p.kind, p.name, p.steps, p.terminator,
                "third-party" if p.file in THIRD_PARTY else "authored",
                ";".join(p.flags),
            ])

    md: list[str] = []
    md.append("# Proof-step ground truth\n")
    md.append("Generated by `_count_steps.py`. Convention: one period-terminated ")
    md.append("tactic = 1 step; `t1; t2.` = 1 step; bullets = 0 steps; ")
    md.append("`Trocq Use` counted separately as commands.\n\n")

    md.append("Files marked *third-party* are vendored sources; they are reported ")
    md.append("for completeness but excluded from the effort totals.\n\n")

    md.append("## Per-file totals\n\n")
    md.append("| File | Proofs | Tactic steps | `Trocq Use` | `Trocq Register` | Provenance |\n")
    md.append("|---|---:|---:|---:|---:|---|\n")
    authored = [0, 0, 0, 0]  # proofs, steps, uses, registers
    for name in sorted(per_file):
        steps, uses, registers = per_file[name]
        cnt = sum(1 for p in all_proofs if p.file == name)
        third = name in THIRD_PARTY
        tag = "third-party" if third else "authored"
        md.append(f"| `{name}` | {cnt} | {steps} | {uses} | {registers} | {tag} |\n")
        if not third:
            authored[0] += cnt
            authored[1] += steps
            authored[2] += uses
            authored[3] += registers
    md.append(
        f"| **TOTAL (authored only)** | **{authored[0]}** | **{authored[1]}** | "
        f"**{authored[2]}** | **{authored[3]}** | |\n"
    )

    md.append("\n## Per-proof detail\n")
    for name in sorted(per_file):
        rows = [p for p in all_proofs if p.file == name]
        if not rows:
            continue
        md.append(f"\n### `{name}`\n\n")
        md.append("| Line | Kind | Name | Steps | End | Flags |\n")
        md.append("|---:|---|---|---:|---|---|\n")
        for p in rows:
            md.append(
                f"| {p.line} | {p.kind} | `{p.name}` | {p.steps} | {p.terminator} | "
                f"{', '.join(p.flags) or '--'} |\n"
            )

    md_path = HERE / "_counts.md"
    md_path.write_text("".join(md), encoding="utf-8")

    anomalies = [p for p in all_proofs if p.terminator in {"Admitted", "Abort"} or p.flags]
    print(f"parsed {len(files)} files, {len(all_proofs)} proofs")
    print(f"wrote {csv_path}")
    print(f"wrote {md_path}")
    if anomalies:
        print(f"\n{len(anomalies)} flagged (deliberate failures / unfinished):")
        for p in anomalies:
            print(f"  {p.file}:{p.line} {p.name} [{p.terminator}] {','.join(p.flags) or ''}")

    if args.check and anomalies:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

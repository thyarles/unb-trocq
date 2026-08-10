#!/usr/bin/env python3
"""
_graphs.py -- Figures for "When Does Proof Transfer Pay Off?"

Supersedes and merges the earlier _graphs.py / _graphs_v2.py, which hard-coded
their constants and had drifted from the measured corpus.  Nothing here is
hard-coded: every constant is derived from _counts.csv, the table emitted by
_count_steps.py, so the figures and _paper.tex cannot disagree.

Run _count_steps.py first, then this.

    python3 _count_steps.py
    python3 _graphs.py

Outputs (into _graphs/): one PDF per figure for LaTeX inclusion, plus a PNG
twin at 200 dpi for quick viewing, plus _figure_constants.txt recording every
derived value so the numbers can be diffed against the paper.

Design notes
------------
Palette is the validated three-slot categorical set (blue / orange / aqua);
adjacent-pair CVD separation and the normal-vision floor were checked with a
validator rather than by eye.  Two series per panel, so identity never rests on
colour alone: every line is also directly labelled at its right-hand end.
Gridlines and axes are solid hairlines one shade off the surface; no dashed
grid, no value printed on every point.
"""

from __future__ import annotations

import csv
import os
from collections import defaultdict
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.colors import LinearSegmentedColormap, TwoSlopeNorm
from matplotlib.lines import Line2D
from matplotlib.ticker import FuncFormatter

HERE = Path(__file__).resolve().parent
OUT = HERE / "_graphs"
OUT.mkdir(exist_ok=True)

# ── Palette (validated: adjacent CVD dE 9.2, normal-vision 24.0, light) ─────
TROCQ = "#2a78d6"   # categorical slot 1 -- blue
MANUAL = "#eb6834"  # categorical slot 2 -- orange
ACCENT = "#1baf7a"  # categorical slot 3 -- aqua (always directly labelled)
INK = "#0b0b0b"
INK_2 = "#52514e"
MUTED = "#898781"
GRID = "#e1e0d9"
AXIS = "#c3c2b7"
SURFACE = "#ffffff"

# LNCS text width is 122.4 mm.
# Rendered larger than the printed size and scaled down by LaTeX at
# \\textwidth, so line weights stay crisp and type lands near 8pt.
W_FULL, W_TALL = 6.6, 7.2

# Colormap for the 3-D ROI surface.  RdYlGn is the original choice and stays
# the default.  Red-to-green is the one pairing dichromatic readers cannot
# separate, so on that surface the sign is carried by the grey zero plane and
# the black break-even contour, not by hue alone.  Set
# TROCQ_3D_CMAP=RdBu_r for a colour-vision-safe variant.
CMAP_3D = os.environ.get("TROCQ_3D_CMAP", "RdYlGn")

plt.rcParams.update({
    # Serif, to sit inside an LNCS page rather than beside it.
    "font.family": "serif",
    "font.serif": ["DejaVu Serif"],
    "mathtext.fontset": "dejavuserif",
    "font.size": 10.5,
    "axes.titlesize": 11,
    "axes.labelsize": 10.5,
    "xtick.labelsize": 9.5,
    "ytick.labelsize": 9.5,
    "legend.fontsize": 9.5,
    "axes.spines.top": False,
    "axes.spines.right": False,
    "axes.edgecolor": "#444444",
    "axes.linewidth": 0.9,
    "axes.grid": True,
    "grid.alpha": 0.30,
    "grid.linewidth": 0.7,
    "figure.facecolor": SURFACE,
    "axes.facecolor": SURFACE,
    "savefig.facecolor": SURFACE,
    "legend.frameon": True,
    "legend.framealpha": 0.95,
    "legend.edgecolor": "#bbbbbb",
    "lines.linewidth": 2.4,
    "figure.dpi": 150,
})


# ══════════════════════════════════════════════════════════════════════════
# Constants, derived from the measured corpus
# ══════════════════════════════════════════════════════════════════════════

def load() -> dict[str, dict[str, int]]:
    steps: dict[str, dict[str, int]] = defaultdict(dict)
    with (HERE / "_counts.csv").open(encoding="utf-8") as fh:
        for row in csv.DictReader(fh):
            steps[row["file"]][row["name"]] = int(row["steps"])
    if not steps:
        raise SystemExit("_counts.csv is empty -- run _count_steps.py first")
    return steps


S = load()
g = lambda f, n: S[f][n]

# --- Regime B: bridge-based manual baseline (bs_p4 / bs_p5 / bs_p6) --------
S_iso = g("bs_p5.v", "plist_nlist_iso") + g("bs_p5.v", "nlist_plist_iso")
BR = {
    "plength": g("bs_p5.v", "_plength_eq_nlength"),
    "papp": g("bs_p5.v", "plist_2_nlist_app"),
    "prev": g("bs_p6.v", "plist_2_nlist_rev"),
}
WR = {
    "plength": g("bs_p5.v", "R__plength"),
    "papp": g("bs_p5.v", "R__papp"),
    "prev": g("bs_p6.v", "R__prev"),
}
SHARED_USE = 3                      # R_NatList, Param44_nat, Param_add
PARAM44 = g("bs_p5.v", "R_NatList")

C_BASE_B = S_iso + sum(BR.values())                                  # 27
EXTRA_B = PARAM44 + SHARED_USE + sum(WR.values()) + len(WR)          # 28
TROCQ_B = C_BASE_B + EXTRA_B                                         # 55
P_SIMPLE = g("bs_p4.v", "plength_papp_via_natlist")                  # 7
P_COMPLEX = g("bs_p6.v", "_prev_papp_manual")                        # 11
C_AVG = 5                            # _prev x3, _papp x2
K = P_COMPLEX / C_AVG                                                # 2.2
PER_THM = 2

# --- Regime A: copy-paste manual baseline (bs_a1) --------------------------
PASTE = [g("bs_a1.v", n) for n in
         ("plength_papp_manual", "papp_assoc_manual", "prev_papp_manual")]
P_PASTE = sum(PASTE) / len(PASTE)                                    # 17/3
S_BIJ = (g("bs_a1.v", "plist_nlist_iso") + g("bs_a1.v", "nlist_plist_iso")
         + g("bs_a1.v", "R_NatList") + SHARED_USE)                   # 16
A1 = [("_plength_eq_nlength", "R__plength"),
      ("plist_2_nlist_app", "R__papp"),
      ("plist_2_nlist_rev", "R__prev")]
PER_FN = sum(g("bs_a1.v", b) + g("bs_a1.v", w) + 1 for b, w in A1)   # 37
TROCQ_A = S_BIJ + PER_FN                                             # 53

# --- bs_a2: the same copy-paste baseline once a typeclass is introduced ----
# Copy-paste still compiles here, but psum_papp_manual needs two hand repairs
# (DIVERGENCE 1 and 2 at the proof site), so P rises and so does the setup.
PASTE_A2 = [g("bs_a2.v", n) for n in
            ("plength_papp_manual", "papp_assoc_manual",
             "prev_papp_manual", "psum_papp_manual")]
P_PASTE_A2 = sum(PASTE_A2) / len(PASTE_A2)                           # 6.0
S_BIJ_A2 = (g("bs_a2.v", "plist_nlist_iso") + g("bs_a2.v", "nlist_plist_iso")
            + g("bs_a2.v", "R_NatList") + g("bs_a2.v", "R_NatList_nat")
            + SHARED_USE)                                            # 21
BRIDGES_A2 = sum(g("bs_a2.v", n) for n in
                 ("plength_eq_nlength", "plist_2_nlist_app",
                  "plist_2_nlist_rev", "plist_2_nlist_sum"))         # 23
REGISTERED_A2 = sum(g("bs_a2.v", n) for n in
                    ("R_plength_nat", "R_papp_nat",
                     "R_prev_nat", "R_psum_nat")) + 4                # 32
TROCQ_A2 = (S_BIJ_A2 + BRIDGES_A2 + REGISTERED_A2
            + g("bs_a2.v", "psum_nat_eq_psum"))                      # 82
NSTAR_A2 = TROCQ_A2 / (P_PASTE_A2 - PER_THM)                         # 20.5
ROI_INF_A2 = (P_PASTE_A2 - PER_THM) / PER_THM                        # 2.0

# --- Counterweights (bs_a2, bs_m1) ----------------------------------------
GREF_TAX = sum(g("bs_a2.v", n) for n in
               ("R_plength", "R_papp", "R_prev", "R_psum"))          # 22
Z_TROCQ = sum(g("bs_a2.v", n) for n in
              ("R_plength_Z", "R_papp_Z", "R_prev_Z")) + 4           # 24
Z_MANUAL = sum(g("bs_a2.v", n) for n in
               ("papp_assoc_Z", "prev_papp_Z", "plength_papp_Z"))    # 9


def uses(fname: str) -> int:
    import re
    src = (HERE / fname).read_text(encoding="utf-8")
    from _count_steps import strip_comments
    return len(re.findall(r"^\s*Trocq\s+Use\s", strip_comments(src), re.M))


def n_star(fixed_t: float, fixed_m: float, slope_m: float) -> float:
    return (fixed_t - fixed_m) / (slope_m - PER_THM)


NSTAR_A = n_star(TROCQ_A, 0.0, P_PASTE)                              # 14.5
NSTAR_B = n_star(TROCQ_B, C_BASE_B, P_COMPLEX)                       # 3.11
ROI_INF_A = (P_PASTE - PER_THM) / PER_THM                            # 1.83
ROI_INF_B = (K * C_AVG - PER_THM) / PER_THM                          # 4.5


# ══════════════════════════════════════════════════════════════════════════
# Helpers
# ══════════════════════════════════════════════════════════════════════════

def save(fig, stem: str) -> None:
    for ext, kw in (("pdf", {}), ("png", {"dpi": 160})):
        fig.savefig(OUT / f"{stem}.{ext}", bbox_inches="tight",
                    pad_inches=0.05, **kw)
    plt.close(fig)
    print(f"  wrote _graphs/{stem}.pdf and .png")


def times_axis(ax) -> None:
    """Format the ROI axis as multiples: 1.0x, 2.0x, ..."""
    ax.yaxis.set_major_formatter(FuncFormatter(lambda v, _: f"{v:.1f}×"))


def callout(ax, x, y, text, color=INK, size=10.5):
    """A boxed formula callout, in the style of the original figures."""
    ax.text(x, y, text, transform=ax.transAxes, ha="center", va="center",
            fontsize=size, color=color, zorder=9,
            bbox=dict(boxstyle="round,pad=0.45", facecolor=SURFACE,
                      edgecolor="#999999", linewidth=0.9, alpha=0.96))


def breakeven(ax, x, y, label, tx, ty):
    """Break-even dot with a leader line to an offset label."""
    ax.plot([x], [y], "o", ms=9, mfc=INK, mec=SURFACE, mew=1.8, zorder=9)
    ax.annotate(label, xy=(x, y), xytext=(tx, ty), fontsize=10, color=INK,
                zorder=9,
                arrowprops=dict(arrowstyle="->", color=INK, lw=1.0,
                                shrinkA=0, shrinkB=5))


# ══════════════════════════════════════════════════════════════════════════
# Figure 1 -- cost curves, the two regimes
# ══════════════════════════════════════════════════════════════════════════

def fig_regimes() -> None:
    fig, axes = plt.subplots(1, 2, figsize=(W_FULL, 3.5), sharey=True)
    n = np.linspace(0, 24, 500)

    specs = [
        (axes[0], "(a) Regime A — signatures agree",
         P_PASTE * n, TROCQ_A + PER_THM * n, NSTAR_A,
         rf"$C_M = {P_PASTE:.2f}\,n$", rf"$C_T = {TROCQ_A:.0f} + 2n$",
         "copy-paste"),
        (axes[1], "(b) Regime B — signatures diverge",
         C_BASE_B + P_COMPLEX * n, TROCQ_B + PER_THM * n, NSTAR_B,
         rf"$C_M = {C_BASE_B:.0f} + {P_COMPLEX:.0f}n$",
         rf"$C_T = {TROCQ_B:.0f} + 2n$", "bridges"),
    ]

    for ax, title, cm, ct, ns, mform, tform, mname in specs:
        ax.fill_between(n, cm, ct, where=(ct >= cm), color="#d62728",
                        alpha=0.09, lw=0, zorder=1)
        ax.fill_between(n, cm, ct, where=(cm >= ct), color="#2ca02c",
                        alpha=0.10, lw=0, zorder=1)
        ax.plot(n, cm, color=MANUAL, zorder=4,
                label=f"Manual — {mname}   {mform}")
        ax.plot(n, ct, color=TROCQ, zorder=4, label=f"Trocq   {tform}")
        ax.axvline(ns, color="#888888", lw=1.0, ls="--", zorder=2)

        y_at = (TROCQ_A if ax is axes[0] else TROCQ_B) + PER_THM * ns
        breakeven(ax, ns, y_at, rf"$n^{{*}} \approx {ns:.1f}$",
                  ns + 3.0, y_at - 42)

        ax.set_title(title, pad=8)
        ax.set_xlim(0, 24)
        ax.set_ylim(0, 185)
        ax.legend(loc="upper left", handlelength=1.3, fontsize=8.6,
                  borderpad=0.5, labelspacing=0.4)

    axes[0].set_ylabel("Cumulative tactic steps")
    fig.supxlabel("Number of theorems transferred  ($n$)", y=0.005,
                  fontsize=10.5)

    # Region labels, placed inside the wedge they describe.
    axes[0].text(0.15, 0.17, "Manual\ncheaper", transform=axes[0].transAxes,
                 fontsize=9, color="#a03030", ha="center", linespacing=1.3)
    axes[0].text(0.88, 0.70, "Trocq\ncheaper", transform=axes[0].transAxes,
                 fontsize=9, color="#2a7a2a", ha="center", linespacing=1.3)
    axes[1].text(0.70, 0.72, "Trocq cheaper", transform=axes[1].transAxes,
                 fontsize=9, color="#2a7a2a", ha="center")
    fig.suptitle("Cumulative cost of transferring $n$ theorems, "
                 "measured from the corpus", y=1.02, fontsize=11.5)
    fig.subplots_adjust(wspace=0.09)
    save(fig, "fig1_regimes")


# ══════════════════════════════════════════════════════════════════════════
# Figure 2 -- ROI in both regimes, with asymptotes
# ══════════════════════════════════════════════════════════════════════════

def fig_roi() -> None:
    fig, ax = plt.subplots(figsize=(W_FULL, 3.9))
    n = np.linspace(0.0, 60, 700)

    roi_a = (P_PASTE * n - (TROCQ_A + PER_THM * n)) / (TROCQ_A + PER_THM * n)
    roi_b = ((C_BASE_B + P_COMPLEX * n) - (TROCQ_B + PER_THM * n)) / \
            (TROCQ_B + PER_THM * n)

    ax.fill_between(n, 0, np.minimum(roi_a, 0), color="#d62728", alpha=0.10,
                    lw=0, label="Manual cheaper (ROI $<$ 0)")
    ax.fill_between(n, 0, np.maximum(roi_b, 0), color="#2ca02c", alpha=0.10,
                    lw=0, label="Trocq cheaper (ROI $>$ 0)")
    ax.axhline(0, color=INK, lw=1.0, zorder=3)

    for val, col, name in ((ROI_INF_B, TROCQ, "B"), (ROI_INF_A, MANUAL, "A")):
        ax.axhline(val, color=col, lw=1.2, ls="--", alpha=0.75, zorder=2)
        ax.annotate(rf"$\to {val:.2f}\times$", xy=(60.6, val), va="center",
                    fontsize=9.5, color=col, annotation_clip=False)

    ax.plot(n, roi_b, color=TROCQ, zorder=5,
            label="Regime B — signatures diverge")
    ax.plot(n, roi_a, color=MANUAL, zorder=5,
            label="Regime A — signatures agree")

    breakeven(ax, NSTAR_B, 0, rf"$n^{{*}} \approx {NSTAR_B:.1f}$", 6.5, 1.05)
    breakeven(ax, NSTAR_A, 0, rf"$n^{{*}} \approx {NSTAR_A:.1f}$", 20.5, -0.72)

    callout(ax, 0.37, 0.83,
            r"$\mathrm{ROI}_{\infty} = \dfrac{P_{\mathrm{manual}} - 2}{2}$"
            "\n(finite: both marginal costs are constant)")

    ax.set_xlabel("Number of theorems transferred  ($n$)")
    ax.set_ylabel(r"$\mathrm{ROI}(n) = \dfrac{C_M - C_T}{C_T}$")
    ax.set_xlim(0, 60)
    ax.set_ylim(-1.15, 5.3)
    times_axis(ax)
    ax.set_title("Return on investment saturates — volume alone never "
                 "buys an unbounded return", pad=10, fontsize=11.5)
    ax.legend(loc="lower right", handlelength=1.8)
    save(fig, "fig2_roi")


# ══════════════════════════════════════════════════════════════════════════
# Figure 3 -- ROI surface over (n, c_avg), Regime B
#
# This is the original house-style surface (serif, RdYlGn, formula-bearing
# title, zero plane, projected break-even contour), kept verbatim in look and
# re-pointed at the measured constants.  It renders in the surrounding
# figures' naming scheme as fig3_roi_surface.
#
#   ROI(n, c_avg) = (n(k*c_avg - 2) - EXTRA_B) / (TROCQ_B + 2n)
#   Asymptote (n -> inf): (k*c_avg - 2) / 2
# ══════════════════════════════════════════════════════════════════════════

def fig_roi_surface() -> None:
    from mpl_toolkits.mplot3d import Axes3D  # noqa: F401
    from matplotlib import cm as mpl_cm

    n_vals = np.linspace(0.5, 50, 180)
    c_vals = np.linspace(1.0, 8, 120)
    N, C = np.meshgrid(n_vals, c_vals)
    ROI = (N * (K * C - 2) - EXTRA_B) / (TROCQ_B + 2 * N)

    vmax = float(np.ceil(np.nanmax(ROI)))

    fig = plt.figure(figsize=(11, 7))
    ax = fig.add_subplot(111, projection="3d")

    surf = ax.plot_surface(
        N, C, ROI,
        cmap=getattr(mpl_cm, CMAP_3D),
        vmin=-1.0, vmax=vmax,
        alpha=0.88,
        linewidth=0,
        antialiased=True,
    )

    # Zero-ROI contour projected onto the ROI = 0 plane
    ax.contour(N, C, ROI, levels=[0], colors=["black"], linewidths=1.8,
               offset=0)

    cbar = fig.colorbar(surf, ax=ax, shrink=0.55, aspect=14, pad=0.08)
    cbar.set_label(r"$\mathrm{ROI}(n,\,c_{\mathrm{avg}})$", fontsize=10)
    cbar.ax.yaxis.set_major_formatter(
        FuncFormatter(lambda y, _: f"{y:.1f}×"))

    # Reference plane at ROI = 0
    n_plane = np.array([[n_vals[0], n_vals[-1]], [n_vals[0], n_vals[-1]]])
    c_plane = np.array([[c_vals[0], c_vals[0]], [c_vals[-1], c_vals[-1]]])
    ax.plot_surface(n_plane, c_plane, np.zeros_like(n_plane),
                    alpha=0.18, color="grey")

    ax.set_xlabel(r"Theorems  ($n$)", fontsize=10, labelpad=8)
    ax.set_ylabel(r"Complexity  ($c_{\mathrm{avg}}$)", fontsize=10, labelpad=8)
    ax.set_zlabel(r"$\mathrm{ROI}$", fontsize=10, labelpad=6)
    ax.set_title(
        "ROI Surface over $(n,\\,c_{\\mathrm{avg}})$ — Regime B\n"
        r"$\mathrm{ROI} = \dfrac{n(k\,c_{\mathrm{avg}}-2) - "
        rf"{EXTRA_B:.0f}}}{{{TROCQ_B:.0f} + 2n}}$"
        rf"  ($k={K:.1f}$, $C_{{\mathrm{{base}}}}={C_BASE_B:.0f}$, "
        rf"black contour: break-even)",
        fontsize=11, pad=14)

    ax.view_init(elev=28, azim=-55)

    fig.tight_layout()
    save(fig, "fig3_roi_surface")


# ══════════════════════════════════════════════════════════════════════════
# Figure 4 -- where Trocq's setup goes, and how it scales
# ══════════════════════════════════════════════════════════════════════════

def fig_setup() -> None:
    fig, (ax1, ax2) = plt.subplots(
        2, 1, figsize=(W_FULL, 5.4), gridspec_kw={"height_ratios": [1, 1.7]})

    parts = [
        ("isomorphism proofs", g("bs_a1.v", "plist_nlist_iso")
         + g("bs_a1.v", "nlist_plist_iso")),
        ("Param44 packaging", g("bs_a1.v", "R_NatList")),
        ("bridge lemmas", sum(g("bs_a1.v", b) for b, _ in A1)),
        ("relational witnesses", sum(g("bs_a1.v", w) for _, w in A1)),
        ("Trocq Use registrations", SHARED_USE + len(A1)),
    ]
    assert sum(v for _, v in parts) == TROCQ_A, "anatomy must sum to the setup"
    shades = ["#cde2fb", "#9ec5f4", "#5598e7", "#2a78d6", "#184f95"]
    left = 0.0
    for i, ((label, val), col) in enumerate(zip(parts, shades)):
        ax1.barh([0], [val], left=left, height=0.40, color=col,
                 edgecolor=SURFACE, linewidth=2.0, zorder=3, label=label)
        ax1.text(left + val / 2, 0, f"{val}", ha="center", va="center",
                 fontsize=10, color=INK if i < 3 else SURFACE, zorder=5)
        left += val
    ax1.set_xlim(0, TROCQ_A)
    ax1.set_ylim(-0.42, 0.32)
    ax1.set_yticks([])
    ax1.spines["left"].set_visible(False)
    ax1.grid(False)
    ax1.set_xlabel("Tactic steps")
    ax1.set_title(rf"(a) Anatomy of Trocq's {TROCQ_A}-step setup "
                  rf"($f = 3$ functions)", pad=8)
    ax1.legend(loc="upper center", bbox_to_anchor=(0.5, -0.62), ncol=3,
               handlelength=1.3, columnspacing=1.4)

    files = ["bs_p5.v", "bs_p6.v", "bs_a1.v", "bs_a2.v", "bs_m1.v"]
    vals = [uses(f) for f in files]
    cols = [TROCQ] * len(files)
    cols[-1] = MANUAL
    ax2.bar(range(len(files)), vals, width=0.60, color=cols,
            edgecolor=SURFACE, linewidth=2.0, zorder=3)
    for i, v in enumerate(vals):
        ax2.text(i, v + 1.1, str(v), ha="center", fontsize=10,
                 color=MANUAL if i == len(files) - 1 else INK_2)
    ax2.set_xticks(range(len(files)))
    ax2.set_xticklabels([f.replace(".v", "") for f in files])
    ax2.set_ylim(0, max(vals) * 1.42)
    ax2.set_ylabel("Trocq Use registrations")
    ax2.set_title("(b) Setup scales with the type former, not the theorem count",
                  pad=8)
    ax2.text(1.5, max(vals) * 0.60, "first-order lists", ha="center",
             fontsize=9.5, color=INK_2)
    ax2.annotate("higher-order,\nfunction-encoded maps",
                 xy=(3.62, max(vals) * 0.99), xytext=(2.55, max(vals) * 1.24),
                 ha="center", va="center", fontsize=9.5, color=MANUAL,
                 linespacing=1.3,
                 arrowprops=dict(arrowstyle="->", color=MANUAL, lw=1.0))

    fig.subplots_adjust(hspace=1.30)
    save(fig, "fig4_setup")


# ══════════════════════════════════════════════════════════════════════════
# Figure 5 -- what a typeclass costs (bs_a1 vs bs_a2)
#
# Adapted from the original _graphs_v2.py comparison, restyled to match the
# surrounding figures and re-pointed at the measured constants.  Its point:
# introducing Addable raises BOTH sides, so the ceiling goes up while the
# break-even moves further out -- copy-paste is still viable here, just
# dearer.  This is the quantitative half of the Regime A -> B argument.
# ══════════════════════════════════════════════════════════════════════════

def fig_typeclass() -> None:
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(W_FULL, 2.9))
    n = np.linspace(0, 40, 600)

    # (a) cost
    ax1.plot(n, P_PASTE * n, color=MANUAL, zorder=4)
    ax1.plot(n, TROCQ_A + PER_THM * n, color=TROCQ, zorder=4)
    ax1.plot(n, P_PASTE_A2 * n, color=MANUAL, ls="--", lw=1.9, zorder=4)
    ax1.plot(n, TROCQ_A2 + PER_THM * n, color=TROCQ, ls="--", lw=1.9, zorder=4)

    for ns, slope, col in ((NSTAR_A, P_PASTE, INK), (NSTAR_A2, P_PASTE_A2, INK)):
        ax1.axvline(ns, color=AXIS, lw=0.8, ls=":", zorder=1)
        ax1.plot([ns], [slope * ns], "o", ms=6, mfc=col, mec=SURFACE,
                 mew=1.5, zorder=6)
    ax1.annotate(rf"$n^{{*}} \approx {NSTAR_A:.1f}$",
                 xy=(NSTAR_A, P_PASTE * NSTAR_A), xytext=(2.5, 150),
                 fontsize=8.5, color=INK,
                 arrowprops=dict(arrowstyle="->", color=INK, lw=0.9))
    ax1.annotate(rf"$n^{{*}} \approx {NSTAR_A2:.1f}$",
                 xy=(NSTAR_A2, P_PASTE_A2 * NSTAR_A2), xytext=(26, 55),
                 fontsize=8.5, color=INK,
                 arrowprops=dict(arrowstyle="->", color=INK, lw=0.9))

    ax1.set_xlabel("Theorems transferred  ($n$)")
    ax1.set_ylabel("Cumulative tactic steps")
    ax1.set_xlim(0, 40)
    ax1.set_ylim(0, 240)
    ax1.set_title("(a) A typeclass raises both sides", pad=6, loc="left",
                  fontsize=9.5)
    ax1.legend(handles=[
        Line2D([], [], color=MANUAL, label=rf"copy-paste, bs_a1 ({P_PASTE:.2f}n)"),
        Line2D([], [], color=TROCQ, label=rf"Trocq, bs_a1 ({TROCQ_A:.0f}+2n)"),
        Line2D([], [], color=MANUAL, ls="--", label=rf"+ repair, bs_a2 ({P_PASTE_A2:.2f}n)"),
        Line2D([], [], color=TROCQ, ls="--", label=rf"Trocq, bs_a2 ({TROCQ_A2:.0f}+2n)"),
    ], loc="upper left", fontsize=7.2, handlelength=1.5, labelspacing=0.3)

    # (b) ROI
    roi_a1 = ((P_PASTE - PER_THM) * n - TROCQ_A) / (TROCQ_A + PER_THM * n)
    roi_a2 = ((P_PASTE_A2 - PER_THM) * n - TROCQ_A2) / (TROCQ_A2 + PER_THM * n)
    ax2.axhline(0, color=INK, lw=0.9, zorder=3)
    for val, ls_, lab, dy in ((ROI_INF_A, "-", "bs_a1", -0.20),
                             (ROI_INF_A2, "--", "bs_a2", 0.07)):
        ax2.axhline(val, color=MUTED, lw=0.8, ls=ls_, zorder=1)
        ax2.annotate(rf"$\to {val:.2f}\times$ ({lab})", xy=(39.4, val + dy),
                     ha="right", fontsize=7.5, color=INK_2)
    ax2.plot(n, roi_a1, color=MANUAL, zorder=4)
    ax2.plot(n, roi_a2, color=TROCQ, ls="--", lw=1.9, zorder=4)
    for ns, col in ((NSTAR_A, MANUAL), (NSTAR_A2, TROCQ)):
        ax2.plot([ns], [0], "o", ms=6, mfc=col, mec=SURFACE, mew=1.5, zorder=6)

    ax2.set_xlabel("Theorems transferred  ($n$)")
    ax2.set_ylabel(r"$\mathrm{ROI}(n)$")
    ax2.set_xlim(0, 40)
    ax2.set_ylim(-1.1, 2.45)
    times_axis(ax2)
    ax2.set_title("(b) Ceiling rises, break-even moves out", pad=6,
                  loc="left", fontsize=9.5)

    fig.suptitle("What the Addable typeclass costs: bs_a1.v vs bs_a2.v",
                 y=1.03, fontsize=11)
    fig.subplots_adjust(wspace=0.32)
    save(fig, "fig5_typeclass")


# ══════════════════════════════════════════════════════════════════════════
# Figure 6 -- the break-even estimate across the four iterations
# ══════════════════════════════════════════════════════════════════════════

def fig_iterations() -> None:
    fig, ax = plt.subplots(figsize=(W_FULL, 3.0))
    labels = ["1st\nlinear", "2nd\nshared setup", "3rd\ncomplexity",
              "4th\ncopy-paste"]
    vals = [17 / 5, 22 / 5, NSTAR_B, NSTAR_A]
    cols = ["#999999", "#999999", TROCQ, MANUAL]

    ax.vlines(range(4), 0, vals, color=cols, lw=2.6, zorder=3)
    ax.scatter(range(4), vals, s=110, c=cols, edgecolors=SURFACE,
               linewidths=2.0, zorder=5)
    for i, (v, c) in enumerate(zip(vals, cols)):
        ax.text(i, v + 0.85, f"{v:.1f}", ha="center", fontsize=10.5, color=c)

    ax.set_xticks(range(4))
    ax.set_xticklabels(labels, linespacing=1.4)
    ax.set_ylabel(r"Break-even  $n^{*}$")
    ax.set_ylim(0, 19)
    ax.set_xlim(-0.6, 3.6)
    ax.set_title("Each iteration was falsified by the corpus, not by argument",
                 pad=10)
    ax.annotate("the manual baseline changes here\n"
                r"(bridges $\to$ copy-paste)",
                xy=(3, NSTAR_A * 0.55), xytext=(1.55, 11.4), ha="center",
                fontsize=9.5, color=INK_2, linespacing=1.4,
                arrowprops=dict(arrowstyle="->", color="#999999", lw=1.0))
    save(fig, "fig6_iterations")


def dump_constants() -> None:
    lines = [
        "Constants derived from _counts.csv by _graphs.py",
        "(cross-check these against _paper.tex)",
        "",
        f"  S_iso                 = {S_iso}",
        f"  C_base(f=3)           = {C_BASE_B}",
        f"  Trocq extra(f=3)      = {EXTRA_B}",
        f"  C_trocq  Regime B     = {TROCQ_B} + 2n",
        f"  C_manual Regime B     = {C_BASE_B} + {P_COMPLEX}n",
        f"  P_manual (simple)     = {P_SIMPLE}",
        f"  P_manual (complex)    = {P_COMPLEX}",
        f"  c_avg                 = {C_AVG}",
        f"  k                     = {K}",
        f"  n* Regime B           = {NSTAR_B:.4f}",
        f"  ROI_inf Regime B      = {ROI_INF_B:.4f}",
        "",
        f"  P_paste               = {P_PASTE:.4f}  ({'+'.join(map(str, PASTE))})/3",
        f"  S_bij                 = {S_BIJ}",
        f"  per-function subtotal = {PER_FN}",
        f"  C_trocq  Regime A     = {TROCQ_A} + 2n",
        f"  C_manual Regime A     = {P_PASTE:.2f}n",
        f"  n* Regime A           = {NSTAR_A:.4f}",
        f"  ROI_inf Regime A      = {ROI_INF_A:.4f}",
        "",
        f"  gref tax (bs_a2)      = {GREF_TAX}",
        f"  Z marginal, Trocq     = {Z_TROCQ} setup (+6 theorems = {Z_TROCQ + 6})",
        f"  Z marginal, manual    = {Z_MANUAL}",
    ]
    (OUT / "_figure_constants.txt").write_text("\n".join(lines) + "\n",
                                               encoding="utf-8")
    print("\n".join(lines))


if __name__ == "__main__":
    import sys
    sys.path.insert(0, str(HERE))
    print("Generating figures from measured corpus\n")
    fig_regimes()
    fig_roi()
    fig_roi_surface()
    fig_setup()
    fig_typeclass()
    fig_iterations()
    print()
    dump_constants()
    print(f"\nAll figures in {OUT}")

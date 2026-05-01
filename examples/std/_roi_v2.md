# ROI Analysis: Trocq vs Copy-Paste Proof Transfer

## Experiment: `bs_a1.v`

`bs_a1.v` is a self-contained Rocq experiment measuring the **Return on Investment**
of using the Trocq proof-transfer plugin against the most realistic manual
alternative: **copy-pasting proofs**.

Three phases in a single file:

| Phase | Description | Role |
|-------|-------------|------|
| 1 | `NatList` definitions + base theorems | Source of truth |
| 2 | `PList nat` proofs by pure copy-paste | Manual baseline |
| 3 | Trocq proof transfer | Plugin approach |

**Counting convention:** one period-terminated tactic = 1 step;
`Trocq Use` commands = 1 step each; bullet markers = 0 steps.

---

## 1. Variables

| Symbol | Meaning | Value in `bs_a1.v` |
|--------|---------|-------------------|
| $n$ | Number of theorems to transfer | 3 (measured) |
| $f$ | Number of distinct functions in the theory | 3 (`length`, `app`, `rev`) |
| $P_{\text{paste}}$ | Avg. tactic steps per copy-paste theorem | $17/3 \approx 5.67$ |
| $S_{\text{bij}}$ | One-time cost: iso proofs + type relation + shared registrations | 13 |
| $S_{\text{bridge}}$ | Bridge-lemma tactic cost per function | 5–6 |
| $W_{\text{trocq}}$ | Trocq overhead per function: `R__f` wrapper + `Trocq Use` | 6–8 |

---

## 2. Concrete Counts from `bs_a1.v`

### Phase 1 — NatList Base Theorems (source of truth)

| Lemma / Theorem | Tactic steps |
|---|---|
| `napp_nil_r` (auxiliary) | 4 |
| `nlength_napp` | 5 |
| `napp_assoc` | 5 |
| `nrev_napp` | 7 |
| **Total** | **21** |

### Phase 2 — Copy-Paste Manual (fixed setup = 0)

| Lemma / Theorem | Tactic steps |
|---|---|
| `papp_nil_r` (auxiliary) | 4 |
| `plength_papp_manual` | 5 |
| `papp_assoc_manual` | 5 |
| `prev_papp_manual` | 7 |
| **Fixed setup cost** | **0** |

The monomorphic design of `plength`, `papp`, `prev` (typed `PList nat -> ...`
rather than `forall {A}, PList A -> ...`) ensures every copied proof body is
**tactic-identical** to its NatList source — no extra `intros A`, no structural
rewrites. Copy, rename the type and constructor names, compile.

$$P_{\text{paste}} = \frac{5 + 5 + 7}{3} = \frac{17}{3} \approx 5.67 \text{ steps/theorem}$$

### Phase 3 — Trocq Infrastructure (full bureaucracy)

| Item | Tactic steps |
|---|---|
| `plist_nlist_iso` | 4 |
| `nlist_plist_iso` | 4 |
| `R_NatList` via `Iso.toParam` | 5 |
| Shared `Trocq Use` ×3 | 3 |
| **$S_{\text{bij}}$ subtotal** | **13** |
| `_plength`: bridge(5) + `R__`(5) + `Use`(1) | 11 |
| `_papp`: bridge(6) + `R__`(7) + `Use`(1) | 14 |
| `_prev`: bridge(6) + `R__`(5) + `Use`(1) | 12 |
| **Per-function subtotal** ($f = 3$) | **37** |
| **$S_{\text{setup}}$ total** | **50** |
| Per theorem ×3 (`trocq.` + `apply`) | 6 |

---

## 3. Cost Formulas

$$C_{\text{manual}}(n) = n \cdot P_{\text{paste}} = \frac{17}{3} \cdot n \approx 5.67 \cdot n$$

$$C_{\text{trocq}}(n) = \underbrace{S_{\text{bij}} + f \cdot (S_{\text{bridge}} + W_{\text{trocq}})}_{S_{\text{setup}} = 50} + n \cdot 2 = 50 + 2n$$

where $f = 3$, $S_{\text{bij}} = 13$, and $f \cdot (S_{\text{bridge}} + W_{\text{trocq}}) = 37$.

---

## 4. Break-Even Point

$$C_{\text{manual}}(n^*) = C_{\text{trocq}}(n^*)
\implies \frac{17}{3}\,n^* = 50 + 2n^*
\implies \frac{11}{3}\,n^* = 50
\implies n^* = \frac{150}{11} \approx 13.6$$

**Trocq becomes cheaper only from $n \geq 14$ theorems.**

---

## 5. ROI Formula

$$\text{ROI}(n) = \frac{C_{\text{manual}}(n) - C_{\text{trocq}}(n)}{C_{\text{trocq}}(n)} = \frac{\dfrac{11}{3}\,n - 50}{50 + 2n}$$

**Long-run ROI** ($n \to \infty$):

$$\text{ROI}_{\infty} = \frac{P_{\text{paste}} - 2}{2} = \frac{17/3 - 2}{2} = \frac{11}{6} \approx 1.83\times$$

At scale, manual proof costs 2.83× as much as Trocq per theorem — a bounded
asymptote, not exponential growth.

---

## 6. When Does Trocq Pay Off?

| Scenario | Winner | Key factor |
|---|---|---|
| Few theorems ($n < 14$), types similar | **Manual** | Copy-paste is free; 50-step setup not amortised |
| Many theorems ($n \geq 14$) | **Trocq** | Setup amortised; per-theorem cost only 2 steps |
| Types diverge structurally | **Trocq** | Copied proof scripts break; Trocq unaffected |
| Large vocabulary ($f \gg 3$), few theorems | **Manual** | $f \cdot W_{\text{trocq}}$ grows with no theorems to offset it |
| Massive library ($n \to \infty$) | **Trocq** | ROI $\to 1.83\times$ |

**Three tipping factors:**

1. **Volume** ($n \geq 14$): the 50-step setup is only amortised across a large theorem library.
2. **Structural divergence**: if `PList` and `NatList` had different induction schemes or
   constructor arities, copied proofs would fail and manual cost would spike; Trocq's
   per-theorem cost stays at 2.
3. **Vocabulary stability**: once `R__` wrappers are registered for all $f$ functions,
   every future theorem costs exactly 2 steps regardless of syntactic complexity.

> **Key lesson:** Trocq's true competition is the pragmatic developer who copies
> a working proof and presses F5. That developer wins for small libraries ($n < 14$).
> Trocq wins for large ones.

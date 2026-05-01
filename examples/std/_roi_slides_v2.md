---
marp: true
theme: default
math: katex
paginate: true
style: |
  section {
    font-size: 16px;
    font-family: "Georgia", serif;
  }
  h1 { color: #1a3a5c; }
  h2 { color: #1a3a5c; border-bottom: 2px solid #1f77b4; padding-bottom: 4px; }
  section.title {
    text-align: center;
    justify-content: center;
  }
  section.chapter {
    background: #1a3a5c;
    color: white;
    text-align: center;
    justify-content: center;
  }
  section.chapter h1 { color: white; font-size: 2em; }
  section.chapter p  { color: #cce0ff; font-size: 1.1em; }
  .cols {
    display: grid;
    grid-template-columns: 1fr 1fr;
    gap: 1.2rem;
    align-items: start;
  }
  .cols > * { min-width: 0; }
  table {
    font-size: 0.88em;
    display: block;
    margin: 20px auto;
  }
  img {
    display: block;
    margin: 30px auto;
  }
  code  { font-size: 0.82em; }
  pre   { font-size: 0.78em; }
---

<!-- _class: title -->
<!-- _paginate: false -->

# ROI Analysis: Proof Transfer with Trocq

### When does automation beat copy-paste?

---

## The Experiment: `bs_a1.v`

We measure the **Return on Investment** of using Trocq to transfer theorems
between `NatList` and `PList nat`.

**Three phases in a single file:**

| Phase | Description | Role |
|-------|-------------|------|
| 1 | `NatList` definitions + base theorems | Source of truth |
| 2 | `PList nat` proofs by pure copy-paste | Manual baseline |
| 3 | Trocq proof transfer | Plugin approach |

**What we measure:** *proof obligations* — tactic steps required.

**Counting convention:**
- One period-terminated tactic = **1 step**
- `Trocq Use` commands = **1 step each**
- Bullet markers (`-`) = **0 steps**

> **Goal:** find the break-even point and understand *when* Trocq pays off.

---

<!-- _class: chapter -->
<!-- _paginate: false -->

# The Copy-Paste Baseline

*Phase 1 → Phase 2: rename and compile.*

---

## Phase 1 → Phase 2: Tactic-Identical Proofs

<div class="cols">

**Phase 1 — NatList (source)**
```coq
(* 5 tactic steps *)
Theorem nlength_napp :
  forall (l1 l2 : NatList),
  nlength (napp l1 l2) =
  nlength l1 + nlength l2.
Proof.
  intros l1 l2.
  induction l1 as [|h t IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Defined.
```

**Phase 2 — PList nat (copy-paste)**
```coq
(* 5 tactic steps — identical body *)
Theorem plength_papp_manual :
  forall (l1 l2 : PList nat),
  plength (papp l1 l2) =
  plength l1 + plength l2.
Proof.
  intros l1 l2.
  induction l1 as [|h t IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Defined.
```

</div>

**Key design choice:** `plength`, `papp`, `prev` are typed `PList nat -> ...`
(monomorphic), not `forall {A}, PList A -> ...`.
This makes every copied proof body **tactic-identical** — no `intros A`, no extra rewrites.

**Setup cost: 0.** Every new theorem is just a renamed copy.

---

## Phase 2 — Copy-Paste Costs

| Lemma / Theorem | Tactic steps |
|---|---|
| `papp_nil_r` (auxiliary) | 4 |
| `plength_papp_manual` | 5 |
| `papp_assoc_manual` | 5 |
| `prev_papp_manual` | 7 |
| **Fixed setup cost** | **0** |

$$P_{\text{paste}} = \frac{5 + 5 + 7}{3} = \frac{17}{3} \approx 5.67 \text{ steps/theorem}$$

$$C_{\text{manual}}(n) = n \cdot P_{\text{paste}} = \frac{17}{3}\,n \approx 5.67\,n \qquad \textbf{(no intercept)}$$

The manual cost line **starts at the origin** — no investment is needed before the first theorem.

---

<!-- _class: chapter -->
<!-- _paginate: false -->

# The Trocq Approach

*Phase 3: the full relational infrastructure.*

---

## Phase 3 — Infrastructure Breakdown

Before any theorem can be transferred, Trocq requires:

| Item | Tactic steps |
|---|---|
| `plist_nlist_iso` (forward iso) | 4 |
| `nlist_plist_iso` (backward iso) | 4 |
| `R_NatList` via `Iso.toParam` | 5 |
| Shared `Trocq Use` ×3 | 3 |
| **$S_{\text{bij}}$ subtotal** | **13** |
| `_plength`: bridge(5) + `R__`(5) + `Use`(1) | 11 |
| `_papp`: bridge(6) + `R__`(7) + `Use`(1) | 14 |
| `_prev`: bridge(6) + `R__`(5) + `Use`(1) | 12 |
| **Per-function subtotal** ($f = 3$) | **37** |
| **$S_{\text{setup}}$ total** | **50** |

This is a **one-time fixed cost** of 50 steps — paid before the first theorem.

---

## Phase 3 — Per-Theorem Cost

After the 50-step setup, each theorem costs exactly **2 tactic steps**:

```coq
Theorem _plength_papp : forall (l1 l2 : _PList),
    _plength (_papp l1 l2) = _plength l1 + _plength l2.
Proof. trocq. apply nlength_napp. Qed.   (* 2 steps *)

Theorem _papp_assoc : forall (l1 l2 l3 : _PList),
    _papp (_papp l1 l2) l3 = _papp l1 (_papp l2 l3).
Proof. trocq. apply napp_assoc. Qed.     (* 2 steps *)

Theorem _prev_papp : forall (l1 l2 : _PList),
    _prev (_papp l1 l2) = _papp (_prev l2) (_prev l1).
Proof. trocq. apply nrev_napp. Qed.      (* 2 steps *)
```

**Complexity-blind:** `_prev_papp` has 5 function applications in its statement,
yet costs the same 2 steps as `_plength_papp` which has 3.

$$C_{\text{trocq}}(n) = \underbrace{50}_{S_{\text{setup}}} + 2n$$

---

## Cost Formulas & Break-Even

$$C_{\text{manual}}(n) = \frac{17}{3}\,n \approx 5.67\,n \qquad C_{\text{trocq}}(n) = 50 + 2n$$

**Break-even** — set $C_{\text{manual}} = C_{\text{trocq}}$:

$$\frac{17}{3}\,n^* = 50 + 2n^*
\implies \frac{11}{3}\,n^* = 50
\implies n^* = \frac{150}{11} \approx 13.6$$

**From $n = 14$ onwards, Trocq is strictly cheaper.**

| $n$ | $C_{\text{manual}}$ | $C_{\text{trocq}}$ | Winner |
|-----|----|----|--------|
| 5  | 28  | 60  | Manual |
| 10 | 57  | 70  | Manual |
| 14 | 79  | 78  | **Trocq** |
| 20 | 113 | 90  | **Trocq** |
| 30 | 170 | 110 | **Trocq** |

---

## Cost Graph

![width:720px](_graphs_v2/graph_01_cost.png)

The manual line starts at the **origin** (no setup). Trocq's intercept is **50**.
Break-even is at $n^* \approx 13.6$.

---

## ROI Formula & Long-Run

$$\text{ROI}(n) = \frac{C_{\text{manual}}(n) - C_{\text{trocq}}(n)}{C_{\text{trocq}}(n)} = \frac{\dfrac{11}{3}\,n - 50}{50 + 2n}$$

| Region | Interpretation |
|--------|----------------|
| ROI $< 0$ for $n < 13.6$ | Manual is cheaper — copy-paste not yet outpaced |
| ROI $= 0$ at $n \approx 14$ | Break-even point |
| ROI $\to 1.83\times$ as $n \to \infty$ | Trocq saves 1.83× its own cost |

**Long-run ROI** ($n \to \infty$):

$$\text{ROI}_{\infty} = \frac{P_{\text{paste}} - 2}{2} = \frac{17/3 - 2}{2} = \frac{11}{6} \approx 1.83\times$$

*$P_{\text{paste}}$ = avg. copy-paste tactic steps per theorem; $2$ = Trocq per-theorem cost.*

At scale, manual proof costs **2.83× as much** as Trocq per theorem —
a **bounded asymptote**, not exponential growth.

---

## ROI Curve

![width:720px](_graphs_v2/graph_02_roi.png)

The curve starts at $-1$ ($n = 0$: Trocq costs 50, manual costs 0),
crosses zero at $n \approx 13.6$, then asymptotes to $1.83\times$.

---

## When Does Trocq Pay Off?

| Scenario | Winner | Key factor |
|---|---|---|
| Few theorems ($n < 14$), types similar | **Manual** | Copy-paste is free; 50-step setup not amortised |
| Many theorems ($n \geq 14$) | **Trocq** | Setup amortised; per-theorem cost only 2 steps |
| Types diverge structurally | **Trocq** | Copied scripts break; Trocq unaffected |
| Large vocabulary ($f \gg 3$), few theorems | **Manual** | $f \cdot W_{\text{trocq}}$ grows with no theorems to offset it |
| Massive library ($n \to \infty$) | **Trocq** | ROI $\to 1.83\times$ |

**Three tipping factors:**

1. **Volume** ($n \geq 14$): the 50-step setup only pays off across a large theorem library.
2. **Structural divergence**: if the two types have different induction schemes, copied proofs
   break and manual cost spikes; Trocq's 2-step per-theorem cost is unaffected.
3. **Vocabulary stability**: once `R__` wrappers are registered for $f$ functions, every future
   theorem costs exactly 2 steps regardless of syntactic complexity.

> Trocq's true competition is the pragmatic developer who copies a working proof
> and presses **F5**. That developer wins for $n < 14$. Trocq wins for large libraries.

---

<!-- _class: chapter -->
<!-- _paginate: false -->

# Experiment 2: `bs_a2.v`

*Fixing the cheat — true polymorphism via Typeclasses*

---

## The Design Flaw in `bs_a1.v`

`bs_a1.v` made a quiet design choice that enabled the clean copy-paste:

```coq
(* bs_a1.v — the cheat: operations typed at PList nat *)
Fixpoint plength (l : PList nat) : nat := ...
Fixpoint papp (l1 l2 : PList nat) : PList nat := ...
Fixpoint prev (l : PList nat) : PList nat := ...
```

The professor's question exposed it:

> *"Since `PList` is polymorphic, how do you sum its elements? Who is the addition operator?"*

**`bs_a2.v` fixes both problems:**

```coq
(* bs_a2.v — truly polymorphic structural operations *)
Fixpoint plength {A : Type} (l : PList A) : nat := ...
Fixpoint papp    {A : Type} (l1 l2 : PList A) : PList A := ...
Fixpoint prev    {A : Type} (l : PList A) : PList A := ...

(* Typeclass: who provides addition? *)
Class Addable (A : Type) := {
  add        : A -> A -> A;
  zero       : A;
  add_assoc  : forall x y z, add (add x y) z = add x (add y z);
  add_zero_l : forall x, add zero x = x;
  add_zero_r : forall x, add x zero = x
}.

Fixpoint psum {A} {H : Addable A} (l : PList A) : A :=
  match l with PNil => zero | PCons h t => add h (psum t) end.
```

---

## Phase 3 — Where Copy-Paste Breaks

Structural theorems (`plength`, `papp`, `prev`) still copy-paste perfectly — they traverse the spine only, not the values.

**`psum_papp_manual` breaks in two places:**

<div class="cols">

**`nsum_napp` — NatList (works)**
```coq
(* 5 steps *)
Proof.
  intros l1 l2.
  induction l1 as [|h t IH]; simpl.
  - reflexivity.       (* 0+x=x is definitional *)
  - rewrite IH. lia.   (* lia handles ℕ arithmetic *)
Defined.
```

**`psum_papp_manual` — PList A (diverges)**
```coq
(* 8 steps — 2 divergences *)
Proof.
  intros A H l1 l2.
  induction l1 as [|h t IH]; simpl.
  - symmetry. apply add_zero_l.
    (* ← DIVERGENCE 1: add_zero_l is an axiom *)
  - rewrite IH. symmetry. apply add_assoc.
    (* ← DIVERGENCE 2: lia fails on abstract A *)
Defined.
```

</div>

| Step | NatList | PList A | Root cause |
|---|---|---|---|
| Base case | `reflexivity` | `symmetry. apply add_zero_l` | `add zero x = x` is an axiom, not definitional |
| Inductive | `rewrite IH. lia` | `rewrite IH. symmetry. apply add_assoc` | `lia` is ℕ/ℤ only |

**Setup cost: 0.** But the per-theorem cost for `psum` theorems is now **8** instead of 7.

$$P_{\text{paste}}^{a2} = \frac{5 + 5 + 7 + 8}{4} = 6.25 \text{ steps/theorem}$$

---

## Phase 4+5 — Trocq Handles the Typeclass Gap

The new `inst_addable_nat` instance bridges the abstract `add` to `Nat.add`:

```coq
#[global] Instance inst_addable_nat : Addable nat := {
  add       := Nat.add;    zero      := 0;
  add_assoc := ltac:(intros; lia);
  add_zero_l := ltac:(intros; lia);  add_zero_r := ltac:(intros; lia)
}.
```

Because `inst_addable_nat` makes `@add nat inst_addable_nat` **definitionally equal** to `Nat.add`, the existing `Param_add` registration applies directly. The `R__psum` wrapper needs only **5 steps** — same as the structural wrappers:

```coq
Lemma R__psum (l : _PList) (l' : NatList) (lR : rel R_NatList l l') :
    natR (_psum l) (nsum l').
Proof.
  change (plist_2_nlist l = l') in lR.
  apply map_in_R_nat.
  rewrite plist_2_nlist_sum.   (* new bridge lemma *)
  rewrite lR. reflexivity.
Defined.

Theorem _psum_papp : forall (l1 l2 : _PList),
    _psum (_papp l1 l2) = _psum l1 + _psum l2.
Proof. trocq. apply nsum_napp. Qed.   (* 2 steps *)
```

| Item | bs\_a1.v | bs\_a2.v |
|---|---|---|
| $S_{\text{bij}}$ | 13 | 13 (same) |
| Bridge lemmas | 17 | 23 (+`_psum`: 6) |
| R__ wrappers + Use | 20 | 26 (+`R__psum`: 6) |
| **$S_{\text{setup}}$** | **50** | **62** |

---

## Cost Formulas & Break-Even (bs\_a2.v)

$$C_{\text{manual}}^{a2}(n) = 6.25\,n \qquad C_{\text{trocq}}^{a2}(n) = 62 + 2n$$

$$6.25\,n^* = 62 + 2n^* \implies 4.25\,n^* = 62 \implies n^* = \frac{62}{4.25} \approx 14.6$$

**From $n = 15$ onwards, Trocq is strictly cheaper** (up from 14 in `bs_a1.v`).

| $n$ | $C_M^{a1}$ | $C_T^{a1}$ | $C_M^{a2}$ | $C_T^{a2}$ |
|-----|------|------|------|------|
| 5   | 28   | 60   | 31   | 72   |
| 10  | 57   | 70   | 63   | 82   |
| 15  | 85   | 80✓  | 94   | 92✓  |
| 20  | 113  | 90   | 125  | 102  |
| 30  | 170  | 110  | 188  | 122  |

---

## Cost Comparison Graph

![width:720px](_graphs_v2/graph_03_cost_comparison.png)

**Solid lines** = `bs_a1.v` (monomorphic PList nat).
**Dashed lines** = `bs_a2.v` (truly polymorphic + Typeclass).
Both Trocq lines are parallel (slope = 2); manual lines diverge slightly due to higher $P_M^{a2}$.

---

## ROI Comparison Graph

![width:720px](_graphs_v2/graph_04_roi_comparison.png)

| Metric | `bs_a1.v` | `bs_a2.v` | Δ |
|---|---|---|---|
| $P_{\text{paste}}$ | $\approx 5.67$ | $6.25$ | +0.58 |
| $S_{\text{setup}}$ | $50$ | $62$ | +12 |
| $n^*$ | $\approx 13.6$ | $\approx 14.6$ | +1 |
| $\text{ROI}_\infty$ | $\approx 1.83\times$ | $\approx 2.125\times$ | **+0.3×** |

The Typeclass divergence adds 1 theorem to the break-even, but raises the long-run ceiling by 0.3×.

---

## Takeaway: What `bs_a2.v` Teaches

**The Typeclass divergence cost is modest and mostly absorbed by setup:**

- `psum_papp_manual` cost 8 steps instead of 7 (+1 step, +2 explicit axiom rewrites)
- Trocq handled the same divergence in its existing 5-step `R__psum` wrapper — no extra complexity
- The break-even shifted from $n \approx 14$ to $n \approx 15$ — a rounding of 1

**The key asymmetry:**

| | Manual (copy-paste) | Trocq |
|---|---|---|
| Typeclass axiom mismatch | Divergence visible in every proof body | Absorbed once into `R__psum` + `inst_addable_nat` |
| Each new `psum`-style theorem | 8 steps (forever) | 2 steps (forever) |
| As vocabulary grows ($f \uparrow$) | $P_M$ stays constant | $S_{\text{setup}}$ grows, $n^*$ rises |

> **Refined lesson:** Trocq does not eliminate the cost of Typeclass abstractions —
> it **relocates** that cost to the one-time setup, away from each individual theorem.
> For large libraries, this relocation is the dominant economic advantage.

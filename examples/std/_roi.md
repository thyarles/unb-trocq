# ROI - First try

## 1. Formalizing the Variables

### Independent Variables

| Symbol | Variable | Operationalization |
|--------|----------|--------------------|
| $n$ | Number of theorems to transfer | Count of `Theorem` statements |
| $c$ | Complexity of each theorem | Number of distinct functions/constructors appearing |
| $d$ | Type distance | Param class needed: 44 (iso) = 1, 42/24 = 2, lower = 3+ |

### Cost Metrics

| Symbol | Metric | What it measures |
|--------|--------|-----------------|
| $O$ | Proof obligations | Lemmas + `Defined` blocks required |
| $L$ | Learning overhead | Fixed cost to understand framework internals |
| $R$ | Registration cost | Number of `Trocq Use` + relational witnesses |

---

## 2. The Cost Formulas

**Manual approach** (no framework):
$$C_{\text{manual}}(n, c) = 7cn$$

Each theorem requires $\approx 7c$ obligations (bridge lemmas, inductions, rewrites), all repeated for every theorem.

**Trocq approach:**
$$C_{\text{trocq}}(n, c, d) = \underbrace{(12d + 5)}_{\text{one-time setup}} + \underbrace{2cn}_{\text{per theorem}}$$

- $12d$: relational witnesses scale with type distance $d$
- $5$: registrations (`Trocq Use` calls)
- $2cn$: each theorem costs ~2 steps after setup (`trocq.` + `apply`)

---

## 3. Break-Even and ROI

Setting $C_{\text{manual}} = C_{\text{trocq}}$ with $c = 1, d = 1$:

$$7n = 17 + 2n \implies n^* = \frac{17}{5} \approx 3.4 \text{ theorems}$$

The **ROI formula** (savings relative to Trocq's cost):

$$\text{ROI}(n) = \frac{C_{\text{manual}}(n) - C_{\text{trocq}}(n)}{C_{\text{trocq}}(n)} = \frac{5n - 17}{17 + 2n}$$

- $\text{ROI} < 0$ for $n < 3.4$: manual is cheaper
- $\text{ROI} = 0$ at $n \approx 4$: break-even
- $\text{ROI} \to 2.5$ as $n \to \infty$: Trocq saves ~2.5× the cost of using it

---

## 4. Recommended Visual Representation

A **cost vs. $n$ line chart** is the clearest artifact:

- X-axis: number of theorems $n$
- Y-axis: total proof obligations
- Two lines: $7n$ (manual) and $17 + 2n$ (Trocq)
- Mark the intersection at $n \approx 4$ as the break-even point

A second chart can show the **ROI curve** $\frac{5n-17}{17+2n}$ crossing zero at $n \approx 4$ and asymptoting upward — this directly answers "in which scenarios is Trocq more efficient?"

---

## 5. Qualitative Factors the Formula Doesn't Capture

You can note:

- **Learning curve** is a fixed cost absorbed into setup ($L \subset C_{\text{trocq, setup}}$) — it does not scale with $n$, which is Trocq's key advantage
- **Type distance $d$** directly affects whether the break-even shifts: for $d = 2$ (weaker Param class), the setup rises to $\approx 29$ obligations, pushing $n^*$ to $\approx 5.8$
- For **structurally distant types** (e.g., binary vs. unary nat), the manual approach may actually be competitive up to 6–8 theorems


# ROI - Second try

The analysis provided in the `ROI_01` file contains a fundamental mathematical flaw regarding how the formalization costs scale, which becomes immediately apparent when cross-referencing it with your Rocq code in `bs_p4.v` (the manual approach) and `bs_p5.v` (the Trocq approach). 

Here is a detailed evaluation of your current analysis, followed by specific suggestions and formulas to accurately answer the prompt regarding Variables, Cost Metrics, and ROI.

## 1. Critique of the `ROI_01` Analysis Based on the Code
The formula proposed in `ROI_01` for the manual approach is $C_{\text{manual}}(n, c) = 7cn$, implying that **all** manual proof obligations scale linearly with every new theorem. However, looking at `bs_p4.v`, this is factually incorrect. 

In the manual approach, you define the conversion functions (`plist_to_natlist`, `natlist_to_plist`) and prove their mutual isomorphisms (`plist_natlist_iso`, `natlist_plist_iso`) only **once per type**. Furthermore, the compatibility bridge lemmas (like `plength_eq_nlength` and `plist_to_natlist_app`) are proven only **once per function**. If you add a second or third theorem to transfer, you **do not** rewrite these 6 base lemmas. You only write the manual rewrite script for the new theorem. Therefore, the manual cost is largely a *fixed setup cost* plus a variable cost that scales with $n$, not a purely multiplicative $7cn$.

Secondly, `ROI_01` assumes Trocq bypasses these manual obligations. But looking at `bs_p5.v`, **Trocq actually requires the exact same manual bridge lemmas** (`_plength_eq_nlength`, `plist_2_nlist_app`) to function. On top of those, Trocq requires you to write `Param` wrapper lemmas (`R__plength`, `R__papp`) and register them with `Trocq Use`. 

**Conclusion from the code:** Trocq's *initial setup cost* is actually **higher** than the manual setup cost. Trocq's true ROI comes entirely from the *per-theorem* scaling. While a manual theorem requires a bespoke, step-by-step rewrite script for every new goal, Trocq solves any new theorem instantly in two steps (`trocq. apply ...`).

---

## 2. Suggestions for Variables, Cost Metrics, and ROI Formulas

To provide an analytical and visually representable answer to the prompt, you should structure your variables and formulas to reflect the fixed vs. variable costs accurately.

### Identification of Independent Variables (Causes)
*   **$n$ (Quantity of theorems):** The number of theorems in the original theory that need to be transferred to the new type.
*   **$f$ (Size and complexity of the signature):** Instead of a generic complexity metric $c$, define $f$ as the number of distinct constants, constructors, and functions involved in the theory. Every new function increases the fixed setup cost because it requires a new bridge lemma and, for Trocq, a new relational wrapper. 
*   **$d$ (Type Distance):** The specific `Param` class required (e.g., Level `(4,4)` for an isomorphism, or Level `(4,2a)` for a retraction). If $d$ is a weaker relation (like a retraction mapping $\mathbb{Z}$ to $\mathbb{Z}/9\mathbb{Z}$), you only provide one conversion function, which slightly lowers the setup cost.

### Cost Metrics (Effects)
*   **Base Setup Cost (Shared):** The number of manual conversion functions, mutual inverse proofs, and bridge lemmas. 
*   **Trocq Bureaucracy Cost:** The difficulty of establishing relations. Trocq requires packing the isomorphisms into `Iso.toParam` and proving relations using `map_in_R_nat` and `eq_trans`, which are syntactically heavier and more complex than standard manual lemmas.
*   **Per-Theorem Cost:** The number of LTAC tactics required to prove the final goal. For manual, this scales heavily with the size of the theorem. For Trocq, this is capped at ~2 tactics (`trocq. apply...`).
*   **Learning Curve ($L$):** A heavy, one-time fixed cost for the user to understand the 36 levels of parametricity, univalent maps, and the constraints of the `Trocq Use` command.

### The Revised Analytical Formulas

To derive an accurate ROI, define the costs as linear functions of $f$ (functions) and $n$ (theorems):

1.  **Manual Cost Formula:**
    $$C_{\text{manual}}(n, f) = \underbrace{S_{\text{types}} + f \cdot S_{\text{bridge}}}_{\text{Fixed Setup}} + \underbrace{n \cdot P_{\text{manual}}}_{\text{Variable Cost}}$$
    *   $S_{\text{types}}$: Cost to prove conversions (e.g., 4 lemmas).
    *   $S_{\text{bridge}}$: Cost to prove 1 compatibility lemma per function.
    *   $P_{\text{manual}}$: Cost to manually rewrite a theorem (high, scales with theorem complexity).

2.  **Trocq Cost Formula:**
    $$C_{\text{trocq}}(n, f) = \underbrace{S_{\text{types}} + f \cdot S_{\text{bridge}}}_{\text{Base Setup}} + \underbrace{1 + f + \text{Registrations}}_{\text{Trocq Wrappers}} + \underbrace{n \cdot P_{\text{trocq}}}_{\text{Variable Cost}}$$
    *   Trocq duplicates the base setup.
    *   Trocq adds 1 type relation, $f$ function relations, and their registrations.
    *   $P_{\text{trocq}}$ is basically $0 \approx 2$ lines of code (`trocq. apply...`).

## 3. Recommended Graphical Representation (ROI)
To visually represent this for your analysis:

**Graph 1: Cost vs. Number of Theorems ($n$)**
*   **X-axis:** Number of theorems transferred ($n$).
*   **Y-axis:** Total proof obligations (lines of code or number of lemmas).
*   **The Lines:** 
    *   Plot the **Manual** line starting at a low Y-intercept (just the base setup) but with a **steep slope** (because every theorem requires a long manual rewrite script).
    *   Plot the **Trocq** line starting at a **higher Y-intercept** (due to the added burden of `Param` relations and `Trocq Use`), but with a **nearly flat slope** (because transferring a theorem costs almost nothing).
*   **The Break-Even Point:** The exact intersection of these two lines dictates when Trocq becomes profitable. 

**Graph 2: The ROI Curve**
Plot the ROI equation: $\text{ROI}(n) = \frac{C_{\text{manual}}(n) - C_{\text{trocq}}(n)}{C_{\text{trocq}}(n)}$
*   The curve will start in the negative (indicating Trocq is a waste of time for just 1 or 2 theorems because of the heavy setup).
*   It will cross the zero-axis at the break-even point.
*   It will asymptote upwards, proving that **Trocq's automation is exponentially more efficient in scenarios where a theory has a massive library of theorems ($n \to \infty$) but a relatively small number of base operations ($f$)**.
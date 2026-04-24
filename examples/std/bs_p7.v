From Stdlib Require Import ssreflect.
From Stdlib Require Import Lia.
Local Open Scope nat_scope.
From Trocq Require Import Trocq.
From Trocq Require Import Param_nat.

Set Universe Polymorphism.

Require Import Trocq_examples.bs_p1.
Require Import Trocq_examples.bs_p2.
Require Import Trocq_examples.bs_p5.

(*  ── New Definitions ───────────────────────────────────────────────────────────── *)

(*  Sum of all elements in a NatList. *)
Fixpoint nsum (l : NatList) : nat :=
    match l with
    | NNil      => O
    | NCons h t => h + nsum t
    end.

(*  Sum of all elements in a _PList (= PList nat).

    Type-safety note: the monomorphic alias  _PList := PList nat  already
    restricts the element type to nat at the definition site.  There is no
    need for an explicit runtime guard — Rocq's type system statically
    prevents passing a  PList string  (or any non-nat PList) to  psum. *)
Fixpoint psum (l : _PList) : nat :=
    match l with
    | @PNil _      => O
    | @PCons _ h t => h + psum t
    end.

(*  ── Base Proofs ───────────────────────────────────────────────────────────────── *)

(*  The sum distributes over list concatenation:
    nsum (l1 ++ l2) = nsum l1 + nsum l2.

    Step-case arithmetic:  h + (nsum t + nsum l2) = (h + nsum t) + nsum l2
    This is just associativity of addition, discharged by lia. *)
Theorem nsum_napp : forall (l1 l2 : NatList),
    nsum (napp l1 l2) = nsum l1 + nsum l2.
Proof.
    intros l1 l2.
    induction l1 as [| h t IH]; simpl.
    - reflexivity.
    - rewrite IH.
      lia.
Defined.

(*  ── Manual Transfer ───────────────────────────────────────────────────────────── *)

(*  Bridge lemma: psum commutes with the forward conversion.
    Converting a _PList to a NatList and then summing gives the same result
    as summing the _PList directly. *)
Lemma psum_eq_nsum : forall (l : _PList),
    psum l = nsum (plist_2_nlist l).
Proof.
    induction l as [| h t IH]; simpl.
    - reflexivity.
    - rewrite IH.
      reflexivity.
Defined.

(*  Manual proof of psum_papp WITHOUT Trocq.

    Proof obligations incurred (per-theorem cost):
      1. introduce variables
      2. bridge: lhs psum → nsum
      3. bridge: _papp → napp
      4. apply NatList theorem
      5. bridge back: nsum → psum
      6. bridge back: nsum → psum
      7. reflexivity
      ───────────────
      TOTAL: 7 tactic steps
 *)
Theorem psum_papp_manual : forall (l1 l2 : _PList),
    psum (_papp l1 l2) = psum l1 + psum l2.
Proof.
    intros l1 l2.
    rewrite psum_eq_nsum.
    rewrite plist_2_nlist_app.
    rewrite nsum_napp.
    rewrite <- psum_eq_nsum.
    rewrite <- psum_eq_nsum.
    reflexivity.
Defined.

(*  ── Manual Transfer | Concrete examples ────────────────────────────────────────── *)

(*  Normal case: two non-empty lists. psum [1;2] + psum [3;4] = 3 + 7 = 10 *)
Goal psum (_papp (1 :p: 2 :p: {{}}) (3 :p: 4 :p: {{}})) =
     psum (1 :p: 2 :p: {{}}) + psum (3 :p: 4 :p: {{}}).
     apply psum_papp_manual. Qed.

(*  Left-empty: psum [] + psum [1;2] = 0 + 3 = 3 *)
Goal psum (_papp _PNil (1 :p: 2 :p: {{}})) =
     psum _PNil + psum (1 :p: 2 :p: {{}}).
     apply psum_papp_manual. Qed.

(*  Right-empty: psum [1;2] + psum [] = 3 + 0 = 3 *)
Goal psum (_papp (1 :p: 2 :p: {{}}) _PNil) =
     psum (1 :p: 2 :p: {{}}) + psum _PNil.
     apply psum_papp_manual. Qed.

(*  ── Trocq Transfer | Relational witness for psum / nsum ───────────────────────── *)

(*  R__psum connects psum and nsum under the R_NatList relation:
    if l ~ l' (i.e. plist_2_nlist l = l') then psum l ~ nsum l'.

    Proof obligations incurred (setup cost):
      1. change ... in lR     — normalize the hypothesis type
      2. apply map_in_R_nat   — reduce to plain nat equality
      3. rewrite psum_eq_nsum — bridge: psum → nsum ∘ plist_2_nlist
      4. rewrite lR           — substitute the related pair
      5. reflexivity
      ──────────────────────
      TOTAL: 5 tactic steps 
*)
Lemma R__psum (l : _PList) (l' : NatList) (lR : rel R_NatList l l') :
    natR (psum l) (nsum l').
Proof.
    change (plist_2_nlist l = l') in lR.
    apply map_in_R_nat.
    rewrite psum_eq_nsum.
    rewrite lR.
    reflexivity.
Defined.

(*  ── Trocq Transfer | Register in Trocq's database ─────────────────────────────── *)

Trocq Use R__psum.

(*  ── Trocq Transfer | The theorem via Trocq ────────────────────────────────────── *)

(*  Per-theorem cost: 2 tactic steps. *)
Theorem psum_papp_trocq : forall (l1 l2 : _PList),
    psum (_papp l1 l2) = psum l1 + psum l2.
Proof.
    trocq.
    apply nsum_napp.
Qed.

Print Assumptions psum_papp_trocq.

(*  ── Trocq Transfer | Concrete examples ────────────────────────────────────────── *)

(*  The same three Goal witnesses, now closed by psum_papp_trocq instead.
    The proof term Rocq constructs is much larger (it embeds the full
    parametricity witness built by the trocq tactic), but the statement
    and the one-liner proof are identical from the user's perspective.  *)

Goal psum (_papp (1 :p: 2 :p: {{}}) (3 :p: 4 :p: {{}})) =
     psum (1 :p: 2 :p: {{}}) + psum (3 :p: 4 :p: {{}}).
     apply psum_papp_trocq. Qed.

Goal psum (_papp _PNil (1 :p: 2 :p: {{}})) =
     psum _PNil + psum (1 :p: 2 :p: {{}}).
     apply psum_papp_trocq. Qed.

Goal psum (_papp (1 :p: 2 :p: {{}}) _PNil) =
     psum (1 :p: 2 :p: {{}}) + psum _PNil.
     apply psum_papp_trocq. Qed.

(*  Check: inspect the types (statements) of both proof terms. *)
Check psum_papp_manual.
Check psum_papp_trocq.

(*  The two theorems have the same TYPE *)
Check (psum_papp_manual = psum_papp_trocq).

(*  ── ROI Analysis ──────────────────────────────────────────────────────────────── *)

(** ┌─────────────────────────────────────────────────────────────────────┐
    │  SHARED COST (paid once, independent of transfer method)            │
    ├────────────────────────────────┬────────────────────────────────────┤
    │  Lemma / Theorem               │  Proof steps                       │
    ├────────────────────────────────┼────────────────────────────────────┤
    │  nsum_napp                     │  5                                 │
    │  psum_eq_nsum                  │  4                                 │
    ├────────────────────────────────┼────────────────────────────────────┤
    │  SHARED SUBTOTAL               │  9                                 │
    └────────────────────────────────┴────────────────────────────────────┘

    ┌─────────────────────────────────────────────────────────────────────┐
    │  SETUP COST (paid once per new function, here: psum / nsum)         │
    ├────────────────────────────────┬──────────────────┬─────────────────┤
    │  Item                          │  Manual          │  Trocq          │
    ├────────────────────────────────┼──────────────────┼─────────────────┤
    │  Bridge lemma (psum_eq_nsum)   │  (shared, 3)     │  (shared, 3)    │
    │  Relational wrapper (R__psum)  │  —               │  5 tactics      │
    │  Trocq Use R__psum             │  —               │  1 command      │
    ├────────────────────────────────┼──────────────────┼─────────────────┤
    │  SETUP SUBTOTAL (extra)        │  0               │  6              │
    └────────────────────────────────┴──────────────────┴────────────────-┘

    ┌─────────────────────────────────────────────────────────────────────┐
    │  PER-THEOREM COST (for each additional theorem about psum / nsum)   │
    ├────────────────────────────────┬──────────────────┬─────────────────┤
    │  Approach                      │  Manual          │  Trocq          │
    ├────────────────────────────────┼──────────────────┼─────────────────┤
    │  psum_papp / psum_papp_trocq   │  7 tactics       │  2 tactics      │
    ├────────────────────────────────┼──────────────────┼─────────────────┤
    │  PER-THEOREM SUBTOTAL          │  7               │  2              │
    └────────────────────────────────┴──────────────────┴─────────────────┘

    ┌─────────────────────────────────────────────────────────────────────┐
    │  TOTAL COST after n theorems involving psum:                        │
    │                                                                     │
    │   C_manual(n)  = 9 (shared) + 0  (setup) + 7n  = 9 + 7n             │
    │   C_trocq(n)   = 9 (shared) + 6  (setup) + 2n  = 15 + 2n            │
    │                                                                     │
    │  Break-even:  9 + 7n = 15 + 2n  =>  5n = 6  =>  n ≈ 2 theorems      │
    │                                                                     │
    │  From n = 2 onwards, Trocq becomes cheaper.                         │
    │                                                                     │
    │  Observation: the sum function has a simpler manual rewrite chain   │
    │  (7 tactics) than reversal in bs_p6 (9 tactics), so the break-even  │
    │  point is slightly later (≈ 2 vs. ≈ 1 theorem). This confirms       │
    │  the general trend: the more complex the per-theorem manual proof,  │
    │  the earlier Trocq pays off.                                        │
    └─────────────────────────────────────────────────────────────────────┘

    Key takeaway:
    - Even for a simple function like sum, Trocq pays off after only 2
      theorems, demonstrating that its setup cost is modest.
    - The type-safety concern (can psum receive a non-nat list?) is resolved
      at the type level, not at runtime: _PList is a monomorphic alias for
      PList nat, so the Rocq type-checker statically rejects any attempt to
      pass a PList string to psum. *)

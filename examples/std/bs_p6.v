From Stdlib Require Import ssreflect.
Local Open Scope nat_scope.
From Trocq Require Import Trocq.
From Trocq Require Import Param_nat.

Set Universe Polymorphism.

Require Import Trocq_examples.bs_p1.
Require Import Trocq_examples.bs_p2.
Require Import Trocq_examples.bs_p5.

(*  ── New Definitions ───────────────────────────────────────────────────── *)

(*  Reversal for NatList — accumulates into a new list by cons-ing the
    current head onto the reversed tail, then appending the singleton.       *)
Fixpoint nrev (l : NatList) : NatList :=
    match l with
    | NNil      => NNil
    | NCons h t => napp (nrev t) (NCons h NNil)
    end.

(*  Reversal for _PList (monomorphic alias for @prev nat).
    Follows the same pattern as the other _P* aliases in bs_p5 to avoid
    Trocq confusing implicit sort arguments with list variables.             *)
Fixpoint _prev (l : _PList) : _PList :=
    match l with
    | @PNil _      => _PNil
    | @PCons _ h t => _papp (_prev t) (_PCons h _PNil)
    end.

(*  ── Base Proofs | Auxiliary lemmas ────────────────────────────────────── *)

(*  napp with an empty right argument is the identity.
    Needed as the base case for nrev_napp.                                   *)
Lemma napp_nil_r : forall l : NatList, napp l NNil = l.
Proof.
    induction l as [| h t IH]; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
Defined.

(*  _papp with an empty right argument is the identity.
    Needed as the base case for _prev_papp.                                  *)
Lemma _papp_nil_r : forall l : _PList, _papp l _PNil = l.
Proof.
    unfold _papp, _PNil.
    induction l as [| h t IH]; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
Defined.

(*  ── Base Proofs | Distribution of reversal over append (NatList) ──────── *)

(*  Reversing a concatenation yields the concatenation of the reversals
    in the opposite order: nrev (l1 ++ l2) = nrev l2 ++ nrev l1.             *)
Theorem nrev_napp : forall (l1 l2 : NatList),
    nrev (napp l1 l2) = napp (nrev l2) (nrev l1).
Proof.
    intros l1 l2.
    induction l1 as [| h t IH]; simpl.
    - (* Base: nrev l2 = napp (nrev l2) NNil *)
      symmetry. apply napp_nil_r.
    - (* Step: IH : nrev (napp t l2) = napp (nrev l2) (nrev t)
         Goal  : napp (nrev (napp t l2)) (NCons h NNil)
               = napp (nrev l2) (napp (nrev t) (NCons h NNil)) *)
      rewrite IH.
      rewrite napp_assoc.
      reflexivity.
Defined.

(*  ── Base Proofs | Distribution of reversal over append (_PList) ───────── *)

(*  Mirror of nrev_napp for the polymorphic list type.
    Proved independently by structural induction, using _papp_nil_r and
    _papp_assoc (the latter imported from bs_p5 via Trocq).                  *)
Theorem _prev_papp : forall (l1 l2 : _PList),
    _prev (_papp l1 l2) = _papp (_prev l2) (_prev l1).
Proof.
    intros l1 l2.
    induction l1 as [| h t IH]; simpl.
    - symmetry. apply _papp_nil_r.
    - rewrite IH.
      apply _papp_assoc.
Defined.

(*  ── Manual Transfer ───────────────────────────────────────────────────── *)

(*  This phase proves _prev (_papp l1 l2) = _papp (_prev l2) (_prev l1)
    by going THROUGH NatList: we build the bridge lemma that connects _prev
    to nrev, then chain it with plist_2_nlist_app and nrev_napp manually.

    Contrast with Phase 4, where Trocq does all of this automatically.       *)

(*  ── Manual Transfer | Bridge lemma for reversal ───────────────────────── *)

(*  The forward conversion function plist_2_nlist commutes with reversal:
    converting a reversed _PList is the same as reversing after converting.  *)
Lemma plist_2_nlist_rev : forall (l : _PList),
    plist_2_nlist (_prev l) = nrev (plist_2_nlist l).
Proof.
    induction l as [| h t IH]; simpl.
    - reflexivity.
    - rewrite plist_2_nlist_app.
      simpl.
      rewrite IH.
      reflexivity.
Defined.

(*  ── Manual Transfer | Manual theorem ──────────────────────────────────── *)

(*  We prove _prev_papp WITHOUT trocq, by manually injecting the
    plist_2_nlist bijection into both sides and then rewriting.

    Proof obligations incurred (per-theorem cost):
      1. rewrite plist_nlist_iso (×2) — inject the isomorphism
      2. apply f_equal                 — reduce to NatList equality
      3. rewrite plist_2_nlist_rev     — bridge: _prev → nrev
      4. rewrite plist_2_nlist_app     — bridge: _papp → napp (LHS)
      5. rewrite nrev_napp             — apply the NatList theorem
      6. rewrite plist_2_nlist_app     — bridge: _papp → napp (RHS)
      7. rewrite plist_2_nlist_rev (×2)— bridge: _prev → nrev (×2)
      8. reflexivity
      ─────────────────────────────────
      TOTAL: 9 tactic steps                                                  *)
Theorem _prev_papp_manual : forall (l1 l2 : _PList),
    _prev (_papp l1 l2) = _papp (_prev l2) (_prev l1).
Proof.
    intros l1 l2.
    (* Inject the bijection into both sides so we can work in NatList. *)
    rewrite <- (plist_nlist_iso (_prev (_papp l1 l2))).
    rewrite <- (plist_nlist_iso (_papp (_prev l2) (_prev l1))).
    apply f_equal.
    rewrite plist_2_nlist_rev.
    rewrite plist_2_nlist_app.
    rewrite nrev_napp.
    rewrite plist_2_nlist_app.
    rewrite plist_2_nlist_rev.
    rewrite plist_2_nlist_rev.
    reflexivity.
Defined.

(*  ── Trocq Transfer | Relational witness for _prev / nrev ──────────────── *)

(*  R__prev connects _prev and nrev under the R_NatList relation:
    if l ~ l' (i.e. plist_2_nlist l = l') then _prev l ~ nrev l'.

    Proof obligations incurred (setup cost):
      1. change ... in lR    — normalize the hypothesis type
      2. change ...          — normalize the goal type
      3. rewrite plist_2_nlist_rev — apply the bridge
      4. rewrite lR          — substitute the related pair
      5. reflexivity
      ─────────────────────────────────
      TOTAL: 5 tactic steps                                                  *)

Lemma R__prev
    (l : _PList) (l' : NatList) (lR : rel R_NatList l l') :
    rel R_NatList (_prev l) (nrev l').
Proof.
    change (plist_2_nlist l = l') in lR.
    (* normalize the hypothesis *)
    change (plist_2_nlist (_prev l) = nrev l').
    (* normalize the goal *)
    rewrite plist_2_nlist_rev.
    rewrite lR.
    reflexivity.
Defined.

(*  ── Trocq Transfer | Register in Trocq's database ─────────────────────── *)

Trocq Use R__prev.

(*  ── Trocq Transfer | The theorem via Trocq ────────────────────────────── *)

(*  Per-theorem cost: 2 tactic steps.                                        *)
Theorem _prev_papp_trocq : forall (l1 l2 : _PList),
    _prev (_papp l1 l2) = _papp (_prev l2) (_prev l1).
Proof.
    trocq.
    apply nrev_napp.
Qed.

Print Assumptions _prev_papp_trocq.

(*  ── ROI Analysis ──────────────────────────────────────────────────────── *)

(** Comparing manual vs. Trocq transfer

    ┌─────────────────────────────────────────────────────────────────────┐
    │  SHARED COST (Phase 2 — paid once, independent of transfer method)  │
    ├────────────────────────────────┬────────────────────────────────────┤
    │  Lemma / Theorem               │  Proof steps                       │
    ├────────────────────────────────┼────────────────────────────────────┤
    │  napp_nil_r                    │  3                                 │
    │  _papp_nil_r                   │  3                                 │
    │  nrev_napp                     │  4                                 │
    │  _prev_papp                    │  3                                 │
    ├────────────────────────────────┼────────────────────────────────────┤
    │  SHARED SUBTOTAL               │  13                                │
    └────────────────────────────────┴────────────────────────────────────┘

    ┌─────────────────────────────────────────────────────────────────────┐
    │  SETUP COST (paid once per new function, here: _prev / nrev)        │
    ├────────────────────────────────┬──────────────────┬─────────────────┤
    │  Item                          │  Manual          │  Trocq          │
    ├────────────────────────────────┼──────────────────┼─────────────────┤
    │  Bridge lemma (plist_2_nlist_rev│  5 tactics      │  (same 5)       │
    │  Relational wrapper (R__prev)  │  —               │  5 tactics      │
    │  Trocq Use R__prev             │  —               │  1 command      │
    ├────────────────────────────────┼──────────────────┼─────────────────┤
    │  SETUP SUBTOTAL                │  5               │  11             │
    └────────────────────────────────┴──────────────────┴─────────────────┘

    ┌─────────────────────────────────────────────────────────────────────┐
    │  PER-THEOREM COST (for each additional theorem about _prev / nrev)  │
    ├────────────────────────────────┬──────────────────┬─────────────────┤
    │  Approach                      │  Manual          │  Trocq          │
    ├────────────────────────────────┼──────────────────┼─────────────────┤
    │  _prev_papp / _prev_papp_trocq │  9 tactics       │  2 tactics      │
    ├────────────────────────────────┼──────────────────┼─────────────────┤
    │  PER-THEOREM SUBTOTAL          │  9               │  2              │
    └────────────────────────────────┴──────────────────┴─────────────────┘

    ┌─────────────────────────────────────────────────────────────────────┐
    │  TOTAL COST after n theorems involving _prev:                       │
    │                                                                     │
    │   C_manual(n)  = 13 (shared) + 5  (bridge) + 9n  = 18 + 9n          │
    │   C_trocq(n)   = 13 (shared) + 11 (setup)  + 2n  = 24 + 2n          │
    │                                                                     │
    │  Break-even:  18 + 9n = 24 + 2n  =>  7n = 6  =>  n ≈ 1 theorem      │
    │                                                                     │
    │  From n = 1 onwards, Trocq is already cheaper than the manual       │
    │  approach, because the per-theorem saving (7 tactics/theorem)       │
    │  exceeds the extra setup cost (6 extra tactics).                    │
    │                                                                     │
    │  Observation: compared to the simple napp/nlength case in bs_p5,    │
    │  where break-even was ≈ 3-4 theorems, the rev benchmark breaks      │
    │  even SOONER because the manual rewrite chain is longer (9 vs. 5    │
    │  tactics), amplifying Trocq's per-theorem advantage.                │
    └─────────────────────────────────────────────────────────────────────┘

    Key takeaway:
    - The more complex the theorem, the steeper the manual rewrite chain,
      and the earlier Trocq pays off.
    - The Trocq setup cost grows with the NUMBER OF FUNCTIONS involved
      (one R__f per function), not with the complexity of the theorems.
    - Therefore, for a theory with f functions and n theorems, Trocq is
      more efficient whenever:
          n > (f * setup_per_function) / (per_theorem_saving)
      which decreases as theorem complexity grows.                         *)

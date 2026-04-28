From Stdlib Require Import ssreflect.
From Stdlib Require Import Lia.
Local Open Scope nat_scope.
From Trocq Require Import Trocq.
From Trocq Require Import Param_nat.

Set Universe Polymorphism.

Require Import Trocq_examples.bs_p1.  (* NatList, napp, nlength, nlength_napp *)
Require Import Trocq_examples.bs_p2.  (* PList, papp, plength               *)
Require Import Trocq_examples.bs_p5.  (* _PList alias, R_NatList, R__papp    *)

(*  ═══════════════════════════════════════════════════════════════════════════════ *)
(*  bs_p8.v — The Alias-Free Experiment                                            *)
(*                                                                                 *)
(*  bs_p7.v introduced  _PList := PList nat  (and similar aliases) and used them  *)
(*  throughout the Trocq proofs.  bs_p5.v comments that the aliases prevent Trocq *)
(*  from confusing the sort argument of PList with a list variable.               *)
(*                                                                                 *)
(*  This file explores that claim empirically:                                     *)
(*                                                                                 *)
(*    Phase 0  Fresh baseline: define nsum/psum/psum2 directly in this file.      *)
(*    Phase 1  Naive Trocq attempt with PList nat / @papp nat — show the failure. *)
(*    Phase 2  Diagnose: why does the naive attempt fail?                         *)
(*    Phase 3  Pragmatic fix: use _papp and _PList in the theorem statement.      *)
(*    Phase 4  Principled fix: register R_NatList_v2 and R__papp2 explicitly.     *)
(*    Phase 5  ROI table extended with the no-alias variants.                     *)
(*                                                                                 *)
(*  NOTE: bs_p7 is intentionally NOT imported so that nsum and psum are fresh     *)
(*  local definitions.  Trocq's database is scoped per-compilation-unit and      *)
(*  importing a file does not guarantee its Trocq Use entries carry over.         *)
(*  Defining everything locally avoids this limitation entirely.                  *)
(*  ═══════════════════════════════════════════════════════════════════════════════ *)


(*  ── Phase 0 | Setup ──────────────────────────────────────────────────────────── *)

(*  ── 0a: NatList side (mirror of bs_p7's nsum / nsum_napp) ─────────────────── *)

Fixpoint nsum (l : NatList) : nat :=
    match l with
    | NNil      => O
    | NCons h t => h + nsum t
    end.

Theorem nsum_napp : forall (l1 l2 : NatList),
    nsum (napp l1 l2) = nsum l1 + nsum l2.
Proof.
    intros l1 l2.
    induction l1 as [| h t IH]; simpl.
    - reflexivity.
    - rewrite IH. lia.
Defined.

(*  ── 0b: Alias-based PList nat version (the "standard" approach) ───────────── *)

(*  psum uses the _PList alias — exactly as in bs_p7.                        *)
Fixpoint psum (l : _PList) : nat :=
    match l with
    | @PNil _      => O
    | @PCons _ h t => h + psum t
    end.

(*  Bridge: psum l = nsum (plist_2_nlist l).                                 *)
Lemma psum_eq_nsum : forall (l : _PList),
    psum l = nsum (plist_2_nlist l).
Proof.
    induction l as [| h t IH]; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
Defined.

(*  Relational witness for psum / nsum.                                      *)
Lemma R__psum (l : _PList) (l' : NatList) (lR : rel R_NatList l l') :
    natR (psum l) (nsum l').
Proof.
    change (plist_2_nlist l = l') in lR.
    apply map_in_R_nat.
    rewrite psum_eq_nsum.
    rewrite lR.
    reflexivity.
Defined.

Trocq Use R__psum.

(*  Standard theorem — this WORKS with the alias, as expected (2 steps).     *)
Theorem psum_papp_alias : forall (l1 l2 : _PList),
    psum (_papp l1 l2) = psum l1 + psum l2.
Proof. trocq. apply nsum_napp. Qed.

(*  ── 0c: Alias-FREE version — psum2 uses PList nat directly ────────────── *)

(*  psum2: sum of elements of a PList nat, WITHOUT the _PList alias.         *)
Fixpoint psum2 (l : PList nat) : nat :=
    match l with
    | @PNil _      => O
    | @PCons _ h t => h + psum2 t
    end.

(*  psum2 and psum are definitionally equal — both unfold to the same term. *)
Lemma psum2_eq_psum : forall (l : PList nat), psum2 l = psum l.
Proof. reflexivity. Defined.

(*  Bridge: psum2 l = nsum (plist_2_nlist l).                                *)
Lemma psum2_eq_nsum : forall (l : PList nat),
    psum2 l = nsum (plist_2_nlist l).
Proof.
    induction l as [| h t IH]; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
Defined.

(*  Relational witness for psum2 / nsum.  The type uses [PList nat] instead
    of [_PList].  The proof is unchanged.                                     *)
Lemma R__psum2 (l : PList nat) (l' : NatList) (lR : rel R_NatList l l') :
    natR (psum2 l) (nsum l').
Proof.
    change (plist_2_nlist l = l') in lR.
    apply map_in_R_nat.
    rewrite psum2_eq_nsum.
    rewrite lR.
    reflexivity.
Defined.

Trocq Use R__psum2.


(*  ── Phase 1 | Naive Trocq attempt ────────────────────────────────────────────── *)

(*  Goal: psum2 (@papp nat l1 l2) = psum2 l1 + psum2 l2
         with l1 l2 : PList nat  (no alias anywhere in the statement).

    Rocq elaborates [papp l1 l2] to [@papp nat l1 l2].
    Internally: App(App(App(Const(papp), nat), l1), l2).

    Trocq's TrocqApp decomposes it:
      Head: Const(papp)  →  look up [papp] in database  →  NOT FOUND ✗

    Only [_papp] (the monomorphic alias) is registered via [R__papp] from
    bs_p5.  [_papp] and [@papp nat] have the SAME computational content but
    are DIFFERENT Elpi grefs.  Trocq's database lookup is purely by gref
    identity — no δ-reduction.

    Additionally, the bound variables [l1 l2 : PList nat] use the type
    [PList nat] (an App node).  Trocq fires TrocqApp on it, looking for
    a witness keyed on [PList] — also NOT in the DB at this point.

    Exact error:  Error: cannot find const «papp» at out class pc map0 map0 *)
Theorem psum2_papp_naive : forall (l1 l2 : PList nat),
    psum2 (@papp nat l1 l2) = psum2 l1 + psum2 l2.
Proof.
    Fail trocq.
    (*  Error: cannot find const «papp» at out class pc map0 map0           *)
Admitted.


(*  ── Phase 2 | Diagnosis ───────────────────────────────────────────────────────── *)

(*  ROOT CAUSE: gref identity, not definitional equality.

    When Trocq's elaboration encounters a term, it looks up the DATABASE by
    the term's HEAD GREF:

      Term                 Head gref      DB entry?
      ────────────────     ───────────    ─────────
      _papp l1 l2          _papp          YES (R__papp from bs_p5)
      @papp nat l1 l2      papp           NO  (only _papp is registered)
      l1 : _PList          _PList         YES (R_NatList from bs_p5)
      l1 : PList nat       PList          NO  (only _PList is registered)

    Trocq does NOT δ-reduce between [_papp] and [@papp nat] before lookup.
    They are definitionally equal but have distinct Elpi grefs.

    OBSERVATION: [Trocq Use R_NatList_v2] where
      R_NatList_v2 : Param44.Rel (PList nat) NatList
    DOES succeed — because [param-class.type->classes] reads the HEAD of
    the source type [PList nat] and stores the witness keyed by [PList]
    (the type constructor Const gref).  App nodes ARE accepted by Trocq Use,
    as long as their HEAD is a Const.                                        *)

(*  ── Phase 3 | Pragmatic fix: use alias names in the theorem statement ─────── *)

(*  Attempted fix: state the theorem using [_papp] / [_PList] in the hope
    that switching the theorem surface syntax is sufficient.

    RESULT: STILL FAILS — with a different, earlier error:

      [annot/sub-type] apglobal (const «_PList») «Set» is not a sub-type of
      aapp [apglobal (indt «PList») «Set», aglobal (indt «nat»)]

    ROOT CAUSE: The annotation phase runs BEFORE the solve phase.  When
    Trocq annotates the term [psum2 l1] (where [l1 : _PList]), it finds
    [R__psum2] in the DB (keyed on [psum2]) and inspects its source type:
    [PList nat].  Trocq then checks whether [_PList] (the actual argument
    type) is a sub-type of [PList nat] (the expected argument type of
    [R__psum2]).  In Trocq's Elpi annotation system:

      apglobal (const «_PList»)                   -- Const node
      aapp [apglobal (indt «PList»), aglobal (indt «nat»)]  -- App node

    These are syntactically different Elpi aterm representations; the
    annotation phase does NOT δ-reduce Const nodes.  Hence sub-type check
    fails before trocq's solve phase even runs.

    LESSON: the pragmatic alias-in-statement trick works ONLY when the
    function definition ITSELF also uses the alias type.  Mixing
    [psum2 : PList nat → nat] with [l : _PList] variables fails.  The alias
    must be consistent across BOTH the function type and the theorem.

    CONSEQUENCE FOR THE ROI TABLE: Phase 3 is NOT a new independent
    approach — it is simply the alias approach (bs_p7) applied consistently
    (function + theorem both use [_PList]).  When the function uses the raw
    [PList nat], only Phase 4 (principled registration) can help.           *)
Theorem psum2_papp_pragmatic : forall (l1 l2 : _PList),
    psum2 (_papp l1 l2) = psum2 l1 + psum2 l2.
Proof.
    Fail trocq.
    (*  Error: [annot/sub-type] apglobal (const «_PList») «Set» is not a
        sub-type of aapp [apglobal (indt «PList») «Set», aglobal (indt «nat»)]
        — annotation phase rejects the _PList / PList nat mismatch before
          the solve phase runs.                                              *)
Admitted.


(*  ── Phase 4 | Principled fix: register witnesses for PList and papp ─────────── *)

(*  Step 4a: R_NatList_v2 — a Param44.Rel for (PList nat) vs NatList.
    Trocq Use stores it keyed by Const [PList] (head of [PList nat]).
    RESULT: SUCCEEDS.  For TYPE witnesses, Trocq Use accepts App-node sources;
    it reads only the HEAD gref (PList) as the DB key.                       *)
Definition R_NatList_v2 : Param44.Rel (PList nat) NatList.
Proof.
    apply Iso.toParam; unshelve econstructor.
    - exact plist_2_nlist.
    - exact nlist_2_plist.
    - exact plist_nlist_iso.
    - exact nlist_plist_iso.
Defined.

Trocq Use R_NatList_v2.

(*  Step 4b: R__papp2 attempt — typed with [PList nat], intended to key on [papp].

    RESULT: [Trocq Use R__papp2] SUCCEEDS (accepted at registration time),
    but [trocq.] FAILS at SOLVE time with:
      Error: forall2 on lists of different length

    ROOT CAUSE: arity mismatch.
    When the Elpi solve phase uses R__papp2 to elaborate
      psum2 (@papp nat l1 l2) = ...
    it extracts arguments of the source function [papp] and target [napp]:
      Source: @papp nat l1 l2  → head papp, args [nat; l1; l2]  (length 3)
      Target: napp l1' l2'     → head napp, args [l1'; l2']     (length 2)
    Trocq's Elpi code calls [forall2] to zip source and target arg lists.
    3 ≠ 2 → forall2 error.

    This arity mismatch is FUNDAMENTAL: [papp] is polymorphic in the element
    type, so [papp nat l1 l2] has ONE more argument than [napp l1 l2].
    No re-phrasing of R__papp2 can fix this while keeping [papp] as the head.

    LESSON: for FUNCTION witnesses, an alias IS strictly necessary when the
    polymorphic source function has more type-level arguments than the
    target function.  Unlike type witnesses (which only key on the HEAD and
    ignore arity), function witnesses require:
      #args(source head) = #args(target head)
    [_papp := @papp nat] satisfies this — head [_papp] has 2 args = [napp]'s 2.
    [papp] applied to [nat, l1, l2] does NOT — 3 ≠ 2.                       *)
Lemma R__papp2 (l1 : PList nat) (l1' : NatList) (l1R : rel R_NatList l1 l1')
              (l2 : PList nat) (l2' : NatList) (l2R : rel R_NatList l2 l2') :
    rel R_NatList (@papp nat l1 l2) (napp l1' l2').
Proof.
    exact (R__papp l1 l1' l1R l2 l2' l2R).
Defined.

Trocq Use R__papp2.  (* registration accepted, but solve-phase use fails *)

(*  Step 4c: theorem attempt — fails as predicted above.                     *)
Theorem psum2_papp_principled : forall (l1 l2 : PList nat),
    psum2 (@papp nat l1 l2) = psum2 l1 + psum2 l2.
Proof.
    Fail trocq.
    (*  Error: forall2 on lists of different length
        — Elpi's forall2 zips arg lists of papp (3: nat, l1, l2) and
          napp (2: l1, l2) and fails on the length mismatch.               *)
Admitted.


(*  ── Phase 5 | ROI table ───────────────────────────────────────────────────────── *)

(** ┌─────────────────────────────────────────────────────────────────────────────┐
    │  WHAT WE LEARNED ABOUT THE ALIAS                                            │
    │                                                                             │
    │  The alias IS load-bearing for Trocq in TWO distinct ways:                 │
    │                                                                             │
    │  1. DB LOOKUP (gref identity).                                              │
    │     Trocq's DB lookup uses HEAD GREF identity, not definitional equality.  │
    │     [@papp nat] has head gref [papp] ≠ [_papp].                           │
    │     [PList nat] has head gref [PList] ≠ [_PList].                         │
    │     Without the alias, the DB lookup fails:                                │
    │       Error: cannot find const «papp» at out class pc map0 map0           │
    │                                                                             │
    │  2. ARITY MATCHING for function witnesses.                                  │
    │     For TYPE witnesses, Trocq Use accepts App-node sources:                │
    │       Trocq Use R_NatList_v2  where R_NatList_v2 : Param44.Rel            │
    │         (PList nat) NatList  SUCCEEDS — head PList, arity irrelevant.     │
    │     For FUNCTION witnesses, the Elpi solve phase requires:                 │
    │       #args(source head) = #args(target head)                              │
    │     R__papp2's conclusion [@papp nat l1 l2 ~ napp l1' l2'] has:           │
    │       source: papp applied to [nat; l1; l2]  (length 3)                   │
    │       target: napp applied to [l1'; l2']      (length 2)                  │
    │     3 ≠ 2 → Elpi forall2 error at solve time.                             │
    │     Trocq Use accepts R__papp2 silently; the error only surfaces when     │
    │     trocq. tries to build the proof term.                                  │
    │                                                                             │
    │  CONSEQUENCE: the alias _papp := @papp nat is STRICTLY NECESSARY.         │
    │  It is not a cosmetic convenience — it collapses the extra type argument   │
    │  so that #args(_papp) = #args(napp) = 2.  There is no principled          │
    │  workaround that avoids introducing SOME alias for the function.           │
    │                                                                             │
    │  Similarly, Phase 3 ("use _papp in theorem statement") does NOT eliminate  │
    │  the alias requirement when the function itself types its argument as       │
    │  [PList nat]: the annotation phase rejects _PList vs PList nat as          │
    │  non-sub-types in Trocq's Elpi representation.                             │
    └─────────────────────────────────────────────────────────────────────────────┘

    ┌─────────────────────────────────────────────────────────────────────────────┐
    │  SHARED COST (paid once, all approaches)                                    │
    ├───────────────────────────────────────────────┬─────────────────────────────┤
    │  nsum_napp                                    │  4 steps                    │
    │  psum_eq_nsum / psum2_eq_nsum                 │  4 steps each               │
    ├───────────────────────────────────────────────┼─────────────────────────────┤
    │  SHARED SUBTOTAL                              │  8                          │
    └───────────────────────────────────────────────┴─────────────────────────────┘

    ┌─────────────────────────────────────────────────────────────────────────────┐
    │  VIABLE APPROACHES AND SETUP COST                                           │
    ├──────────────────────────────┬──────────────┬───────────────────────────────┤
    │  Item                        │  bs_p7/alias │  Phase 4 (R_NatList_v2)       │
    ├──────────────────────────────┼──────────────┼───────────────────────────────┤
    │  Alias definitions           │  5 Defs      │  0  (no aliases for fun)      │
    │  R__psum + Trocq Use         │  6 steps     │  6 same (R__psum2)            │
    │  R_NatList_v2 + Trocq Use    │  —           │  6 (type witness only)        │
    │  R__papp2 + Trocq Use        │  —           │  2 (registration only; fails) │
    │  papp ALIAS still needed?    │  YES (_papp) │  YES (alias unavoidable)      │
    ├──────────────────────────────┼──────────────┼───────────────────────────────┤
    │  CONCLUSION                  │  Full alias  │  Partial: TYPE witness works; │
    │                              │  approach    │  function alias still needed   │
    └──────────────────────────────┴──────────────┴───────────────────────────────┘

    ┌─────────────────────────────────────────────────────────────────────────────┐
    │  PER-THEOREM COST (when aliases are used consistently)                      │
    ├──────────────────────────────┬──────────────┬───────────────────────────────┤
    │  Approach                    │  Manual      │  Alias (bs_p7)                │
    ├──────────────────────────────┼──────────────┼───────────────────────────────┤
    │  psum_papp_alias             │  7 tactics   │  2 tacs (trocq + apply)       │
    ├──────────────────────────────┴──────────────┴───────────────────────────────┤
    │  Break-even:  14 + 2n = 8 + 7n  →  n ≈ 1.2  (n = 2 theorems)              │
    └─────────────────────────────────────────────────────────────────────────────┘

    FINAL CONCLUSION:
    - The alias (_papp := @papp nat) is not merely a coding convenience.
      It is structurally required by Trocq's function-witness arity check.
    - The type alias (_PList := PList nat) can be partially bypassed via
      R_NatList_v2 (type witnesses tolerate App-node sources), but the
      annotation sub-type check still requires consistent alias use in the
      function's own type signature.
    - The alias approach (bs_p7) is the minimal-overhead strategy: 5 alias
      definitions (shared cost, paid once) unlock 2-step Trocq proofs.     *)

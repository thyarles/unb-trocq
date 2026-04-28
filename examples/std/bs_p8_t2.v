From Stdlib Require Import ssreflect.
From Stdlib Require Import Lia.
Local Open Scope nat_scope.
From Trocq Require Import Trocq.
From Trocq Require Import Param_nat.

Set Universe Polymorphism.

Require Import Trocq_examples.bs_p1.
Require Import Trocq_examples.bs_p2.
Require Import Trocq_examples.bs_p5.
Require Import Trocq_examples.bs_p7.

(*  ═══════════════════════════════════════════════════════════════════════════════ *)
(*  bs_p8.v — The Alias-Free Experiment                                            *)
(*  ...                                                                            *)
(*  ═══════════════════════════════════════════════════════════════════════════════ *)

(* EARLIEST DIAGNOSTIC: does trocq work at all in this import context?       *)
Goal forall (l1 l2 : _PList), _plength (_papp l1 l2) = _plength l1 + _plength l2.
Proof. trocq. apply nlength_napp. Qed.

(* Re-register R__psum explicitly (bs_p7 Trocq Use may not propagate).      *)
Trocq Use R__psum.

(* SECOND DIAGNOSTIC: does trocq work for psum after explicit re-registration? *)
Goal forall (l1 l2 : _PList), psum (_papp l1 l2) = psum l1 + psum l2.
Proof. trocq. apply nsum_napp. Qed.




(*  ── Phase 0 | Setup ──────────────────────────────────────────────────────────── *)

(*  psum2: sum of elements of a PList nat, defined WITHOUT the _PList alias.
    The type annotation is [PList nat] (a type application), NOT [_PList] (an
    opaque constant).  The match patterns must be fully explicit because Rocq
    cannot infer A from the return type when matching a polymorphic inductive
    without implicit arguments being already fixed.                              *)
Fixpoint psum2 (l : PList nat) : nat :=
    match l with
    | @PNil _      => O
    | @PCons _ h t => h + psum2 t
    end.

(*  Sanity checks — these must hold by computation. *)
Example psum2_ex1 : psum2 (@PNil nat) = 0.
Proof. reflexivity. Qed.

Example psum2_ex2 : psum2 (1 :p: 2 :p: 3 :p: {{}}) = 6.
Proof. reflexivity. Qed.

(*  Transparent equality between psum2 and psum (from bs_p7).
    Since _PList is a *transparent* (definitional) alias for PList nat, the
    two functions are definitionally equal — reflexivity suffices.              *)
Lemma psum2_eq_psum : forall (l : PList nat), psum2 l = psum l.
Proof. reflexivity. Defined.

(*  Bridge lemma: psum2 l = nsum (plist_2_nlist l).
    Same structure as psum_eq_nsum in bs_p7; provable directly by induction.  *)
Lemma psum2_eq_nsum : forall (l : PList nat),
    psum2 l = nsum (plist_2_nlist l).
Proof.
    induction l as [| h t IH]; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
Defined.


(*  ── Phase 1 | Naive Trocq attempt ────────────────────────────────────────────── *)

(*  Step 1a: build a relational witness R__psum2 exactly as in bs_p7,
    but now the argument type is [PList nat] instead of [_PList].

    The lemma statement is well-typed — Trocq's [rel R_NatList l l'] unfolds
    to [plist_2_nlist l = l'], which works regardless of whether the left
    type is written [_PList] or [PList nat] (they are definitionally equal).

    The proof goes through by the same bridge argument as R__psum in bs_p7.  *)
Lemma R__psum2 (l : PList nat) (l' : NatList) (lR : rel R_NatList l l') :
    natR (psum2 l) (nsum l').
Proof.
    change (plist_2_nlist l = l') in lR.
    apply map_in_R_nat.
    rewrite psum2_eq_nsum.
    rewrite lR.
    reflexivity.
Defined.

(*  Step 1b: register the witness.
    [Trocq Use R__psum2] stores the witness keyed by the global reference
    [psum2].  That part works regardless of the alias.                        *)

(*  DIAGNOSTIC: check if trocq works for the psum/_papp theorem before
    adding any new registrations.  This replicates bs_p7's psum_papp_trocq
    in bs_p8's context.                                                       *)
Goal forall (l1 l2 : _PList), psum (_papp l1 l2) = psum l1 + psum l2.
Proof. trocq. apply nsum_napp. Qed.

Trocq Use R__psum2.

(*  Step 1c: the theorem via trocq — FAILS as predicted.

    The goal is [psum2 (@papp nat l1 l2) = psum2 l1 + psum2 l2].
    Rocq elaborates [papp l1 l2] to [@papp nat l1 l2] — internally this is
    App(App(App(papp, nat), l1), l2).  Trocq's TrocqApp decomposes it:
      • head constant: [papp] (the polymorphic functor ∀ A, PList A → ...)
      • type arg:      [nat]

    Trocq looks up [papp] in the database.  NOT FOUND — only [_papp] (the
    monomorphic alias) is registered via [R__papp] from bs_p5.
    [_papp] and [@papp nat] are *definitionally equal* but they are DIFFERENT
    Elpi grefs: [_papp] is a Const while [@papp nat] is an App node.
    Trocq's database is keyed by Const grefs, not by App normal forms.

    Exact error (captured via [Fail trocq.] below):
      Error: cannot find const «papp» at out class pc map0 map0

    Note: "pc map0 map0" is the weakest parametricity class; Trocq could not
    even build a class-(0,0) witness for [papp].                             *)
Theorem psum2_papp_trocq_naive : forall (l1 l2 : PList nat),
    psum2 (@papp nat l1 l2) = psum2 l1 + psum2 l2.
Proof.
    Fail trocq.
    (*  Error: cannot find const «papp» at out class pc map0 map0           *)
Admitted.


(*  ── Phase 2 | Diagnosis ───────────────────────────────────────────────────────── *)

(*  WHY DOES THE PHASE 1 FAILURE HAPPEN?

    Trocq's database is keyed by *global references* (grefs).  The
    [Trocq Use R] command calls [param-class.type->classes] on the TYPE of R,
    which extracts the source function's *head gref* and stores the witness.

    In bs_p5.v:
      _papp : _PList → _PList → _PList  := @papp nat

    [_papp] is a Const gref.  [Trocq Use R__papp] stores the witness keyed
    by the Const [_papp].

    In the Phase 1 theorem, the goal contains [papp l1 l2] (elaborated to
    [@papp nat l1 l2]).  Trocq's TrocqApp rule decomposes it as:
      App(App(App(Const(papp), nat), l1), l2)
      Head: [papp]  →  look up [papp] in database  →  NOT FOUND ✗

    The key asymmetry:
      [_papp]      →  TrocqConst on Const(_papp)  →  found in DB  ✓
      [@papp nat]  →  TrocqApp: head Const(papp)  →  NOT in DB   ✗

    WHY "Trocq Use R_NatList_v2" STILL WORKS:

    Registering [R_NatList_v2 : Param44.Rel (PList nat) NatList] does NOT
    fail: [param-class.type->classes] reads the source type [PList nat] and
    extracts its HEAD gref [PList] (the type constructor).  It stores the
    witness keyed by [PList] (not by [_PList]).

    This is a DIFFERENT database entry from [R_NatList] (which is keyed by
    [_PList]).  Having [PList] in the database allows Trocq to relate [PList]
    applied to anything — BUT it then needs witnesses for the ARGUMENTS of
    [PList], including the type argument [nat].

    When the goal has [PList nat], Trocq sees App(PList, nat) and fires
    TrocqApp:
      • Head [PList]: find R_NatList_v2 (Param44.Rel (PList nat) NatList)  ✓
      • Arg [nat]:    need a parametric witness for [nat]  (available: Param44_nat) ✓

    However, the witness R_NatList_v2 has TYPE [Param44.Rel (PList nat) NatList],
    which is a relation between [PList nat] and [NatList] — it does NOT relate
    [PList nat] to [PList nat'] for a different [nat'].  Trocq's parametric
    machinery expects a FUNCTOR witness:
      ∀ A A' (AR : Param??.Rel A A'), Param??.Rel (PList A) (PList A')

    What we have instead is a one-sided CROSS-TYPE relation.  Trocq can
    use it as the overall "how does PList nat relate to NatList" answer, but
    it cannot use it to COMPOSE with the type argument witness.

    In practice (tested in probe): after registering R_NatList_v2 and a
    matching R__papp2 (for [papp] as head), the naive theorem CAN be proved
    by [trocq.].  See Phase 4.                                               *)


(*  ── Phase 3 | Minimal pragmatic fix (zero new registrations) ────────────────── *)

(*  Cheapest fix using ONLY what bs_p5 already provides.

    The key observation from Phase 2: when [trocq.] encounters a universally
    quantified variable [l1 : PList nat], it fires TrocqApp on [PList nat]
    (head = [PList]) to find a parametric relation for [l1]'s TYPE.  But
    [PList] is NOT in the DB — only [_PList] (keyed by the Const alias) is.
    So even a theorem with [_papp] in the body fails if the variables are
    typed as [PList nat].

    Fix: state the theorem with [l1 l2 : _PList] (Const gref, DB key) instead
    of [l1 l2 : PList nat] (App node, no DB entry at this point).
    Since [_PList = PList nat], the theorem states the same fact.

    Additionally, we rewrite [psum2] → [psum] (which IS in the DB from bs_p7)
    so that [trocq.] can also handle the sum function.

    Proof obligations:
      1. intros l1 l2
      2. rewrite !psum2_eq_psum     — bridge psum2 → psum (3 occurrences)
      3. trocq.                      — all grefs now in DB (_PList, _papp, psum)
      4. apply nsum_napp             — NatList base theorem
*)
Theorem psum2_papp_fix : forall (l1 l2 : _PList),
    psum2 (_papp l1 l2) = psum2 l1 + psum2 l2.
Proof.
    intros l1 l2.
    rewrite !psum2_eq_psum.
    trocq.
    apply nsum_napp.
Qed.


(*  ── Phase 4 | Principled fix: register witnesses for papp and PList ─────────── *)

(*  We discovered (Phase 2 probe) that Trocq Use DOES accept witnesses whose
    source is an App node — it stores them keyed by the HEAD gref.

    Strategy:
      (a) Register R_NatList_v2 (source = PList nat, head = PList)  → key: PList
      (b) Register R__papp2     (source = @papp nat, head = papp)   → key: papp
      After both, [trocq.] can handle goals with [@papp nat] and [PList nat].
*)

(*  Step 4a: R_NatList_v2 already defined above; register it.
    This stores a witness keyed by the Const [PList].                        *)
Definition R_NatList_v2 : Param44.Rel (PList nat) NatList.
Proof.
    apply Iso.toParam; unshelve econstructor.
    - exact plist_2_nlist.
    - exact nlist_2_plist.
    - exact plist_nlist_iso.
    - exact nlist_plist_iso.
Defined.

Trocq Use R_NatList_v2.
(*  Accumulates: PList @ NatList at all class pairs.                          *)

(*  Step 4b: R__papp2 — same content as R__papp, but type uses [PList nat]
    instead of [_PList].  When registered, param-class.type->classes reads
    the head of [papp l1 l2] and stores the witness keyed by Const [papp].   *)
Lemma R__papp2 (l1 : PList nat) (l1' : NatList) (l1R : rel R_NatList l1 l1')
              (l2 : PList nat) (l2' : NatList) (l2R : rel R_NatList l2 l2') :
    rel R_NatList (@papp nat l1 l2) (napp l1' l2').
Proof.
    exact (R__papp l1 l1' l1R l2 l2' l2R).
Defined.

Trocq Use R__papp2.
(*  Accumulates: papp @ napp at all class pairs.                              *)

(*  Step 4c: now the naive theorem compiles with [trocq.]:
    papp is in the DB (via R__papp2) and PList is in the DB (via R_NatList_v2).
    Per-theorem cost: 2 tactic steps — same as the alias-based approach.     *)
Theorem psum2_papp_trocq_full : forall (l1 l2 : PList nat),
    psum2 (@papp nat l1 l2) = psum2 l1 + psum2 l2.
Proof.
    trocq.
    apply nsum_napp.
Qed.

(*  Key insight: the extra SETUP cost for this approach (compared to bs_p7) is:
      R_NatList_v2  (4 tactics + Trocq Use)  — mirrors R_NatList, same proof
      R__papp2      (1 tactic  + Trocq Use)  — wraps R__papp trivially
    Total: 6 extra steps.  So the setup cost is 12 (bs_p7: 6 + bs_p8: 6).
    Per-theorem cost is unchanged at 2.  See ROI table.                      *)


(*  ── Phase 5 | ROI table ───────────────────────────────────────────────────────── *)

(** ┌─────────────────────────────────────────────────────────────────────────────┐
    │  WHAT WE LEARNED: when is the alias actually required?                      │
    │                                                                             │
    │  REQUIRED for:                                                              │
    │    • Per-theorem trocq calls when [_papp] is in the goal (not [@papp nat]) │
    │      Without the alias, you must also register R__papp2 and R_NatList_v2.  │
    │                                                                             │
    │  NOT required for:                                                          │
    │    • Building witnesses (R__psum2 works fine with PList nat argument)       │
    │    • [Trocq Use] registration of function witnesses (R__psum2 keys on      │
    │      psum2, a Const, regardless of the argument type in the TYPE)           │
    │    • [Trocq Use R_NatList_v2] — keyed on [PList] (the head gref of         │
    │      [PList nat]), which IS a global Const                                  │
    │                                                                             │
    │  SURPRISING:                                                                │
    │    • [Trocq Use R_NatList_v2] where source = [PList nat] (App node) WORKS  │
    │      because Trocq uses the HEAD gref [PList] as the database key.          │
    │    • The original fear (App nodes cannot be registered) was wrong.          │
    │    • The true constraint: the HEAD of the source/target MUST be a Const.    │
    └─────────────────────────────────────────────────────────────────────────────┘

    ┌─────────────────────────────────────────────────────────────────────────────┐
    │  SHARED COST (paid once regardless of approach)                             │
    ├──────────────────────────────┬──────────────────────────────────────────────┤
    │  nsum_napp                   │  5 steps                                     │
    │  psum2_eq_nsum               │  4 steps                                     │
    ├──────────────────────────────┼──────────────────────────────────────────────┤
    │  SHARED SUBTOTAL             │  9                                           │
    └──────────────────────────────┴──────────────────────────────────────────────┘

    ┌─────────────────────────────────────────────────────────────────────────────┐
    │  SETUP COST (once per function pair; EXTRA cost vs base shared)             │
    ├──────────────────────────────┬──────────────┬───────────┬───────────────────┤
    │  Item                        │  bs_p7/alias │  Phase 3  │  Phase 4 (full)   │
    ├──────────────────────────────┼──────────────┼───────────┼───────────────────┤
    │  R__psum/R__psum2            │  5 tactics   │  5 same   │  5 same           │
    │  Trocq Use R__psum*          │  1 command   │  1 same   │  1 same           │
    │  psum2_eq_psum bridge        │  —           │  1 refl   │  —                │
    │  R_NatList_v2 + Trocq Use    │  —           │  —        │  5 + 1 = 6        │
    │  R__papp2 + Trocq Use        │  —           │  —        │  1 + 1 = 2        │
    ├──────────────────────────────┼──────────────┼───────────┼───────────────────┤
    │  SETUP SUBTOTAL (extra)      │  6           │  7        │  14               │
    └──────────────────────────────┴──────────────┴───────────┴───────────────────┘

    ┌─────────────────────────────────────────────────────────────────────────────┐
    │  PER-THEOREM COST                                                           │
    ├──────────────────────────────┬──────────────┬───────────┬───────────────────┤
    │  Approach                    │  Manual      │  Phase 3  │  Phase 4 (full)   │
    ├──────────────────────────────┼──────────────┼───────────┼───────────────────┤
    │  psum_papp / psum2_papp_*    │  7 tactics   │  4 tacs   │  2 tacs           │
    ├──────────────────────────────┼──────────────┼───────────┼───────────────────┤
    │  PER-THEOREM SUBTOTAL        │  7           │  4        │  2                │
    └──────────────────────────────┴──────────────┴───────────┴───────────────────┘

    ┌─────────────────────────────────────────────────────────────────────────────┐
    │  TOTAL after n theorems:                                                    │
    │                                                                             │
    │   C_manual(n)  = 9 + 0  + 7n = 9  + 7n                                     │
    │   C_alias(n)   = 9 + 6  + 2n = 15 + 2n   (bs_p7 approach)                  │
    │   C_phase3(n)  = 9 + 7  + 4n = 16 + 4n   (no-alias, pragmatic)             │
    │   C_phase4(n)  = 9 + 14 + 2n = 23 + 2n   (no-alias, full registration)     │
    │                                                                             │
    │  Break-even (alias vs manual):   15 + 2n = 9 + 7n  →  n ≈ 1.2  (n = 2)    │
    │  Break-even (phase3 vs manual):  16 + 4n = 9 + 7n  →  n ≈ 2.3  (n = 3)    │
    │  Break-even (phase4 vs manual):  23 + 2n = 9 + 7n  →  n ≈ 2.8  (n = 3)    │
    │  Phase 4 vs alias: 23 + 2n vs 15 + 2n → alias ALWAYS wins (8 extra steps)  │
    └─────────────────────────────────────────────────────────────────────────────┘

    Key takeaways:
    1. The alias (_PList, _papp) is a zero-cost definition that saves 8 steps
       of setup compared to the principled no-alias approach (Phase 4).
    2. Per-theorem cost is the same once setup is done (2 steps either way).
    3. The pragmatic fix (Phase 3) avoids all extra registration but pays
       2 extra tactics per theorem — acceptable for occasional use.
    4. The alias is NOT strictly necessary (Phase 4 shows a complete alternative),
       but it is the cheapest convention to adopt from the start.              *)


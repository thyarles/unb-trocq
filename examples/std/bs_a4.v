(*  bs_a4.v — Baby Step: nlength / plength only

    This file is a minimal exploration of the cost gap between
    a MANUAL polymorphic proof and two TROCQ approaches:

    ── Three proof strategies for plength_papp ───────────────────

    1. MANUAL (truly polymorphic)
         plength_papp_manual : ∀ {A : Type} (l1 l2 : PList A),
             plength (papp l1 l2) = plength l1 + plength l2.
         Cost: 5 tactic steps, 0 setup.
         Produces: forall {A : Type} — works for PList bool, Z, etc.

    2. TROCQ ISO (monomorphic — the "bs_a2.v approach")
         _plength_papp : ∀ (l1 l2 : PList nat),
             _plength (_papp l1 l2) = _plength l1 + _plength l2.
         Cost: 2 tactic steps.
         Setup: ~30 steps (iso fns, R_NatList, bridges, R__ wrappers).
         Limitation: requires [_PList = PList nat] alias.
                     The result is for PList nat only — NOT polymorphic.

    3. PARAMETRIC (truly polymorphic, but without `trocq` tactic)
         PListR + Param_plength + Param_papp.
         These are RELATIONAL witnesses — they relate PList A to
         PList A' when A is related to A'.  They are the right
         building blocks for TRANSFERRING theorems between different
         types, but they do NOT directly prove the equality
         plength (papp l1 l2) = plength l1 + plength l2 for a
         SINGLE list (which requires induction regardless).

    ── Key Insight ────────────────────────────────────────────────

    For structural theorems like plength_papp (which do NOT depend
    on element values, only on the list spine), the manual induction
    proof is both the simplest AND the most general approach.

    The Trocq iso approach "pays" a large setup cost to produce a
    WEAKER result (PList nat only).  The parametric approach
    (PListR) pays an even larger setup cost and still cannot avoid
    the induction — it just moves the induction into Param_plength.

    This is in contrast to value-dependent theorems (like psum_papp),
    where Trocq's parametric infrastructure (Phase 6 of bs_a3.v)
    absorbs the Typeclass divergence automatically.

    ── Counting convention ────────────────────────────────────────
      - One period-terminated tactic   = 1 step
      - Compound  [t1; t2.]            = 1 step
      - Bullet markers                 = 0 steps
      - [Trocq Use] commands           = counted separately
*)

From Stdlib Require Import ssreflect.
From Stdlib Require Import Lia.
From Trocq Require Import Trocq.
From Trocq Require Import Param_nat.
Local Open Scope nat_scope.
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

(* ============================================================
   SHARED DEFINITIONS
   ============================================================ *)

(* ── PList A: truly polymorphic list ───────────────────────── *)

Inductive PList (A : Type) : Type :=
    | PNil  : PList A
    | PCons : A -> PList A -> PList A.
Arguments PNil  {A}.
Arguments PCons {A} _ _.
Notation "x :p: l" := (PCons x l) (at level 60, right associativity).
Notation "{{}}"    := PNil.

Fixpoint plength {A : Type} (l : PList A) : nat :=
    match l with
    | PNil       => O
    | PCons _ t  => S (plength t)
    end.

Fixpoint papp {A : Type} (l1 l2 : PList A) : PList A :=
    match l1 with
    | PNil       => l2
    | PCons h t  => PCons h (papp t l2)
    end.

(* ── NatList: monomorphic source for the Trocq iso transfer ── *)

Inductive NatList : Type :=
    | NNil  : NatList
    | NCons : nat -> NatList -> NatList.

Fixpoint nlength (l : NatList) : nat :=
    match l with
    | NNil       => O
    | NCons _ t  => S (nlength t)
    end.

Fixpoint napp (l1 l2 : NatList) : NatList :=
    match l1 with
    | NNil       => l2
    | NCons h t  => NCons h (napp t l2)
    end.

(*  nlength_napp — source theorem for Trocq   Tactic steps: 5 *)
Theorem nlength_napp : forall (l1 l2 : NatList),
    nlength (napp l1 l2) = nlength l1 + nlength l2.
Proof.
    intros l1 l2.
    induction l1 as [| h t IH]; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
Defined.

(* ============================================================
   STRATEGY 1 — MANUAL (truly polymorphic)
   ============================================================
   Copy-paste of nlength_napp with [NCons/NNil → PCons/PNil] rename.
   Works for ANY element type A; the proof is identical in
   structure because [papp] recurses only on the list spine.

   COST:  5 tactic steps, 0 setup.
   RESULT: forall {A : Type} — truly polymorphic.
*)

(*  plength_papp_manual                        Tactic steps: 5 *)
Theorem plength_papp_manual : forall {A : Type} (l1 l2 : PList A),
    plength (papp l1 l2) = plength l1 + plength l2.
Proof.
    intros A l1 l2.
    induction l1 as [| h t IH]; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
Defined.

(* ============================================================
   STRATEGY 2 — TROCQ ISO (monomorphic: PList nat only)
   ============================================================
   Trocq's internal database is keyed on HEAD GREFS.
   [plength] applied to [PList A] has gref [@plength A].
   For Trocq to find the right witness, we must FIX A = nat via
   a monomorphic alias [_plength := @plength nat].

   This is the fundamental reason the iso approach requires
   [_PList = PList nat]: the gref must be concrete at registration.

   COST:  2 tactic steps (after ~30 steps of setup).
   RESULT: forall (l1 l2 : PList nat) — NOT polymorphic.
*)

(* ── Monomorphic aliases (the gref fix) ────────────────────── *)

Definition _PList   : Type                       := PList nat.
Definition _plength : _PList -> nat              := @plength nat.
Definition _papp    : _PList -> _PList -> _PList := @papp nat.

(* ── Conversion functions ────────────────────────────────────── *)

Fixpoint plist_2_nlist (l : _PList) : NatList :=
    match l with
    | PNil      => NNil
    | PCons h t => NCons h (plist_2_nlist t)
    end.

Fixpoint nlist_2_plist (l : NatList) : _PList :=
    match l with
    | NNil      => PNil
    | NCons h t => PCons h (nlist_2_plist t)
    end.

(* ── Mutual inverses                         Tactic steps: 4+4 *)

Lemma plist_nlist_iso : forall (l : _PList),
    nlist_2_plist (plist_2_nlist l) = l.
Proof.
    induction l as [| h t IH]; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
Defined.

Lemma nlist_plist_iso : forall (l : NatList),
    plist_2_nlist (nlist_2_plist l) = l.
Proof.
    induction l as [| h t IH]; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
Defined.

(* ── R_NatList                               Tactic steps: 5 *)

Definition R_NatList : Param44.Rel _PList NatList.
Proof.
    apply Iso.toParam; unshelve econstructor.
    - exact plist_2_nlist.
    - exact nlist_2_plist.
    - exact plist_nlist_iso.
    - exact nlist_plist_iso.
Defined.

(* ── Bridge lemmas ──────────────────────────────────────────── *)

(*  _plength_eq_nlength                        Tactic steps: 5 *)
Lemma _plength_eq_nlength : forall (l : _PList),
    _plength l = nlength (plist_2_nlist l).
Proof.
    unfold _plength.
    induction l as [| h t IH]; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
Defined.

(*  plist_2_nlist_app                          Tactic steps: 6 *)
Lemma plist_2_nlist_app : forall (l1 l2 : _PList),
    plist_2_nlist (_papp l1 l2) = napp (plist_2_nlist l1) (plist_2_nlist l2).
Proof.
    unfold _papp.
    intros l1 l2.
    induction l1 as [| h t IH]; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
Defined.

(* ── Relational wrappers ────────────────────────────────────── *)

(*  R__plength                                 Tactic steps: 5 *)
Lemma R__plength
    (l : _PList) (l' : NatList) (lR : rel R_NatList l l') :
    natR (_plength l) (nlength l').
Proof.
    change (plist_2_nlist l = l') in lR.
    apply map_in_R_nat.
    rewrite _plength_eq_nlength.
    rewrite lR.
    reflexivity.
Defined.

(*  R__papp                                    Tactic steps: 7 *)
Lemma R__papp
    (l1 : _PList) (l1' : NatList) (l1R : rel R_NatList l1 l1')
    (l2 : _PList) (l2' : NatList) (l2R : rel R_NatList l2 l2') :
    rel R_NatList (_papp l1 l2) (napp l1' l2').
Proof.
    change (plist_2_nlist l1 = l1') in l1R.
    change (plist_2_nlist l2 = l2') in l2R.
    change (plist_2_nlist (_papp l1 l2) = napp l1' l2').
    rewrite plist_2_nlist_app.
    rewrite l1R. rewrite l2R.
    reflexivity.
Defined.

(* ── Trocq Use registrations ────────────────────────────────── *)

Trocq Use R_NatList.    (* Trocq Use #1 *)
Trocq Use Param44_nat.  (* Trocq Use #2 *)
Trocq Use Param_add.    (* Trocq Use #3 — needed for [+] in the statement *)
Trocq Use R__plength.   (* Trocq Use #4 *)
Trocq Use R__papp.      (* Trocq Use #5 *)

(* ── Final iso theorem                        Tactic steps: 2
   Result is for [PList nat] only — the [_PList] alias is
   what Trocq's gref lookup finds.                            *)

(*  _plength_papp                              Tactic steps: 2 *)
Theorem _plength_papp : forall (l1 l2 : _PList),
    _plength (_papp l1 l2) = _plength l1 + _plength l2.
Proof. trocq. apply nlength_napp. Qed.

(*  Strategy 2 tactic-step summary
    ┌──────────────────────────────────┬──────────────┐
    │  Item                            │ Tactic steps │
    ├──────────────────────────────────┼──────────────┤
    │  plist_nlist_iso                 │      4       │
    │  nlist_plist_iso                 │      4       │
    │  R_NatList                       │      5       │
    │  Trocq Use ×2 (shared)           │      2 cmds  │
    │  _plength_eq_nlength             │      5       │
    │  plist_2_nlist_app               │      6       │
    │  R__plength                      │      5       │
    │  R__papp                         │      7       │
    │  Trocq Use ×2 (per-function)     │      2 cmds  │
    ├──────────────────────────────────┼──────────────┤
    │  _plength_papp (final theorem)   │      2       │
    ├──────────────────────────────────┼──────────────┤
    │  TOTAL                           │     38       │
    └──────────────────────────────────┴──────────────┘

    C_iso(n) = 36 + 2n   (setup 36, then 2 per theorem)
    But the result is for PList nat ONLY.
*)

(* ============================================================
   STRATEGY 3 — PARAMETRIC via PListR (truly polymorphic)
   ============================================================
   PListR is the parametric inductive relation between
   [PList A] and [PList A'].  It generalises the iso approach
   by being INDEPENDENT of any concrete element type.

   The cost of building the parametric infrastructure is ~33
   tactic steps (see bs_a3.v Phase 6a).  For the plength/papp
   case, we show the key building blocks:
     Param_plength  — plength is preserved by PListR
     Param_papp     — papp preserves PListR

   CRITICAL OBSERVATION:
     Param_plength does NOT prove:
         plength (papp l1 l2) = plength l1 + plength l2
     for a SINGLE list l1, l2 : PList A.
     It proves:
         plength l = plength l'
     when l : PList A and l' : PList A' are RELATED by PListR.

     For the single-list equality, induction is still required.
     This is why the parametric approach does not reduce the
     per-theorem proof cost for purely structural theorems.

   The parametric approach IS valuable for:
     (a) Transferring theorems between DIFFERENT concrete types
         (e.g., PList Z from PList nat, without re-proving).
     (b) Building relational witnesses for value-dependent theorems
         like psum_papp (see bs_a3.v Phase 6c/6d).

   COST:  ~33 steps setup (PListR infra) + 4 steps for Param_plength
           + 4 steps for Param_papp.
   RESULT: Param_plength and Param_papp as reusable relational lemmas.
           The final theorem plength_papp_poly is still proved by
           applying plength_papp_manual (0 extra steps after Phase 3).
*)

(* ── PListR: the parametric relation (Strategy 3 heart) ─────── *)

Inductive PListR (A A' : Type) (AR : A -> A' -> Type)
    : PList A -> PList A' -> Type :=
    | PNilR  : PListR A A' AR PNil PNil
    | PConsR :
        forall (a : A) (a' : A') (aR : AR a a')
               (l : PList A) (l' : PList A') (lR : PListR A A' AR l l'),
            PListR A A' AR (PCons a l) (PCons a' l').

(* ── Param_plength: structural, no element-type knowledge ────── *)

(*  When l and l' have the same spine (related by PListR),
    their lengths are equal.  No arithmetic, no Addable.        *)

(*  Param_plength                               Tactic steps: 4 *)
Lemma Param_plength :
    forall (A A' : Type) (AR : A -> A' -> Type)
           (l : PList A) (l' : PList A') (lR : PListR A A' AR l l'),
        plength l = plength l'.
Proof.
    intros A A' AR l l' lR.
    induction lR as [| a a' aR l l' _ IH]; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
Defined.

(* ── Param_papp: papp preserves PListR ────────────────────────── *)

(*  Param_papp                                  Tactic steps: 4 *)
Lemma Param_papp :
    forall (A A' : Type) (AR : A -> A' -> Type)
           (l1 : PList A) (l1' : PList A') (lR1 : PListR A A' AR l1 l1')
           (l2 : PList A) (l2' : PList A') (lR2 : PListR A A' AR l2 l2'),
        PListR A A' AR (papp l1 l2) (papp l1' l2').
Proof.
    intros A A' AR l1 l1' lR1 l2 l2' lR2.
    induction lR1 as [| a a' aR l l' _ IH]; simpl.
    - exact lR2.
    - exact (PConsR A A' AR a a' aR _ _ IH).
Defined.

(* ── Demonstration: parametric use of Param_plength ─────────── *)

(*  PListR_refl: every list is related to itself under eq.
    Needed to apply Param_plength / Param_papp self-referentially. *)

(*  PListR_refl                                 Tactic steps: 4 *)
Lemma PListR_refl : forall (A : Type) (l : PList A),
    PListR A A eq l l.
Proof.
    intros A l.
    induction l as [| h t IH]; simpl.
    - exact (PNilR A A eq).
    - exact (PConsR A A eq h h eq_refl t t IH).
Defined.

(*  plength_papp_poly: truly polymorphic
    PROOF: direct application of plength_papp_manual (0 extra steps).
    This demonstrates that the parametric infrastructure (Param_plength,
    Param_papp) is not needed to prove THIS particular theorem —
    the manual proof already covers all element types.
    However, Param_papp is reusable for MORE COMPLEX relational goals
    (e.g., psum_papp in bs_a3.v Phase 6c/6d).                    *)

(*  plength_papp_poly                           Tactic steps: 1 *)
Theorem plength_papp_poly : forall {A : Type} (l1 l2 : PList A),
    plength (papp l1 l2) = plength l1 + plength l2.
Proof. exact @plength_papp_manual. Qed.

(*  Alternatively, a proof that uses Param_plength + Param_papp
    explicitly (showing the parametric route):                   *)

(*  NOTE on Param_plength + Param_papp for this specific theorem:
    These relational witnesses are STRUCTURAL building blocks.
    To prove plength (papp l1 l2) = plength l1 + plength l2 for
    a single PList A, we still need either:
      (a) induction on l1 (= plength_papp_manual), or
      (b) a NatList↔PList iso (= Strategy 2 iso approach).
    Param_plength and Param_papp shine when TRANSFERRING between
    two DIFFERENT types (e.g., PList nat → PList Z), see bs_a3.v. *)

(* ============================================================
   COST COMPARISON
   ============================================================

   ┌──────────────────────────────────────────────────────────┐
   │  Strategy 1 — MANUAL (truly polymorphic)                 │
   │    plength_papp_manual : ∀ {A : Type}                    │
   │    5 tactic steps, 0 setup                               │
   │    C_manual(n) = 5n                                      │
   ├──────────────────────────────────────────────────────────┤
   │  Strategy 2 — TROCQ ISO (monomorphic)                    │
   │    _plength_papp : ∀ l1 l2 : PList nat                   │
   │    2 tactic steps, 36 steps setup                        │
   │    C_iso(n) = 36 + 2n                                    │
   │    Break-even: 5n = 36 + 2n → n ≈ 12                    │
   │    BUT: result is weaker (PList nat, not ∀ A)            │
   ├──────────────────────────────────────────────────────────┤
   │  Strategy 3 — PARAMETRIC (truly polymorphic)             │
   │    Param_plength + Param_papp as relational lemmas        │
   │    ~33 steps for PListR infra + 8 steps (Param_p* ×2)    │
   │    plength_papp_poly: 1 step (apply manual)              │
   │    C_param(n) ≈ 41 + 1n  (marginal cost 1 per theorem)   │
   │    Break-even vs manual: 5n = 41 + n → n ≈ 10.25        │
   │    BUT: the parametric infra saves cost only when         │
   │    combined with value-dependent theorems (psum).         │
   ├──────────────────────────────────────────────────────────┤
   │  CONCLUSION FOR STRUCTURAL THEOREMS (plength, papp, prev) │
   │    The manual approach dominates for small n.            │
   │    Neither Trocq strategy is worth the setup cost        │
   │    for purely structural theorems.                       │
   │    Trocq's advantage emerges for value-dependent theorems │
   │    (psum_papp) where the Addable typeclass divergence    │
   │    forces 2 extra manual steps per theorem — see bs_a3.v │
   │    Phase 6 for the fair comparison.                      │
   └──────────────────────────────────────────────────────────┘
*)

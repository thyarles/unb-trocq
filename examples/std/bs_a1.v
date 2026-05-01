(*  Trocq  ROI Experiment

    Phase 1  Definitions + NatList base theorems   (source of truth)
    Phase 2  PList proofs by pure copy-paste       (no bijections)
    Phase 3  Trocq transfer                        (the full overhead)

    Counting convention used throughout:
      - One period-terminated tactic    = 1 step
      - Compound  [t1; t2.]             = 1 step
      - Bullet markers                  = 0 steps
      - [Trocq Use] commands            = counted separately (not tactics)   
*)

From Stdlib Require Import ssreflect.
From Stdlib Require Import Lia.
From Trocq Require Import Trocq.
From Trocq Require Import Param_nat.
Local Open Scope nat_scope.
Set Universe Polymorphism.

(* ============================================================
   PHASE 1 -- Definitions and NatList Base Theorems
   ============================================================
   NatList (monomorphic) and PList (polymorphic, used at nat).
   Operations length / app / rev for both types.
   Base theorems proved for NatList ONLY; Phase 2 copies them.
*)

(* ── NatList: type and operations ─────────────────────────── *)

Inductive NatList : Type :=
    | NNil  : NatList
    | NCons : nat -> NatList -> NatList.
Notation "x :n: l" := (NCons x l) (at level 60, right associativity).
Notation "[[]]"    := NNil.

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

Fixpoint nrev (l : NatList) : NatList :=
    match l with
    | NNil       => NNil
    | NCons h t  => napp (nrev t) (NCons h NNil)
    end.

(* ── PList: type and operations (monomorphic: PList nat) ───── *)

Inductive PList (A : Type) : Type :=
    | PNil  : PList A
    | PCons : A -> PList A -> PList A.
Arguments PNil  {A}.
Arguments PCons {A} _ _.
Notation "x :p: l" := (PCons x l) (at level 60, right associativity).
Notation "{{}}"    := PNil.

(*  DESIGN CHOICE: plength / papp / prev are stated for [PList nat],
    not [PList A].  This is what makes Phase 2 possible: every proof
    is tactic-identical to its NatList counterpart. 
*)

Fixpoint plength (l : PList nat) : nat :=
    match l with
    | PNil       => O
    | PCons _ t  => S (plength t)
    end.

Fixpoint papp (l1 l2 : PList nat) : PList nat :=
    match l1 with
    | PNil       => l2
    | PCons h t  => PCons h (papp t l2)
    end.

Fixpoint prev (l : PList nat) : PList nat :=
    match l with
    | PNil       => PNil
    | PCons h t  => papp (prev t) (PCons h PNil)
    end.

(* ── Auxiliary: napp l NNil = l  (needed by nrev_napp) ─────── *)

(*  napp_nil_r                                  Tactic steps: 4 *)
Lemma napp_nil_r : forall l : NatList, napp l NNil = l.
Proof.
    induction l as [| h t IH]; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
Defined.

(* ── Base theorems (NatList only) ──────────────────────────── *)

(*  nlength_napp                                Tactic steps: 5 *)
Theorem nlength_napp : forall (l1 l2 : NatList),
    nlength (napp l1 l2) = nlength l1 + nlength l2.
    (* len(l1 ++ l2) = len l1 + len l2 *)
Proof.
    intros l1 l2.
    induction l1 as [| h t IH]; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
Defined.

(*  napp_assoc                                  Tactic steps: 5 *)
Theorem napp_assoc : forall (l1 l2 l3 : NatList),
    napp (napp l1 l2) l3 = napp l1 (napp l2 l3).
    (* (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3) *)
Proof.
    intros l1 l2 l3.
    induction l1 as [| h t IH]; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
Defined.

(*  nrev_napp                                   Tactic steps: 7 *)
Theorem nrev_napp : forall (l1 l2 : NatList),
    nrev (napp l1 l2) = napp (nrev l2) (nrev l1).
    (* rev(l1 ++ l2) = rev l2 ++ rev l1 *)
Proof.
    intros l1 l2.
    induction l1 as [| h t IH]; simpl.
    - symmetry. apply napp_nil_r.
    - rewrite IH. rewrite napp_assoc. reflexivity.
Defined.

(*  Phase 1 tactic-step summary
    ┌──────────────────────┬──────────────┐
    │ Lemma / Theorem      │ Tactic steps │
    ├──────────────────────┼──────────────┤
    │ napp_nil_r  (aux)    │      4       │
    │ nlength_napp         │      5       │
    │ napp_assoc           │      5       │
    │ nrev_napp            │      7       │
    ├──────────────────────┼──────────────┤
    │ TOTAL (NatList)      │     21       │
    └──────────────────────┴──────────────┘
*)

(* ============================================================
   PHASE 2 -- The "Normal Human" Manual Transfer (Copy-Paste)
   ============================================================
   Each proof below is a LITERAL rename of the Phase 1 NatList
   proof.  The only changes are:

     NatList  -->  PList nat
     NNil     -->  PNil
     NCons    -->  PCons
     napp     -->  papp
     nlength  -->  plength
     nrev     -->  prev
     [[]]     -->  {{}}

   NO bijections.  NO bridge lemmas.  NO conversion functions.
   Just Ctrl+C, Ctrl+V, and a find-and-replace.
*)

(* ── Auxiliary (from napp_nil_r) ───────────────────────────── *)

(*  papp_nil_r                                  Tactic steps: 4 *)
Lemma papp_nil_r : forall l : PList nat, papp l PNil = l.
    (* papp l PNil = l *)
Proof.
    induction l as [| h t IH]; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
Defined.

(* ── Copy-paste theorems (PList nat) ───────────────────────── *)

(*  plength_papp_manual                         Tactic steps: 5 *)
Theorem plength_papp_manual : forall (l1 l2 : PList nat),
    plength (papp l1 l2) = plength l1 + plength l2.
    (* from nlength_napp; NatList renamed to PList nat. *)
Proof.
    intros l1 l2.
    induction l1 as [| h t IH]; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
Defined.

(*  papp_assoc_manual                           Tactic steps: 5 *)
Theorem papp_assoc_manual : forall (l1 l2 l3 : PList nat),
    papp (papp l1 l2) l3 = papp l1 (papp l2 l3).
    (* from napp_assoc; NatList renamed to PList nat. *)
Proof.
    intros l1 l2 l3.
    induction l1 as [| h t IH]; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
Defined.

(*  prev_papp_manual                            Tactic steps: 7 *)
Theorem prev_papp_manual : forall (l1 l2 : PList nat),
    prev (papp l1 l2) = papp (prev l2) (prev l1).
    (* from nrev_napp; NatList renamed to PList nat.
        napp_nil_r   -->  papp_nil_r
        napp_assoc   -->  papp_assoc_manual *)
Proof.
    intros l1 l2.
    induction l1 as [| h t IH]; simpl.
    - symmetry. apply papp_nil_r.
    - rewrite IH. rewrite papp_assoc_manual. reflexivity.
Defined.

(*  Phase 2 tactic-step summary
    ┌──────────────────────────────┬──────────────┐
    │ Lemma / Theorem              │ Tactic steps │
    ├──────────────────────────────┼──────────────┤
    │ papp_nil_r   (aux)           │      4       │
    │ plength_papp_manual          │      5       │
    │ papp_assoc_manual            │      5       │
    │ prev_papp_manual             │      7       │
    ├──────────────────────────────┼──────────────┤
    │ TOTAL (3 theorems + 1 aux)   │     21       │
    ├──────────────────────────────┼──────────────┤
    │ SETUP COST                   │      0       │
    └──────────────────────────────┴──────────────┘

    P_paste (avg per theorem, 3 theorems)  = (5 + 5 + 7) / 3 ≈ 5.67

    C_manual(n) = n * P_paste  ≈  5.67 * n

    There is no fixed setup cost.  Every new theorem just requires
    a copy-paste of the corresponding NatList proof.
*)

(* ============================================================
   PHASE 3 -- The Trocq Transfer
   ============================================================
   We now prove the same three theorems via Trocq. This requires
   writing ALL of the infrastructure that the copy-paste approach
   skips:

     1. Monomorphic aliases (required by Trocq's gref lookup)
     2. Forward / backward conversion functions
     3. Mutual-inverse proofs (isomorphism)
     4. R_NatList      — the type-level parametric relation
     5. Bridge lemmas  — commutativity with each operation
     6. R__f lemmas    — function-level parametric relations
     7. Trocq Use registrations

   Only THEN can each theorem be proved in 2 tactic steps.
*)

(* ── Monomorphic aliases  ───────────────────────────────────── *)

(*  Trocq's internal database is keyed on the head global reference
    (gref) of each term. Writing [_papp l1 l2] gives head gref
    [_papp]; writing [@papp nat l1 l2] gives head gref [papp] and
    would miss the registered witness. Since our plength / papp /
    prev are already monomorphic (no implicit A), the aliases just
    rename them — but the aliased names are what we use in theorems
    so that Trocq's lookup always finds the right witness.
*)

Definition _PList   : Type                       := PList nat.
Definition _PNil    : _PList                     := @PNil nat.
Definition _PCons   : nat -> _PList -> _PList    := @PCons nat.
Definition _plength : _PList -> nat              := plength.
Definition _papp    : _PList -> _PList -> _PList := papp.
Definition _prev    : _PList -> _PList           := prev.

(* ── Conversion functions (no tactic steps — fixpoint defs) ─── *)

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

(* ── Mutual inverses  ──────────────────────────────────────────
   These prove the two functions form a bijection (isomorphism).
*)

(*  plist_nlist_iso                              Tactic steps: 4 *)
Lemma plist_nlist_iso : forall (l : _PList),
    nlist_2_plist (plist_2_nlist l) = l.
Proof.
    induction l as [| h t IH]; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
Defined.

(*  nlist_plist_iso                              Tactic steps: 4 *)
Lemma nlist_plist_iso : forall (l : NatList),
    plist_2_nlist (nlist_2_plist l) = l.
Proof.
    induction l as [| h t IH]; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
Defined.

(* ── Type-level parametric relation  ──────────────────────────
   R_NatList packs the isomorphism into a Param44.Rel, which is
   the 'dictionary' Trocq uses to rewrite the type in the goal.
*)

(*  R_NatList                                   Tactic steps: 5 *)
Definition R_NatList : Param44.Rel _PList NatList.
Proof.
    apply Iso.toParam; unshelve econstructor.
    - exact plist_2_nlist.    (* map:   _PList  -> NatList *)
    - exact nlist_2_plist.    (* comap: NatList -> _PList  *)
    - exact plist_nlist_iso.  (* mapK:  comap . map = id   *)
    - exact nlist_plist_iso.  (* comapK: map . comap = id  *)
Defined.

(* ── Shared registrations  ─────────────────────────────────────
   Trocq Use commands are not tactic steps, but are required once.
*)

Trocq Use R_NatList.     (* Trocq Use #1 *)
Trocq Use Param44_nat.   (* Trocq Use #2 *)
Trocq Use Param_add.     (* Trocq Use #3 *)

(* ── Bridge lemmas  ─────────────────────────────────────────────
   Each bridge lemma states that the forward conversion function
   commutes with the corresponding PList operation.
*)

(*  _plength_eq_nlength                         Tactic steps: 5 *)
Lemma _plength_eq_nlength : forall (l : _PList),
    _plength l = nlength (plist_2_nlist l).
Proof.
    unfold _plength.
    induction l as [| h t IH]; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
Defined.

(*  plist_2_nlist_app                           Tactic steps: 6 *)
Lemma plist_2_nlist_app : forall (l1 l2 : _PList),
    plist_2_nlist (_papp l1 l2) = napp (plist_2_nlist l1) (plist_2_nlist l2).
Proof.
    unfold _papp.
    intros l1 l2.
    induction l1 as [| h t IH]; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
Defined.

(*  plist_2_nlist_rev                           Tactic steps: 6 *)
Lemma plist_2_nlist_rev : forall (l : _PList),
    plist_2_nlist (_prev l) = nrev (plist_2_nlist l).
Proof.
    induction l as [| h t IH]; simpl.
    - reflexivity.
    - rewrite plist_2_nlist_app. simpl. rewrite IH. reflexivity.
Defined.

(* ── Function-level parametric relations (R__ wrappers)  ────────
   Each R__ lemma witnesses that the PList and NatList operations
   are compatible under R_NatList.  Pattern:
     if l ~ l'  (i.e. plist_2_nlist l = l')  then  f l ~ g l'.
*)

(*  R__plength                                  Tactic steps: 5 *)
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

(*  R__papp                                     Tactic steps: 7 *)
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

(*  R__prev                                     Tactic steps: 5 *)
Lemma R__prev
    (l : _PList) (l' : NatList) (lR : rel R_NatList l l') :
    rel R_NatList (_prev l) (nrev l').
Proof.
    change (plist_2_nlist l = l') in lR.
    change (plist_2_nlist (_prev l) = nrev l').
    rewrite plist_2_nlist_rev.
    rewrite lR.
    reflexivity.
Defined.

(* ── Per-function registrations  ───────────────────────────────
   Each registration makes the R__ witness visible to the trocq
   tactic during goal rewriting.
*)

Trocq Use R__plength.   (* Trocq Use #4 *)
Trocq Use R__papp.      (* Trocq Use #5 *)
Trocq Use R__prev.      (* Trocq Use #6 *)

(* ── Trocq theorems  ────────────────────────────────────────────
   After all the infrastructure above, each theorem costs exactly
   2 tactic steps: [trocq.] rewrites the goal to its NatList form;
   [apply <natlist_thm>] closes it immediately.
*)

(*  _plength_papp                               Tactic steps: 2 *)
Theorem _plength_papp : forall (l1 l2 : _PList),
    _plength (_papp l1 l2) = _plength l1 + _plength l2.
Proof. trocq. apply nlength_napp. Qed.

(*  _papp_assoc                                 Tactic steps: 2 *)
Theorem _papp_assoc : forall (l1 l2 l3 : _PList),
    _papp (_papp l1 l2) l3 = _papp l1 (_papp l2 l3).
Proof. trocq. apply napp_assoc. Qed.

(*  _prev_papp                                  Tactic steps: 2 *)
Theorem _prev_papp : forall (l1 l2 : _PList),
    _prev (_papp l1 l2) = _papp (_prev l2) (_prev l1).
Proof. trocq. apply nrev_napp. Qed.

(*  Phase 3 tactic-step summary
    ┌──────────────────────────────────────────┬──────────────┐
    │  Item                                    │ Tactic steps │
    ├──────────────────────────────────────────┼──────────────┤
    │  S_bij (isos + R_NatList)                │              │
    │    plist_nlist_iso                       │      4       │
    │    nlist_plist_iso                       │      4       │
    │    R_NatList (Iso.toParam)               │      5       │
    │    Trocq Use ×3 (shared)                 │      3 cmds  │
    │    S_bij subtotal                        │     13       │
    ├──────────────────────────────────────────┼──────────────┤
    │  Per function (f = 3)                    │              │
    │    plength: bridge(5) + R__(5) + Use(1)  │     11       │
    │    papp:    bridge(6) + R__(7) + Use(1)  │     14       │
    │    prev:    bridge(6) + R__(5) + Use(1)  │     12       │
    │    Per-function subtotal                 │     37       │
    ├──────────────────────────────────────────┼──────────────┤
    │  Per theorem ×3                          │      6       │
    ├──────────────────────────────────────────┼──────────────┤
    │  TOTAL (Trocq setup + theorems)          │     56       │
    │  SETUP ONLY (without per-theorem)        │     50       │
    └──────────────────────────────────────────┴──────────────┘

    (Trocq Use commands counted as 1 step each above.)

    For ROI:  S_setup = 50 (one-time),  n * 2 (per theorem)
    C_trocq(n) = 50 + 2n
*)

(* ============================================================
   PHASE 4 -- New ROI Formulas and Break-Even Point
   ============================================================
   We now have all the concrete numbers from Phases 2 and 3.
   This section derives the cost formulas, fixes the formulas
   from the prompt where needed, and calculates the new n*.

   KEY INSIGHT: the "normal human" copy-paste baseline has
   ZERO fixed cost. This fundamentally changes the economics.

   ── Concrete counts ──────────────────────────────────────────

   Phase 2  (Manual  -- Ctrl+C / Ctrl+V)
     papp_nil_r        (auxiliary)  :  4 tactic steps
     plength_papp_manual            :  5 tactic steps
     papp_assoc_manual              :  5 tactic steps
     prev_papp_manual               :  7 tactic steps
     Fixed setup cost               :  0
     P_paste  (avg per theorem)     :  (5 + 5 + 7) / 3  =  17/3  ≈ 5.67

   Phase 3  (Trocq)
     S_bij  (isos + R_NatList + 3 shared Trocq Use)  :  13 tactic steps
     f * (S_bridge + W_trocq)  with f = 3            :  37 tactic steps
       plength: 5 + 6  =  11
       papp:    6 + 8  =  14
       prev:    6 + 6  =  12
     S_setup  = S_bij + f*(S_bridge + W_trocq)        :  50
     Per-theorem cost                                 :   2 (trocq. apply)

   ── The Cost Formulas ────────────────────────────────────────

   The prompt's formulas are CORRECT in structure.
   Plugging in our numbers:

     C_manual(n)  =  n * P_paste
                  =  (17/3) * n
                  ≈  5.67 * n

     C_trocq(n)   =  S_bij  +  f * (S_bridge + W_trocq)  +  n * 2
                  =  13     +  37                        +  n * 2
                  =  50 + 2n

   NOTE: the prompt writes W_trocq for the per-function Trocq cost.
   In our counting W_trocq_i includes: R__f lemma tactics + 1 Trocq Use.
   Values: W_trocq(plength)=6, W_trocq(papp)=8, W_trocq(prev)=6.
   Since functions differ, the formula is exact as a sum:
     f * (S_bridge + W_trocq)  means  sum_{i=1}^{f} (S_bridge_i + W_trocq_i).

   ── Break-Even Point ─────────────────────────────────────────

   Set C_manual(n) = C_trocq(n) and solve for n:

     (17/3) * n  =  50  +  2n
     (17/3 - 6/3) * n  =  50
     (11/3) * n  =  50
     n*  =  150 / 11  ≈  13.6

   Trocq becomes cheaper only from n >= 14 theorems.

   COMPARE with previous results:
     Fourth Try  (manual = bijection-based):  n*  ≈  1.2
     Fifth Try   (manual = copy-paste):       n*  ≈  13.6

   The break-even increased by a factor of ~11.  The copy-paste
   baseline is so cheap that Trocq must amortise its 50-step
   setup across at least 14 theorems before it pays off.

   ── ROI Formula ──────────────────────────────────────────────

     ROI(n) =  (C_manual - C_trocq) / C_trocq
            =  ((17/3)*n  -  50  -  2n) / (50 + 2n)
            =  ((11/3)*n  -  50)        / (50 + 2n)

   Long-run asymptote (n -> infinity):

     ROI_inf =  (P_paste - 2) / 2
             =  (17/3 - 2)   / 2
             =  (11/3)       / 2
             =  11/6  ≈  1.83

   Even at n = infinity, Trocq only saves 1.83x its own cost,
   because the manual proof per theorem.
 
   ── Formula correction ───────────────────────────────────────

   The prompt writes:
     C_trocq = S_bijections + f * (S_bridge + W_trocq) + n * 2

   One clarification:
     S_bijections  must include the shared Trocq Use registrations
     (R_NatList, Param44_nat, Param_add), not just the tactic proofs.
   In our numbers S_bij = 13 already includes those 3 commands,
   so the formula as written is consistent with our counts.

   ── Summary ──────────────────────────────────────────────────

   ┌─────────────────────────────────────────────────────────┐
   │  C_manual(n)   =   5.67 * n          (no setup cost)    │
   │  C_trocq(n)    =   50 + 2n           (heavy setup)      │
   │  n*            =   150/11  ≈  13.6                      │
   │  ROI_inf       =   11/6    ≈  1.83x                     │
   │                                                         │
   │  Trocq wins only when transferring >= 14 theorems       │
   │  for the same (NatList, PList nat) vocabulary.          │
   └─────────────────────────────────────────────────────────┘ 
*)

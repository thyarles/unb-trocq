From Stdlib Require Import ssreflect.
Local Open Scope nat_scope.
From Trocq Require Import Trocq.
From Trocq Require Import Param_nat.

Set Universe Polymorphism.

(*  ── PList definitions ─────────────────────────────────────────────── *)

Require Import Trocq_examples.bs_p2.

(*  ── Base definitions ──────────────────────────────────────────────── *)

Inductive BolList : Type :=
    | BNil  : BolList
    | BCons : bool -> BolList -> BolList.
Notation "x :b: l" := (BCons x l) (at level 60, right associativity).
Notation "[bb]"    := BNil.

Fixpoint blength (l : BolList) : nat :=
    match l with
    | BNil       => O
    | BCons _ t  => S (blength t)
    end.

Fixpoint bapp (l1 l2 : BolList) : BolList :=
    match l1 with
    | BNil       => l2
    | BCons h t  => BCons h (bapp t l2)
    end.

(* Monomorphic aliases for PList bool avoids Trocq confusing the implicit
   sort argument with a list variable. *)
Definition NBPList   : Type                          := PList bool.
Definition nbPNil    : NBPList                       := @PNil bool.
Definition nbPCons   : bool -> NBPList -> NBPList    := @PCons bool.
Definition nbplength : NBPList -> nat                := @plength bool.
Definition nbpapp    : NBPList -> NBPList -> NBPList := @papp bool.

(*  ── Conversion functions ──────────────────────────────────────────── *)

Fixpoint bollist_to_plist (l : BolList) : NBPList :=
    match l with
    | BNil      => nbPNil
    | BCons h t => nbPCons h (bollist_to_plist t)
    end.

Fixpoint plist_to_bollist (l : NBPList) : BolList :=
    match l with
    | @PNil _      => BNil
    | @PCons _ h t => BCons h (plist_to_bollist t)
    end.

(*  ── Bridge lemmas  ───────────────────────────────────────────────── *)

Lemma blength_eq_nbplength : forall (l : BolList),
    nbplength (bollist_to_plist l) = blength l.
Proof.
    unfold nbplength.
    induction l; simpl.
    - reflexivity.
    - rewrite IHl. reflexivity.
Defined.

Lemma bollist_to_plist_app :
    forall (l1 l2 : BolList),
    bollist_to_plist (bapp l1 l2) =
    nbpapp (bollist_to_plist l1) (bollist_to_plist l2).
Proof.
    unfold nbpapp.
    intros l1 l2.
    induction l1; simpl.
    - reflexivity.
    - rewrite IHl1. reflexivity.
Defined.

(*  ── Mutual inverses ──────────────────────────────────────────────── *)

Lemma bollist_plist_iso :
    forall (l : BolList),
    plist_to_bollist (bollist_to_plist l) = l.
Proof.
    induction l; simpl.
    - reflexivity.
    - rewrite IHl. reflexivity.
Defined.

Lemma plist_bollist_iso :
    forall (l : NBPList),
    bollist_to_plist (plist_to_bollist l) = l.
Proof.
    induction l; simpl.
    - unfold nbPNil. reflexivity.
    - rewrite IHl. unfold nbPCons. reflexivity.
Defined.

(*  ── Relation between the types ───────────────────────────────────── *)

Definition R_BolList : Param44.Rel BolList NBPList.
Proof.
    apply Iso.toParam; unshelve econstructor.
    - apply bollist_to_plist.   (* map   : BolList     → PList bool *)
    - apply plist_to_bollist.   (* comap : PList bool  → BolList    *)
    - apply bollist_plist_iso.  (* mapK  : comap ∘ map = id         *)
    - apply plist_bollist_iso.  (* comapK: map ∘ comap = id         *)
Defined.

(*  ── Relation between the functions ───────────────────────────────── *)

Definition R_blength
    (l : BolList) (l' : NBPList) (lR : rel R_BolList l l') :
    natR (blength l) (nbplength l') :=
    map_in_R_nat
        (eq_trans (eq_sym (blength_eq_nbplength l)) (ap nbplength lR)).

Definition R_bapp
    (l1 : BolList) (l1' : NBPList) (l1R : rel R_BolList l1 l1')
    (l2 : BolList) (l2' : NBPList) (l2R : rel R_BolList l2 l2') :
    rel R_BolList (bapp l1 l2) (nbpapp l1' l2') :=
    eq_trans
        (bollist_to_plist_app l1 l2)
        (eq_trans
            (ap (fun x => nbpapp x (bollist_to_plist l2)) l1R)
            (ap (nbpapp l1') l2R)).

(*  ── Register in Trocq's database ─────────────────────────────────── *)

Trocq Use R_BolList.        (* relation between the types *)
Trocq Use R_blength.        (* relation between the functions *)
Trocq Use R_bapp.           (* relation between the functions *)

Trocq Use Param44_nat.      (* from Trocq *)
Trocq Use Param_add.        (* from Trocq *)

(*  ── The theorem via Trocq ────────────────────────────────────────── *)
Theorem blength_bapp_trocq : forall (l1 l2 : BolList),
    blength (bapp l1 l2) = blength l1 + blength l2.
Proof.
    trocq.
    apply plength_papp.
Qed.

(* Notes:
    Param01_paths
        From Trocq Require Import Trocq` already executes:
            Trocq Use Param10_paths.
            Trocq Use Param01_paths.
        It's globally pre-registered. You never needed to
        add it yourself.
    Param44_Bool
        [bool] never appears in the theorem statement:
        [BolList] is treated by Trocq as an atomic type
        translated wholesale via [R_BolList].
        The element type [bool] is hidden inside the
        isomorphism and never surfaces in the goal.
        Trocq only needs the relation for types/values
        that appear in the goal being translated.
    [R_BNil], [R_BCons]
        The constructors [BNil] and [BCons] do not
        appear in the goal. Trocq only needs constructor
        relations when the goal mentions those constructors
        directly or when Trocq itself needs to perform case
        analysis. Here, `trocq` just translates the type
        [BolList → NBPList], replaces [blength]/[bapp]
        using [R_blength]/[R_bapp], and hands off to [apply
        plength_papp]. The constructors are never consulted. *)
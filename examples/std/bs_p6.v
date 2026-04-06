From Stdlib Require Import ssreflect.
Local Open Scope nat_scope.
From Trocq Require Import Trocq.
From Trocq Require Import Param_nat.

Set Universe Polymorphism.

(*  ── NatList definitions (source – theorem to transfer) ────────────── *)

Require Import Trocq_examples.bs_p1.

(*  ── PList nat definitions (target – type to prove) ────────────────── *)

Require Import Trocq_examples.bs_p2.

(* Monomorphic aliases for PList nat avoids Trocq confusing the implicit
   sort argument with a list variable. *)
Definition NPNatList   : Type                                := PList nat.
Definition npPNil      : NPNatList                           := @PNil nat.
Definition npPCons     : nat -> NPNatList -> NPNatList       := @PCons nat.
Definition npnlength   : NPNatList -> nat                    := @plength nat.
Definition npnapp      : NPNatList -> NPNatList -> NPNatList := @papp nat.

(*  ── Conversion functions ──────────────────────────────────────────── *)

Fixpoint plist_to_natlist (l : NPNatList) : NatList :=
    match l with
    | @PNil _      => NNil
    | @PCons _ h t => NCons h (plist_to_natlist t)
    end.

Fixpoint natlist_to_plist (l : NatList) : NPNatList :=
    match l with
    | NNil      => npPNil
    | NCons h t => npPCons h (natlist_to_plist t)
    end.

(*  ── Bridge lemmas  ────────────────────────────────────────────────── *)

Lemma npnlength_eq_nlength :
    forall (l : NPNatList),
    npnlength l = nlength (plist_to_natlist l).
Proof.
    unfold npnlength.
    induction l; simpl.
    - reflexivity.
    - rewrite IHl. reflexivity.
Defined.

Lemma plist_to_natlist_app :
    forall (l1 l2 : NPNatList),
    plist_to_natlist (npnapp l1 l2) =
    napp (plist_to_natlist l1) (plist_to_natlist l2).
Proof.
    unfold npnapp.
    intros l1 l2.
    induction l1; simpl.
    - reflexivity.
    - rewrite IHl1. reflexivity.
Defined.

(*  ── Mutual inverses ───────────────────────────────────────────────── *)

Lemma plist_natlist_iso :
    forall (l : NPNatList),
    natlist_to_plist (plist_to_natlist l) = l.
Proof.
    induction l; simpl.
    - unfold npPNil. reflexivity.
    - rewrite IHl. unfold npPCons. reflexivity.
Defined.

Lemma natlist_plist_iso :
    forall (l : NatList),
    plist_to_natlist (natlist_to_plist l) = l.
Proof.
    induction l; simpl.
    - reflexivity.
    - rewrite IHl. reflexivity.
Defined.

(*  ── Relation between the types ────────────────────────────────────── *)

Definition R_NatList : Param44.Rel NPNatList NatList.
Proof.
    apply Iso.toParam; unshelve econstructor.
    - apply plist_to_natlist.   (* map   : NPNatList → NatList    *)
    - apply natlist_to_plist.   (* comap : NatList   → NPNatList  *)
    - apply plist_natlist_iso.  (* mapK  : comap ∘ map = id       *)
    - apply natlist_plist_iso.  (* comapK: map ∘ comap = id       *)
Defined.

(*  ── Relation between the functions ────────────────────────────────── *)

Definition R_npnlength
    (l : NPNatList) (l' : NatList) (lR : rel R_NatList l l') :
    natR (npnlength l) (nlength l') :=
    map_in_R_nat
        (eq_trans (npnlength_eq_nlength l) (ap nlength lR)).

Definition R_npnapp
    (l1 : NPNatList) (l1' : NatList) (l1R : rel R_NatList l1 l1')
    (l2 : NPNatList) (l2' : NatList) (l2R : rel R_NatList l2 l2') :
    rel R_NatList (npnapp l1 l2) (napp l1' l2') :=
    eq_trans
        (plist_to_natlist_app l1 l2)
        (eq_trans
            (ap (fun x => napp x (plist_to_natlist l2)) l1R)
            (ap (napp l1') l2R)).

(*  ── Register in Trocq's database ──────────────────────────────────── *)

Trocq Use R_NatList.        (* relation between the types *)
Trocq Use R_npnlength.      (* relation between the functions *)
Trocq Use R_npnapp.         (* relation between the functions *)

Trocq Use Param44_nat.      (* from Trocq *)
Trocq Use Param_add.        (* from Trocq *)

(*  ── The theorem via Trocq ─────────────────────────────────────────── *)
Theorem npnlength_npnapp_trocq : forall (l1 l2 : NPNatList),
    npnlength (npnapp l1 l2) = npnlength l1 + npnlength l2.
Proof.
    trocq.
    apply nlength_napp.
Qed.
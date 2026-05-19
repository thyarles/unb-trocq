From Stdlib Require Import ssreflect.
From Stdlib Require Import Lia.
From Trocq Require Import Trocq.
From Trocq Require Import Param_nat.
Local Open Scope nat_scope.
Set Universe Polymorphism.

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

(*  nsum: sum of elements (new; not in bs_a1.v) *)
Fixpoint nsum (l : NatList) : nat :=
    match l with
    | NNil       => 0
    | NCons h t  => h + nsum t
    end.

(* ── PList: type and structural operations (truly polymorphic) *)

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

Fixpoint prev {A : Type} (l : PList A) : PList A :=
    match l with
    | PNil       => PNil
    | PCons h t  => papp (prev t) (PCons h PNil)
    end.

(* ── Auxiliary lemma ────────────────────────────────────────── *)

Lemma napp_nil_r : forall l : NatList, napp l NNil = l.
Proof.
    induction l as [| h t IH]; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
Defined.

(* ── Base theorems (NatList) ────────────────────────────────── *)

Theorem nlength_napp : forall (l1 l2 : NatList),
    nlength (napp l1 l2) = nlength l1 + nlength l2.
Proof.
    intros l1 l2.
    induction l1 as [| h t IH]; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
Defined.

Theorem napp_assoc : forall (l1 l2 l3 : NatList),
    napp (napp l1 l2) l3 = napp l1 (napp l2 l3).
Proof.
    intros l1 l2 l3.
    induction l1 as [| h t IH]; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
Defined.

Theorem nrev_napp : forall (l1 l2 : NatList),
    nrev (napp l1 l2) = napp (nrev l2) (nrev l1).
Proof.
    intros l1 l2.
    induction l1 as [| h t IH]; simpl.
    - symmetry. apply napp_nil_r.
    - rewrite IH. rewrite napp_assoc. reflexivity.
Defined.

Theorem nsum_napp : forall (l1 l2 : NatList),
    nsum (napp l1 l2) = nsum l1 + nsum l2.
Proof.
    intros l1 l2.
    induction l1 as [| h t IH]; simpl.
    - reflexivity.
    - rewrite IH. lia.
Defined.

Class Addable (A : Type) : Type := {
    add        : A -> A -> A;
    zero       : A;
    add_assoc  : forall x y z : A, add (add x y) z = add x (add y z);
    add_zero_l : forall x : A, add zero x = x;
    add_zero_r : forall x : A, add x zero = x
}.

Fixpoint psum {A : Type} {H : Addable A} (l : PList A) : A :=
    match l with
    | PNil       => zero
    | PCons h t  => add h (psum t)
    end.

(* ── Auxiliary (from napp_nil_r) ────────────────────────────── *)

Lemma papp_nil_r : forall {A : Type} (l : PList A), papp l PNil = l.
Proof.
    intros A.
    induction l as [| h t IH]; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
Defined.

(* ── Copy-paste theorems ────────────────────────────────────── *)

Theorem plength_papp_manual : forall {A : Type} (l1 l2 : PList A),
    plength (papp l1 l2) = plength l1 + plength l2.
Proof.
    intros A l1 l2.
    induction l1 as [| h t IH]; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
Defined.

Theorem papp_assoc_manual : forall {A : Type} (l1 l2 l3 : PList A),
    papp (papp l1 l2) l3 = papp l1 (papp l2 l3).
Proof.
    intros A l1 l2 l3.
    induction l1 as [| h t IH]; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
Defined.

Theorem prev_papp_manual : forall {A : Type} (l1 l2 : PList A),
    prev (papp l1 l2) = papp (prev l2) (prev l1).
Proof.
    intros A l1 l2.
    induction l1 as [| h t IH]; simpl.
    - symmetry. apply papp_nil_r.
    - rewrite IH. rewrite papp_assoc_manual. reflexivity.
Defined.

Theorem psum_papp_manual :
    forall {A : Type} {H : Addable A} (l1 l2 : PList A),
    psum (papp l1 l2) = add (psum l1) (psum l2).
Proof.
    intros A H l1 l2.
    induction l1 as [| h t IH]; simpl.
    - symmetry. apply add_zero_l.
      (* DIVERGENCE 1: was [reflexivity] in nsum_napp *)
    - rewrite IH. symmetry. apply add_assoc.
      (* DIVERGENCE 2: was [lia] *)
Defined.

Instance addableNat : Addable nat := {
    add        := Nat.add;
    zero       := 0;
    add_assoc  := ltac:(intros; lia);
    add_zero_l := ltac:(intros; lia);
    add_zero_r := ltac:(intros; lia)
}.

(* ── 2. Monomorphic aliases ─────────────────────────────────────*)

Definition _PList   : Type                       := PList nat.
Definition _PNil    : _PList                     := @PNil nat.
Definition _PCons   : nat -> _PList -> _PList    := @PCons nat.
Definition _plength : _PList -> nat              := @plength nat.
Definition _papp    : _PList -> _PList -> _PList := @papp nat.
Definition _prev    : _PList -> _PList           := @prev nat.
Definition _psum    : _PList -> nat              := @psum nat addableNat.

(* ── 3. Conversion functions ────────────────────────────────── *)

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

(* ── 4. Mutual-inverse proofs + R_NatList ───────────────────── *)

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

Definition R_NatList : Param44.Rel _PList NatList.
Proof.
    apply Iso.toParam; unshelve econstructor.
    - exact plist_2_nlist.
    - exact nlist_2_plist.
    - exact plist_nlist_iso.
    - exact nlist_plist_iso.
Defined.

(* ── 5. Shared Trocq Use registrations ─────────────────────── *)

Trocq Use R_NatList.     (* Trocq Use #1 *)
Trocq Use Param44_nat.   (* Trocq Use #2 *)
Trocq Use Param_add.     (* Trocq Use #3 *)

(* ── 6. Bridge lemmas ───────────────────────────────────────────*)

Lemma _plength_eq_nlength : forall (l : _PList),
    _plength l = nlength (plist_2_nlist l).
Proof.
    unfold _plength.
    induction l as [| h t IH]; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
Defined.

Lemma plist_2_nlist_app : forall (l1 l2 : _PList),
    plist_2_nlist (_papp l1 l2) = napp (plist_2_nlist l1) (plist_2_nlist l2).
Proof.
    unfold _papp.
    intros l1 l2.
    induction l1 as [| h t IH]; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
Defined.

Lemma plist_2_nlist_rev : forall (l : _PList),
    plist_2_nlist (_prev l) = nrev (plist_2_nlist l).
Proof.
    induction l as [| h t IH]; simpl.
    - reflexivity.
    - rewrite plist_2_nlist_app. simpl. rewrite IH. reflexivity.
Defined.

Lemma plist_2_nlist_sum : forall (l : _PList),
    _psum l = nsum (plist_2_nlist l).
Proof.
    unfold _psum.
    induction l as [| h t IH]; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
Defined.

(* ── R__ relational wrappers ────────────────────────────────── *)

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

Lemma R__psum
    (l : _PList) (l' : NatList) (lR : rel R_NatList l l') :
    natR (_psum l) (nsum l').
Proof.
    change (plist_2_nlist l = l') in lR.
    apply map_in_R_nat.
    rewrite plist_2_nlist_sum.
    rewrite lR.
    reflexivity.
Defined.

(* ── Per-function Trocq Use registrations ───────────────────── *)

Trocq Use R__plength.    (* Trocq Use #4 *)
Trocq Use R__papp.       (* Trocq Use #5 *)
Trocq Use R__prev.       (* Trocq Use #6 *)
Trocq Use R__psum.       (* Trocq Use #7  ← new vs bs_a1.v *)

(* ── Final Trocq theorems ───────────────────────────────────────*)

Theorem _plength_papp : forall (l1 l2 : _PList),
    _plength (_papp l1 l2) = _plength l1 + _plength l2.
Proof. trocq. apply nlength_napp. Qed.

Theorem _papp_assoc : forall (l1 l2 l3 : _PList),
    _papp (_papp l1 l2) l3 = _papp l1 (_papp l2 l3).
Proof. trocq. apply napp_assoc. Qed.

Theorem _prev_papp : forall (l1 l2 : _PList),
    _prev (_papp l1 l2) = _papp (_prev l2) (_prev l1).
Proof. trocq. apply nrev_napp. Qed.

Theorem _psum_papp : forall (l1 l2 : _PList),
    _psum (_papp l1 l2) = _psum l1 + _psum l2.
Proof. trocq. apply nsum_napp. Qed.

(* Manual version: ZList as monomorphic source *)

From Stdlib Require Import ZArith.

Theorem plength_papp_Z : forall (l1 l2 : PList Z),
    plength (papp l1 l2) = plength l1 + plength l2.
Proof. apply plength_papp_manual. Qed.

(* Trocq version: ZList as monomorphic source, mirrors NatList pattern *)

Inductive ZList : Type :=
    | ZNil  : ZList
    | ZCons : Z -> ZList -> ZList.

Fixpoint zlength (l : ZList) : nat :=
    match l with ZNil => O | ZCons _ t => S (zlength t) end.

Fixpoint zapp (l1 l2 : ZList) : ZList :=
    match l1 with ZNil => l2 | ZCons h t => ZCons h (zapp t l2) end.

Theorem zlength_zapp : forall (l1 l2 : ZList),
    zlength (zapp l1 l2) = zlength l1 + zlength l2.
Proof.
    intros l1 l2. induction l1 as [|h t IH]; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
Defined.

Definition _ZPList   : Type                          := PList Z.
Definition _zplength : _ZPList -> nat                := @plength Z.
Definition _zpapp    : _ZPList -> _ZPList -> _ZPList := @papp Z.

Fixpoint zplist_2_zlist (l : _ZPList) : ZList :=
    match l with PNil => ZNil | PCons h t => ZCons h (zplist_2_zlist t) end.

Fixpoint zlist_2_zplist (l : ZList) : _ZPList :=
    match l with ZNil => PNil | ZCons h t => PCons h (zlist_2_zplist t) end.

Lemma zplist_zlist_iso : forall l : _ZPList,
    zlist_2_zplist (zplist_2_zlist l) = l.
Proof. induction l as [|h t IH]; simpl. reflexivity. rewrite IH. reflexivity. Defined.

Lemma zlist_zplist_iso : forall l : ZList,
    zplist_2_zlist (zlist_2_zplist l) = l.
Proof. induction l as [|h t IH]; simpl. reflexivity. rewrite IH. reflexivity. Defined.

Definition R_ZList : Param44.Rel _ZPList ZList.
Proof.
    apply Iso.toParam; unshelve econstructor.
    - exact zplist_2_zlist.
    - exact zlist_2_zplist.
    - exact zplist_zlist_iso.
    - exact zlist_zplist_iso.
Defined.

Trocq Use R_ZList.

Lemma _zplength_eq_zlength : forall l : _ZPList,
    _zplength l = zlength (zplist_2_zlist l).
Proof.
    unfold _zplength. induction l as [|h t IH]; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
Defined.

Lemma zplist_2_zlist_app : forall l1 l2 : _ZPList,
    zplist_2_zlist (_zpapp l1 l2) = zapp (zplist_2_zlist l1) (zplist_2_zlist l2).
Proof.
    unfold _zpapp. intros l1 l2. induction l1 as [|h t IH]; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
Defined.

Lemma R__zplength (l : _ZPList) (l' : ZList) (lR : rel R_ZList l l') :
    natR (_zplength l) (zlength l').
Proof.
    change (zplist_2_zlist l = l') in lR.
    apply map_in_R_nat.
    rewrite _zplength_eq_zlength. rewrite lR. reflexivity.
Defined.

Lemma R__zpapp
    (l1 : _ZPList) (l1' : ZList) (l1R : rel R_ZList l1 l1')
    (l2 : _ZPList) (l2' : ZList) (l2R : rel R_ZList l2 l2') :
    rel R_ZList (_zpapp l1 l2) (zapp l1' l2').
Proof.
    change (zplist_2_zlist l1 = l1') in l1R.
    change (zplist_2_zlist l2 = l2') in l2R.
    change (zplist_2_zlist (_zpapp l1 l2) = zapp l1' l2').
    rewrite zplist_2_zlist_app. rewrite l1R. rewrite l2R. reflexivity.
Defined.

Trocq Use R__zplength.
Trocq Use R__zpapp.

Theorem _zplength_zpapp : forall (l1 l2 : _ZPList),
    _zplength (_zpapp l1 l2) = _zplength l1 + _zplength l2.
Proof. trocq. apply zlength_zapp. Qed.

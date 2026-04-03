From Stdlib Require Import ssreflect.
Local Open Scope nat_scope.

Set Universe Polymorphism.

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

Example nlength_ex1 : nlength [[]] = O.
Proof. simpl. reflexivity. Qed.

Example nlength_ex2 : nlength (S O :n: S (S O) :n: S (S (S O)) :n: [[]]) = S (S (S O)).
Proof. simpl. reflexivity. Qed.

Example nlength_ex3 : nlength (1 :n: 2 :n: 3 :n: [[]]) = 3.
Proof. simpl. reflexivity. Qed.

Example napp_ex : napp (1 :n: 2 :n: [[]]) (3 :n: 4 :n: [[]]) = (1 :n: 2 :n: 3 :n: 4 :n: [[]]).
Proof. simpl. reflexivity. Qed.
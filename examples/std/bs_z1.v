(*  bs_z1.v — Baby Step: Minimized Base Language *)

From Stdlib Require Import ssreflect Lia.
Local Open Scope nat_scope.
Set Universe Polymorphism.

(* A minimized base language of arithmetic expressions using nat *)
Inductive expr : Type :=
  | Const : nat -> expr
  | Plus  : expr -> expr -> expr.

Definition econst (n : nat) : expr := Const n.
Definition eplus (e1 e2 : expr) : expr := Plus e1 e2.

Fixpoint eval (e : expr) : nat :=
  match e with
  | Const n => n
  | Plus e1 e2 => eval e1 + eval e2
  end.

(* We prove 3 simple properties manually *)

Theorem eval_const_plus : forall x y,
  eval (eplus (econst x) (econst y)) = x + y.
Proof.
  intros. simpl. reflexivity.
Defined.

Theorem eval_assoc : forall e1 e2 e3,
  eval (eplus e1 (eplus e2 e3)) = eval (eplus (eplus e1 e2) e3).
Proof.
  intros. simpl. lia.
Defined.

Theorem eval_plus_zero_r : forall e,
  eval (eplus e (econst 0)) = eval e.
Proof.
  intros. simpl. lia.
Defined.

From Coq Require Import ssreflect.
From HoTT Require Import HoTT.
From Trocq Require Import Trocq.
From Coq Require Import List String.
(* From Trocq_examples Require Import N. *)

(** Set Universe Polymorphism

    Coq does not allow Type to be of type Type. Instead, it uses a hidden, infinite hierarchy of
    universes: Type@{0} has type Type@{1}, which has type Type@{2}, and so on.

    The command "Set Universe Polymorphism" changes this behavior. It tells Coq to treat universes
    as local, bound variables rather than fixed global constraints. This allows us to write more 
    general code that can work across different universe levels without having to specify them 
    explicitly.
*)
(* Set Universe Polymorphism. *)


(* ========================================== *)
(* PRELIMINARIES: Defining the missing types  *)
(* ========================================== *)

(* 1. We mock the Presence Condition (pc) as a string for this example *)
Definition pc := string.
Definition Nat := nat.

(* 2. As shown in the slides, Lifted(Nat) is a list of (Nat ⨯ pc) *)
Definition LiftedNat := list (Nat * pc).

(* 3. The `derive` function extracts the Base Nat for a specific configuration *)
Fixpoint derive (l : LiftedNat) (conf : pc) : Nat :=
  match l with
  | [] => 0 (* Default fallback if configuration is not found *)
  | (n, p) :: tail => if String.eqb p conf then n else derive tail conf
  end.
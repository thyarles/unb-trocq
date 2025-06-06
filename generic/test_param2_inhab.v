
(* From elpi.apps Require Import derive.std. *)
From elpi.apps Require Import derive.param2.
Require Import param2_inhab.


(* ========= *)
(* ENUM *)
(* ========= *)
Inductive empty :=.
Elpi derive.param2 empty.
Elpi derive.param2.inhab empty_R. 
Check empty_R_inhab : forall x : empty, empty_R x x.
Print empty_R_inhab.

Elpi derive.param2 unit.
Elpi derive.param2.inhab unit_R.
Check unit_R_inhab : forall x : unit, unit_R x x.
Print unit_R_inhab.

Elpi derive.param2 bool.
Elpi derive.param2.inhab bool_R.
Check bool_R_inhab : forall x : bool, bool_R x x.
Print bool_R_inhab.


(* ========= *)
(* Mentioning other inductives *)
(* ========= *)
Inductive box_unit := B : unit -> box_unit.
Elpi derive.param2 box_unit.
Elpi derive.param2.inhab box_unit_R.
Check box_unit_R_inhab : forall x : box_unit, box_unit_R x x.
Print box_unit_R_inhab.

(* ========= *)
(* RECURSIVE *)
(* ========= *)

Elpi derive.param2 nat.
Elpi Trace Browser.
About nat_R.
Elpi derive.param2.inhab nat_R.
Check nat_R_inhab : forall x, nat_R x x.
Print nat_R_inhab. 

(* ========= *)
(* Parametric *)
(* ========= *)
Inductive wrap (A : Type) := W : A -> wrap.
Elpi derive.param2 wrap.
Elpi derive.param2.inhab wrap_R.
Check wrap_R_inhab : forall (A : Type) (R : A -> A -> Type) (H : full2self A R) (x : wrap A), wrap_R A A R x x.
Print wrap_R_inhab.


Inductive option (A : Type) := None | Some : A -> option.
Elpi derive.param2 option.
Elpi derive.param2.inhab option_R.
Check option_R_inhab : forall (A : Type) (R : A -> A -> Type) (H : full2self A R) (x : option A), option_R A A R x x.
Print option_R_inhab.

Inductive list (A : Type) := Nil | Cons : A -> list.
Elpi derive.param2 list.
Elpi derive.param2.inhab list_R.
Check list_R_inhab : forall (A : Type) (R : A -> A -> Type) (H : full2self A R) (x : list A), list_R A A R x x.
Print list_R_inhab.
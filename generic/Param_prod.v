(*****************************************************************************)
(*                            *                    Trocq                     *)
(*  _______                   *       Copyright (C) 2023 Inria & MERCE       *)
(* |__   __|                  *    (Mitsubishi Electric R&D Centre Europe)   *)
(*    | |_ __ ___   ___ __ _  *       Cyril Cohen <cyril.cohen@inria.fr>     *)
(*    | | '__/ _ \ / __/ _` | *       Enzo Crance <enzo.crance@inria.fr>     *)
(*    | | | | (_) | (_| (_| | *   Assia Mahboubi <assia.mahboubi@inria.fr>   *)
(*    |_|_|  \___/ \___\__, | ************************************************)
(*                        | | * This file is distributed under the terms of  *)
(*                        |_| * GNU Lesser General Public License Version 3  *)
(*                            * see LICENSE file for the text of the license *)
(*****************************************************************************)

From Trocq Require Import Relnm. 

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Unset Universe Polymorphism.
Inductive prod_R (A1 A2 : Type) (A_R : A1 -> A2 -> Type) (B1 B2 : Type) (B_R : B1 -> B2 -> Type)
: prod A1 B1 -> prod A2 B2 -> Type :=
  pair_R : forall (a1 : A1) (a2 : A2),
A_R a1 a2 -> forall (b3 : B1) (b4 : B2),
B_R b3 b4 -> prod_R A1 A2 A_R B1 B2 B_R (@pair A1 B1 a1 b3) (@pair A2 B2 a2 b4).
Set Universe Polymorphism.

Elpi derive.param2.register "prod" "prod_R".
Elpi derive.param2.register "pair" "pair_R".
Elpi derive prod.
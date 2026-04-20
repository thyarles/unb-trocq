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
Set Asymmetric Patterns.

Elpi derive list.

Notation listR := list_R.
Notation nilR := nil_R.
Notation consR := cons_R.

Definition Param42b_list := list_rel42b.
Definition Param2a4_list := list_rel2a4.
Definition Param44_list := list_rel44.

Definition Param_nil : forall (A A' : Type) (AR : Param00.Rel A A'),
 list_R A A' AR (@nil A) (@nil A') := @nil_R.

Definition Param_cons : forall (A A' : Type) (AR : Param00.Rel A A') 
  (a : A) (a' : A') (aR : AR a a')
  (l : list A) (l' : list A') (lR : list_R A A' AR l l'),
      list_R A A' AR (cons a l) (cons a' l') := @cons_R. 

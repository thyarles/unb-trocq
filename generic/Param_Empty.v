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

From Trocq Require Import HoTTNotations Relnm. 

(* translations of inductives in Prop is not yet supported, 
but we can still generate everything for False by manually defining its parametricity translation and making it land in Type. *)
Unset Universe Polymorphism.
Inductive EmptyR : Empty -> Empty -> Type :=. 
(* param2 does not handle universe polymorphic inductives.
   Hence we have define EmptyR before seting Universe Polymorphism. *)
Elpi derive.param2.register "False" "EmptyR".

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

#[prefix="Empty_"] Elpi derive Empty.
Definition Param01_Empty := Empty_rel01.
Definition Param10_Empty := Empty_rel10.


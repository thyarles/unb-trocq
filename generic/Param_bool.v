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

Require Import ssreflect.
Require Import Stdlib Hierarchy Param_lemmas.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Import HoTTNotations.

Require Import Database.
From Trocq Require Import Relnm. 

Elpi derive Bool.
Definition BoolR := bool_R.
Definition trueR := true_R.
Definition Param44_Bool := bool_rel44.

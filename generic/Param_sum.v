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
Set Asymmetric Patterns.

Import HoTTNotations.

Require Import Database.
From Trocq Require Import Rel44. 
Elpi derive sum.
Check sum_map4 : forall (A1 A2 : Type) (AR : A1 -> A2 -> Type),
IsUMap AR -> forall (B1 B2 : Type) (BR : B1 -> B2 -> Type),
IsUMap BR -> IsUMap (sum_R A1 A2 AR B1 B2 BR). 

Definition Param01_sum := sum_rel01.

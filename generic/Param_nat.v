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

Require Import ssreflect ssrbool.
Require Import Stdlib Hierarchy Param_lemmas.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Import HoTTNotations.

Require Import Database.
From Trocq Require Import Relnm. 

Elpi derive nat.
Notation natR := nat_R.
Definition OR := O_R.
Definition SR := S_R.

Definition Param2a0_nat := nat_rel2a0.

Definition Param_add :
  forall (n1 n1' : nat) (n1R : natR n1 n1') (n2 n2' : nat) (n2R : natR n2 n2'),
    natR (n1 + n2) (n1' + n2').
Proof.
  intros n1 n1' n1R n2 n2' n2R.
  induction n1R as [|n1 n1' n1R IHn1R].
  - simpl. exact n2R.
  - simpl. apply SR. exact IHn1R.
Defined. 

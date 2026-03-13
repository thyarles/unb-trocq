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
From Trocq Require Import Rel44. 
Elpi derive nat.
Notation natR := nat_R.
Definition OR := O_R.
Definition SR := S_R.

Check nat_R : nat -> nat -> Type.
Check nat_mymap : nat -> nat. 
Check nat_mR : forall (b b' : nat) (e : nat_mymap b = b'), nat_R b b'. 
Check nat_Rm : forall (b b' : nat) (bR : nat_R b b'), nat_mymap b = b'.
Check nat_mRRmK : forall (b b' : nat) (bR : nat_R b b'), nat_mR _ _  (nat_Rm _ _  bR) = bR.
Check nat_sym : forall (b b' : nat) (bR : nat_R b b'), nat_R b' b.
Check nat_symK : forall (b b' : nat) (bR : nat_R b b'), nat_sym _ _ (nat_sym _ _ bR) = bR.
Check nat_rsymK : forall (b b' : nat), sym_rel nat_R b b' <->> nat_R b b'.
Check nat_map4 : Map4.Has nat_R.
Check nat_rel44 : Param44.Rel nat nat.
Check nat_rel00 : Param00.Rel nat nat.  
Check nat_rel2a0 : Param2a0.Rel nat nat. 
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

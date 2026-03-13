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
From Trocq Require Import Rel44. 
Elpi derive Bool.
Definition BoolR := bool_R.
Definition trueR := true_R.

Check bool_R : Bool -> Bool -> Type.
Check bool_mymap : Bool -> Bool. 
Check bool_mR : forall (b b' : Bool) (e : bool_mymap b = b'), bool_R b b'. 
Check bool_Rm : forall (b b' : Bool) (bR : bool_R b b'), bool_mymap b = b'.
Check bool_mRRmK : forall (b b' : Bool) (bR : bool_R b b'), bool_mR _ _  (bool_Rm _ _  bR) = bR.
Check bool_sym : forall (b b' : Bool) (bR : bool_R b b'), bool_R b' b.
Check bool_symK : forall (b b' : Bool) (bR : bool_R b b'), bool_sym _ _ (bool_sym _ _ bR) = bR.
Check bool_rsymK : forall (b b' : Bool), sym_rel bool_R b b' <->> bool_R b b'.
Check bool_map4 : Map4.Has bool_R.
Check bool_rel44 : Param44.Rel Bool Bool.

Definition Param44_Bool := bool_rel44.
Set Printing All.
Set Printing Universes.
Print bool_rel44.
Print Universes Subgraph (bool_rel44.u0  bool_rel44.u1).

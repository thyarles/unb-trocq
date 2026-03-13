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
Require Import Stdlib Hierarchy.

Import HoTTNotations.

Require Import Database.
From Trocq Require Import Rel44. 

(* translations of inductives in Prop is not yet supported, 
but we can still generate everything for False by manually defining its parametricity translation and making it land in Type. *)
Inductive EmptyR : Empty -> Empty -> Type :=.
(* param2 does not handle universe polymorphic inductives.
   Hence we have define EmptyR before seting Universe Polymorphism. *)
Elpi derive.param2.register "False" "EmptyR".

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Elpi derive Empty.

Check EmptyR : False -> False -> Type.
Check False_mymap : False -> False. 
Check False_mR : forall (b b' : False) (e : False_mymap b = b'), EmptyR b b'. 
Check False_Rm : forall (b b' : False) (bR : EmptyR b b'), False_mymap b = b'.
Check False_mRRmK : forall (b b' : False) (bR : EmptyR b b'), False_mR _ _  (False_Rm _ _  bR) = bR.
Check False_sym : forall (b b' : False) (bR : EmptyR b b'), EmptyR b' b.
Check False_symK : forall (b b' : False) (bR : EmptyR b b'), False_sym _ _ (False_sym _ _ bR) = bR.
Check False_rsymK : forall (b b' : False), sym_rel EmptyR b b' <->> EmptyR b b'.
Check False_map4 : Map4.Has EmptyR.
Check False_rel44 : Param44.Rel False False.

Definition Param01_Empty := False_rel01.
Definition Param10_Empty := False_rel10.

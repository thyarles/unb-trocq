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
Elpi derive option.

Check option_R : forall A1 A2 (AR : A1 -> A2 -> Type), option A1 -> option A2 -> Type.
Check option_mymap : forall A1 A2 (AR : A1 -> A2 -> Type), Map1.Has AR-> option A1 -> option A2. 
Check option_mR : forall A1 A2 (AR : A1 -> A2 -> Type) (AM: Map2a.Has AR), 
  forall l1 l2, option_mymap _ _ _ AM l1 = l2 -> option_R _ _ AR l1 l2.
Check option_Rm : forall A1 A2 (AR : A1 -> A2 -> Type) (AM: Map2b.Has AR), 
  forall l1 l2, option_R _ _ AR l1 l2 -> option_mymap _ _ _ AM l1 = l2.
Check option_mRRmK : forall A1 A2 (AR : A1 -> A2 -> Type) (AM: Map4.Has AR), 
  forall l1 l2 lR, option_mR _ _ _ AM _ _ (option_Rm _ _ _ AM _ _ lR) = lR. 
Check option_sym : forall A1 A2 (A_R : A1 -> A2 -> Type) l1 l2, option_R A1 A2 A_R l1 l2 ->
option_R A2 A1 (sym_rel A_R) l2 l1. 

Check option_symK : forall (A1 A2 : Type) (A_R : A1 -> A2 -> Type) (s1 : option A1)
(s2 : option A2) (IR : option_R A1 A2 A_R s1 s2),
  option_sym A2 A1 (sym_rel A_R) s2 s1 (option_sym A1 A2 A_R s1 s2 IR) =
  IR. 
Check option_rsymK : forall (A1 A2 : Type) (A_R : A1 -> A2 -> Type) (s1 : option A1)
  (s2 : option A2),
  option_R A2 A1 (sym_rel A_R) s2 s1 <->> option_R A1 A2 A_R s1 s2.
Check option_rel44 :
     forall A1 A2 : Type, (A1 <=> A2)%P -> (option A1 <=> option A2)%P. 
     
Check option_map2a : forall (A1 A2 : Type) (AR : A1 -> A2 -> Type),
Map2a.Has AR -> Map2a.Has (option_R A1 A2 AR).

Check option_map2b : forall (A1 A2 : Type) (AR : A1 -> A2 -> Type),
Map2b.Has AR -> Map2b.Has (option_R A1 A2 AR).

Check option_map3 : forall (A1 A2 : Type) (AR : A1 -> A2 -> Type),
Map3.Has AR -> Map3.Has (option_R A1 A2 AR).

Check option_map4 : forall (A1 A2 : Type) (AR : A1 -> A2 -> Type),
Map4.Has AR -> Map4.Has (option_R A1 A2 AR).

Check option_rel00 : forall A1 A2 : Type,
Param00.Rel A1 A2 -> Param00.Rel (option A1) (option A2).

Check option_rel42a : forall A1 A2 : Type,
Param42a.Rel A1 A2 -> Param42a.Rel (option A1) (option A2).

Check option_rel42b : forall A1 A2 : Type,
Param42b.Rel A1 A2 -> Param42b.Rel (option A1) (option A2).

Check option_rel2a4 : forall A1 A2 : Type,
Param2a4.Rel A1 A2 -> Param2a4.Rel (option A1) (option A2).

Check option_rel2b4 : forall A1 A2 : Type,
Param2b4.Rel A1 A2 -> Param2b4.Rel (option A1) (option A2).

Check option_rel33 : forall A1 A2 : Type,
Param33.Rel A1 A2 -> Param33.Rel (option A1) (option A2).

Check option_rel44 : forall (A A' : Type) (AR : Param44.Rel A A'), Param44.Rel (option A) (option A').

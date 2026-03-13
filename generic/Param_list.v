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
Elpi derive list.
Notation listR := list_R.
Notation nilR := nil_R.
Notation consR := cons_R.

Check list_R : forall A1 A2 (AR : A1 -> A2 -> Type), list A1 -> list A2 -> Type.
Check list_mymap : forall A1 A2 (AR : A1 -> A2 -> Type), Map1.Has AR-> list A1 -> list A2. 
Check list_mR : forall A1 A2 (AR : A1 -> A2 -> Type) (AM: Map2a.Has AR), 
  forall l1 l2, list_mymap _ _ _ AM l1 = l2 -> list_R _ _ AR l1 l2.
Check list_Rm : forall A1 A2 (AR : A1 -> A2 -> Type) (AM: Map2b.Has AR), 
  forall l1 l2, list_R _ _ AR l1 l2 -> list_mymap _ _ _ AM l1 = l2.
Check list_mRRmK : forall A1 A2 (AR : A1 -> A2 -> Type) (AM: Map4.Has AR), 
  forall l1 l2 lR, list_mR _ _ _ AM _ _ (list_Rm _ _ _ AM _ _ lR) = lR. 
Check list_sym : forall A1 A2 (A_R : A1 -> A2 -> Type) l1 l2, list_R A1 A2 A_R l1 l2 ->
list_R A2 A1 (sym_rel A_R) l2 l1. 

Check list_symK : forall (A1 A2 : Type) (A_R : A1 -> A2 -> Type) (s1 : list A1)
(s2 : list A2) (IR : list_R A1 A2 A_R s1 s2),
  list_sym A2 A1 (sym_rel A_R) s2 s1 (list_sym A1 A2 A_R s1 s2 IR) =
  IR. 
Check list_rsymK : forall (A1 A2 : Type) (A_R : A1 -> A2 -> Type) (s1 : list A1)
  (s2 : list A2),
  list_R A2 A1 (sym_rel A_R) s2 s1 <->> list_R A1 A2 A_R s1 s2.
Check list_rel44 :
     forall A1 A2 : Type, (A1 <=> A2)%P -> (list A1 <=> list A2)%P. 
     
Check list_map2a : forall (A1 A2 : Type) (AR : A1 -> A2 -> Type),
Map2a.Has AR -> Map2a.Has (list_R A1 A2 AR).

Check list_map2b : forall (A1 A2 : Type) (AR : A1 -> A2 -> Type),
Map2b.Has AR -> Map2b.Has (list_R A1 A2 AR).

Check list_map3 : forall (A1 A2 : Type) (AR : A1 -> A2 -> Type),
Map3.Has AR -> Map3.Has (list_R A1 A2 AR).

Check list_map4 : forall (A1 A2 : Type) (AR : A1 -> A2 -> Type),
Map4.Has AR -> Map4.Has (list_R A1 A2 AR).

Check list_rel00 : forall A1 A2 : Type,
Param00.Rel A1 A2 -> Param00.Rel (list A1) (list A2).

Check list_rel42a : forall A1 A2 : Type,
Param42a.Rel A1 A2 -> Param42a.Rel (list A1) (list A2).

Check list_rel42b : forall A1 A2 : Type,
Param42b.Rel A1 A2 -> Param42b.Rel (list A1) (list A2).

Check list_rel2a4 : forall A1 A2 : Type,
Param2a4.Rel A1 A2 -> Param2a4.Rel (list A1) (list A2).

Check list_rel2b4 : forall A1 A2 : Type,
Param2b4.Rel A1 A2 -> Param2b4.Rel (list A1) (list A2).

Check list_rel33 : forall A1 A2 : Type,
Param33.Rel A1 A2 -> Param33.Rel (list A1) (list A2).

Check list_rel44 : forall (A A' : Type) (AR : Param44.Rel A A'), Param44.Rel (list A) (list A').

Definition Param42b_list := list_rel42b.
Definition Param2a4_list := list_rel2a4.
Definition Param44_list := list_rel44.

Definition Param_nil : forall (A A' : Type) (AR : Param00.Rel A A'),
 list_R A A' AR (@nil A) (@nil A') := @nil_R.

Definition Param_cons : forall (A A' : Type) (AR : Param00.Rel A A') 
  (a : A) (a' : A') (aR : AR a a')
  (l : list A) (l' : list A') (lR : list_R A A' AR l l'),
      list_R A A' AR (cons a l) (cons a' l') := @cons_R. 

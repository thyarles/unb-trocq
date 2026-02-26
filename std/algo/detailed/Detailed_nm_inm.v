
From Trocq Require Import map4 umap Rel40 symK RsymK.
Import HoTTNotations.
From Trocq Require Import coverage.
Unset Uniform Inductive Parameters.

Require Import Stdlib Hierarchy Param_lemmas.
Elpi derive List.

(* From Trocq Require Import Hierarchy. *)
Require Import ssreflect.

Lemma M1_List : forall A B (AR : A -> B -> Type) (AM : Map1.Has AR), 
  Map1.Has (List_R A B AR).
move=> A B AR M1.
apply Map1.BuildHas.
apply (List_mymap A B AR M1).
Set Printing All.
Show Proof.
Qed.
Lemma M2a_List : forall A B (AR : A -> B -> Type) (AM : Map2a.Has AR), 
  Map2a.Has (List_R A B AR).
move=> A B AR M1.
apply (Map2a.BuildHas _ _ _ (List_mymap A B AR M1) (List_mR A B AR M1)).
Show Proof.
Qed.
Lemma M2b_List : forall A B (AR : A -> B -> Type) (AM : Map2b.Has AR), 
  Map2b.Has (List_R A B AR).
move=> A B AR M1.
apply (Map2b.BuildHas _ _ _ (List_mymap A B AR M1) (List_Rm A B AR M1)).
Show Proof.
Qed.

Lemma M3_List : forall A B (AR : A -> B -> Type) (AM : Map3.Has AR), 
  Map3.Has (List_R A B AR).
move=> A B AR M1.
apply (Map3.BuildHas _ _ _ (List_mymap A B AR M1) (List_mR A B AR M1) (List_Rm A B AR M1)).
Show Proof.
Qed.

Lemma M4_List : forall A B (AR : A -> B -> Type) (AM : Map4.Has AR), 
  Map4.Has (List_R A B AR).
move=> A B AR M1.
About Map4.BuildHas.
About Map3.BuildHas.
apply (@Map4.BuildHas _ _ _ (List_mymap A B AR M1) (List_mR A B AR M1) (List_Rm A B AR M1) (List_mRRmK A B AR M1)).
Show Proof.
Qed.

Lemma p42a_list : forall A B (AR : Param42a.Rel A B), Param42a.Rel (List A) (List B).
Proof.
move=> A B [R coM contraM].
unshelve econstructor.
- exact: List_R.
- by apply List_umap.
- 
unshelve eapply eq_Map2a.
exact (List_R B A (sym_rel R)).
exact (List_rsymK B A (sym_rel R)).
by apply M2a_List.
Show Proof.
Qed.
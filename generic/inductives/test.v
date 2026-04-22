From elpi.apps Require Export derive.

From elpi.apps Require Export 
  derive.param2.

From Trocq Require Export HoTTNotations Hierarchy Stdlib.

Unset Universe Polymorphism.
Inductive EmptyR : Empty -> Empty -> Type :=.
(* param2 does not handle universe polymorphic inductives.
   Hence we have define EmptyR before seting Universe Polymorphism. *)
Elpi derive.param2.register "False" "EmptyR".

Set Universe Polymorphism.
 From Trocq Require Export injection_lemmas injK.

#[verbose] Elpi derive Empty.
#[verbose] Elpi derive.injections Empty.
Elpi derive.injK Empty.
Elpi derive Empty.

  derive.projK.

(* From Trocq Require Export sym symK RsymK. *)
(* From Trocq Require Export mymap mR Rm mRRmK mapn Relnm. *)

Unset Universe Minimization ToSet.

#[verbose] Elpi derive Empty.
Definition Param01_Empty := False_rel01.
Definition Param10_Empty := False_rel10.

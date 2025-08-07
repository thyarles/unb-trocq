From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From elpi.apps.derive.elpi Extra Dependency "discriminate.elpi" as discr.
From Trocq Extra Dependency "common_algo.elpi" as common.
From Trocq Extra Dependency "mR.elpi" as mR.
From Trocq Require Import mymap injection_lemmas.

From elpi Require Import elpi.
From elpi.apps Require Import derive.param2 derive.isK.
From elpi.apps Require Import derive.bcongr (* for eq_f register *) 
                              derive.eqK (*for bool_discr *)
                              derive.isK. (* for isK db required by discriminate *)
From elpi.apps Require Import map.                              

From Trocq Require Import Hierarchy.
Unset Uniform Inductive Parameters. 

Elpi Db derive.mR.db lp:{{
  % [ar-db A1 A2 AR] returns the relation between a type A1 and A2.
  pred ar-db i:term, i:term, o:term. 
  % [mR-db T D] links a type T to its corresponding map in R.
  pred mR-db i:term, o:term.

  % [mR-done T] mean T was already derived
  pred mR-done o:term.
}}.

Elpi Command derive.mR.
Elpi Accumulate File derive_hook.
Elpi Accumulate Db Header derive.param2.db.
Elpi Accumulate Db derive.param2.db.
Elpi Accumulate Db derive.mymap.db.
Elpi Accumulate File discr.
Elpi Accumulate Db derive.isK.db.
Elpi Accumulate Db derive.injections.db.
Elpi Accumulate File common.
Elpi Accumulate Db derive.mR.db.
Elpi Accumulate File mR.
Elpi Accumulate lp:{{
  main [str I] :- !, coq.locate I (indt GR),
    coq.gref->id (indt GR) Tname,
    Prefix is Tname ^ "_",
    derive.mR.main GR Prefix _.
  main _ :- usage.

  pred usage.
  usage :- coq.error "Usage: derive.mR <object name>".
}}. 

Elpi derive list.
(* Print list_R. *)
Goal forall (A B : Type) (R : Param10.Rel A B), A -> B.
intros A B R. Fail exact R. exact (map R). Abort.



Inductive False : Prop :=.
Elpi derive.param2 False.
Elpi derive.mymap False.
Elpi derive.projK False.
Elpi derive.injections False.
Elpi derive.isK False.
Elpi derive.mR False.

Elpi derive.param2 unit.
Elpi derive.mymap unit.
Elpi derive.projK unit.
Elpi derive.injections unit.
Elpi derive.isK unit.
Elpi derive.mR unit.

Elpi derive.param2 bool.
Elpi derive.mymap bool.
Elpi derive.isK bool.
Elpi derive.mR bool.
Print bool_mR.

Inductive Wrap : Type :=
| KWrap1 : unit -> Wrap.

Elpi derive.param2 Wrap.
Elpi derive.mymap Wrap.
Elpi derive.projK Wrap.
Elpi derive.injections Wrap.
Elpi derive.mR Wrap.
Print Wrap_mR.

Inductive WrapMore : Type :=
| KWrap : unit -> bool -> WrapMore
| KWrapWrap : Wrap -> WrapMore
| F : unit -> unit -> unit -> WrapMore.

Elpi derive.param2 WrapMore.
Elpi derive.mymap WrapMore.
Elpi derive.projK WrapMore.
Elpi derive.injections WrapMore.
Elpi derive.isK WrapMore.
Elpi derive.mR WrapMore.
Print WrapMore_mR.

Elpi derive.param2 nat.
Elpi derive.mymap nat.
Elpi derive.isK nat.
Elpi derive.mR nat.

Inductive Box (A : Type) :=
| B : A -> Box A.

Elpi derive.param2 Box.
Elpi derive.mymap Box.
Elpi derive.projK Box.
Elpi derive.injections Box.
Elpi derive.isK Box.
Elpi derive.mR Box.

Elpi derive.param2 option.
Elpi derive.mymap option.
Elpi derive.projK option.
Elpi derive.injections option.
Elpi derive.isK option.
Elpi derive.mR option.
Print option_mR.

Elpi derive.param2 prod.
Elpi derive.mymap prod.
Elpi derive.projK prod.
Elpi derive.injections prod.
Elpi derive.isK prod.
Elpi derive.mR prod.
Print prod_mR.


Fail Elpi derive.param2 list.
Elpi derive.mymap list.
Elpi derive.projK list.
Elpi derive.injections list.
Elpi derive.isK list.
Elpi Trace Browser.

Elpi derive.mR list.
Print list_mR.

Elpi Query lp:{{
  F = {{ fun (A : Type) (l : list A) => match l with nil => unit | cons a l => Prop end }}.
  %coq.elaborate-skeleton F Ty FE ok,
  coq.typecheck F Ty ok.
  coq.say F.
  %F = {{ fun b : bool => match b with true => unit | false => Prop end }}.
  %std.findall (param {{ option }} {{ option }} T ) Rules,
  %std.findall (param {{ list }} {{ list }} T ) Rules,
  %std.findall (mymap-db {{ option nat }} {{ option nat }} C ) Rules,
  %coq.typecheck T Ty _,
  coq.say Rules.

}}. 

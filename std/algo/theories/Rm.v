From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From Trocq Extra Dependency "algo/elpi/Rm.elpi" as Rm.
From Trocq Extra Dependency "algo/elpi/common_algo.elpi" as common.
From Trocq Extra Dependency "algo/elpi/utils.elpi" as algo_utils.

From elpi Require Import elpi.
From elpi.apps Require Import derive.param2.
From elpi.apps Require Import derive.bcongr. (* for eq_f register *) 
From Trocq Require Import mymap.
From elpi.apps Require Import derive.induction.
(* From Trocq Require Import HoTT_additions Hierarchy. *)
From Trocq Require Import Hierarchy.
Unset Uniform Inductive Parameters. 

Elpi Db derive.Rm.db lp:{{
  % [ar-db A1 A2 AR] returns the relation between a type A1 and A2.
  pred ar-db i:term, i:term, o:term. 

  % [Rm-db T D] links a type T to its corresponding R in map.
  pred rm-db i:term, o:term.

  % [Rm-done T] mean T was already derived
  pred rm-done o:term.
}}.

Elpi Command derive.Rm.
Elpi Accumulate File derive_hook.
Elpi Accumulate Db Header derive.param2.db.
Elpi Accumulate Db derive.param2.db.
Elpi Accumulate Db derive.mymap.db.
Elpi Accumulate File common.
Elpi Accumulate File algo_utils.
Elpi Accumulate Db Header derive.Rm.db.
Elpi Accumulate Db derive.Rm.db.
Elpi Accumulate File Rm.
Elpi Accumulate lp:{{
  main [str I] :- !, coq.locate I (indt GR),
    coq.gref->id (indt GR) Tname,
    Prefix is Tname ^ "_",
    derive.Rm.main GR Prefix _.
  main _ :- usage.

  pred usage.
  usage :- coq.error "Usage: derive.Rm <object name>".
}}. 

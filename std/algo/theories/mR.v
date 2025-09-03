From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From elpi.apps.derive.elpi Extra Dependency "discriminate.elpi" as discr.
From Trocq Extra Dependency "algo/elpi/common_algo.elpi" as common.
From Trocq Extra Dependency "algo/elpi/mR.elpi" as mR.
From Trocq Extra Dependency "algo/elpi/injection_lemmas.elpi" as injections.

From elpi Require Import elpi.
From elpi.apps Require Export derive.param2 derive.isK.
From elpi.apps Require Export derive.bcongr (* for eq_f register *) 
                              derive.eqK (*for bool_discr *)
                              derive.isK. (* for isK db required by discriminate *)
From Trocq Require Export mymap injection_lemmas. 

From Trocq Require Export Hierarchy.
Unset Uniform Inductive Parameters. 

Elpi Db derive.mR.db lp:{{
  % [ar-db A1 A2 AR] returns the relation between a type A1 and A2.
  pred ar-db i:term, i:term, o:term. 
  % [mR-db T D] links a type T to its corresponding map in R.
  pred mR-db i:term, o:term.

  % [mR-done T] mean T was already derived
  pred mR-done o:inductive.
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

(* hook into derive *)
(* Elpi Accumulate derive Db derive.mR.db.
Elpi Accumulate derive File discr.
Elpi Accumulate derive File common.
Elpi Accumulate derive File injections.
Elpi Accumulate derive File mR.

#[phases="both"] Elpi Accumulate derive lp:{{
  dep1 "mR" "param2".
  dep1 "mR" "mymap".
  dep1 "mR" "injections".
  dep1 "mR" "isK".
}}.

#[synterp] Elpi Accumulate derive lp:{{
  derivation _ _ (derive "mR" (cl\ cl = []) true).
}}.

Elpi Accumulate derive lp:{{

derivation (indt T) Prefix ff (derive "mR" (derive.mR.main T Prefix) (mR-done T)).

}}. *)





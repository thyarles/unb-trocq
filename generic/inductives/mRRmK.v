From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From Trocq.Elpi Extra Dependency "inductives/mRRmK.elpi" as mRRmK.
From Trocq.Elpi Extra Dependency "inductives/common_algo.elpi" as common.
From Trocq.Elpi Extra Dependency "inductives/utils.elpi" as algo_utils.
From Trocq Require Export mymap injK mR Rm.

From elpi Require Import elpi.
From elpi.apps Require Export derive.param2.
From Trocq Require Import Hierarchy.
Unset Uniform Inductive Parameters. 

Elpi Db derive.mRRmK.db lp:{{
  % [ar-db A1 A2 AR] returns the relation between a type A1 and A2.
  pred ar-db i:term, i:term, o:term. 

  % [mRRmK-db T D] links a type T to its corresponding R in map.
  pred mRRmK-db i:term, o:term.

  % [mRRmK-done T] mean T was already derived
  pred mRRmK-done o:inductive.
}}.

Elpi Command derive.mRRmK.
Elpi Accumulate File derive_hook.
Elpi Accumulate Db Header derive.param2.db.
Elpi Accumulate Db derive.param2.db.
Elpi Accumulate Db derive.mymap.db.
Elpi Accumulate File common.
Elpi Accumulate File algo_utils.
Elpi Accumulate Db Header derive.injectionsK.db.
Elpi Accumulate Db derive.injectionsK.db.
Elpi Accumulate Db Header derive.mR.db.
Elpi Accumulate Db derive.mR.db.
Elpi Accumulate Db Header derive.Rm.db.
Elpi Accumulate Db derive.Rm.db.

Elpi Accumulate Db Header derive.mRRmK.db.
Elpi Accumulate Db derive.mRRmK.db.
Elpi Accumulate File mRRmK.
Elpi Accumulate lp:{{
  main [str I] :- !, coq.locate I (indt GR),
    coq.gref->id (indt GR) Tname,
    Prefix is Tname ^ "_",
    derive.mRRmK.main GR Prefix _.
  main _ :- usage.

  pred usage.
  usage :- coq.error "Usage: derive.mRRmK <object name>".
}}. 



(* hook into derive *)
Elpi Accumulate derive Db derive.mRRmK.db.
Elpi Accumulate derive File common.
Elpi Accumulate derive File algo_utils.
Elpi Accumulate derive File mRRmK.

Elpi Accumulate derive lp:{{

dep1 "mRRmK" "param2".
dep1 "mRRmK" "mymap".
dep1 "mRRmK" "injK".
dep1 "mRRmK" "mR".
dep1 "mRRmK" "Rm".
derivation (indt T) Prefix ff (derive "mRRmK" (derive.mRRmK.main T Prefix) (mRRmK-done T)).

}}.

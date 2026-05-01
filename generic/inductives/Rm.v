From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From Trocq.Elpi Extra Dependency "inductives/Rm.elpi" as Rm.
From Trocq.Elpi Extra Dependency "inductives/common_algo.elpi" as common.
From Trocq.Elpi Extra Dependency "inductives/utils.elpi" as algo_utils.

From elpi Require Import elpi.
From Trocq Require Export Hierarchy Param_lemmas mymap.

From elpi.apps Require Export derive derive.param2.

Unset Uniform Inductive Parameters. 
Elpi Db derive.Rm.db lp:{{
  % [ar-db A1 A2 AR] returns the relation between a type A1 and A2.
  pred ar-db i:term, i:term, o:term. 

  % [Rm-db T D] links an inductive type T to its corresponding R in map.
  pred rm-def i:gref, o:gref.
  pred rm-db i:term, o:term, o:term.

  % [Rm-done T] mean T was already derived
  pred rm-done o:inductive.
}}.

#[superglobal] Elpi Accumulate derive.Rm.db lp:{{  

  % refactor db dispatchers
  rm-db I _ R :-
    coq.env.global (indt GRI) I,
    rm-def (indt GRI) GRR,
    coq.env.global GRR R.

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

(* hook into derive *)
Elpi Accumulate derive Db Header derive.Rm.db.
Elpi Accumulate derive Db derive.Rm.db.
Elpi Accumulate derive File common.
Elpi Accumulate derive File algo_utils.
Elpi Accumulate derive File Rm.

Elpi Accumulate derive lp:{{
dep1 "Rm" "mymap".
dep1 "Rm" "param2".
derivation (indt T) Prefix ff (derive "Rm" (derive.Rm.main T Prefix) (rm-done T)).

}}.

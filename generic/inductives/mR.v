From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From Trocq.Elpi.inductives Extra Dependency "mR.elpi" as mR.

From elpi Require Import elpi.
From elpi.apps Require Export derive.param2 derive.isK. (* for isK db required by discriminate *)
From Trocq Require Export DeriveLib mymap injection_lemmas. 

From Trocq Require Export Hierarchy Param_lemmas Stdlib.
Unset Uniform Inductive Parameters. 

Elpi Db derive.mR.db lp:{{
  % [ar-db A1 A2 AR] returns the relation between a type A1 and A2.
  pred ar-db i:term, i:term, o:term. 
  % [mR-db T D] links an inductive T to its corresponding map in R.
  pred mR-def i:gref, o:gref.

  pred mR-db i:term, i:term, o:term.

  % [mR-done T] mean T was already derived
  pred mR-done o:inductive.
}}.

#[superglobal] Elpi Accumulate derive.mR.db lp:{{ 

  % refactor db dispatchers
  mR-db I _ R :-
    coq.env.global (indt GRI) I,
    mR-def (indt GRI) GRR,
    coq.env.global GRR R.

}}.

Elpi Command derive.mR.
Elpi Accumulate Db Header derive.param2.db.
Elpi Accumulate Db Header derive.isK.db.
Elpi Accumulate Db Header derive.mymap.db.
Elpi Accumulate Db Header derive.injections.db.
Elpi Accumulate Db Header derive.mR.db.
Elpi Accumulate File derive_hook.
Elpi Accumulate File mR.
Elpi Accumulate Db derive.param2.db.
Elpi Accumulate Db derive.mymap.db.
Elpi Accumulate Db derive.isK.db.
Elpi Accumulate Db derive.injections.db.
Elpi Accumulate Db derive.mR.db.
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
Elpi Accumulate derive File mR.
Elpi Accumulate derive Db derive.mR.db.

#[phases="both"] Elpi Accumulate derive lp:{{
  dep1 "mR" "param2".
  dep1 "mR" "mymap".
  dep1 "mR" "injections".
  dep1 "mR" "isK".
}}.

Elpi Accumulate derive lp:{{

derivation (indt T) Prefix ff (derive "mR" (derive.mR.main T Prefix) (mR-done T)).

}}.

From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From Trocq.Elpi Extra Dependency "inductives/mapn.elpi" as mapn.
From Trocq Require Import Database map4.
Unset Uniform Inductive Parameters. 

Elpi Command derive.mapn.
Elpi Accumulate Db Header derive.param2.db.
Elpi Accumulate Db Header derive.mymap.db.
Elpi Accumulate Db Header derive.mR.db.
Elpi Accumulate Db Header derive.Rm.db.
Elpi Accumulate Db Header derive.mRRmK.db.
Elpi Accumulate Db Header trocq.db.
Elpi Accumulate File derive_hook.
Elpi Accumulate File mapn.
Elpi Accumulate Db derive.param2.db.
Elpi Accumulate Db derive.mymap.db.
Elpi Accumulate Db derive.mR.db.
Elpi Accumulate Db derive.Rm.db.
Elpi Accumulate Db derive.mRRmK.db.
Elpi Accumulate Db trocq.db.
Elpi Accumulate lp:{{
  main [str I] :- !, coq.locate I (indt GR),
    coq.gref->id (indt GR) Tname,
    Prefix is Tname ^ "_",
    derive.mapn.main GR Prefix _.
  main _ :- usage.

  pred usage.
  usage :- coq.error "Usage: derive.rel40 <object name>".
}}. 

#[superglobal] Elpi Accumulate trocq.db lp:{{ 

  trocq.db.map-ind I M R :-
    coq.env.global (indt GRI) I,
    trocq.db.map-def (indt GRI) M GRR,
    coq.env.global GRR R.

}}.
Elpi Accumulate derive File mapn.
Elpi Accumulate derive Db trocq.db.

Elpi Accumulate derive lp:{{

dep1 "mapn" "mRRmK".
derivation (indt T) Prefix ff (derive "mapn" (derive.mapn.main T Prefix) (trocq.db.map-ind-done T)).

}}.

From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From Trocq.Elpi.inductives Extra Dependency "sym.elpi" as sym.

From elpi.apps Require Export derive derive.param2.
From Trocq Require Export Hierarchy Stdlib.
Unset Uniform Inductive Parameters. 

Elpi Db derive.sym.db lp:{{

  % [sym I S] links I inductive type, 
  %  with the function showing symmetry 
  pred sym-db i:term, o:term.
  pred sym-def i:gref, o:gref.

  % [sym-done T K] means T K was already derived
  pred sym-done o:inductive. 

  % refactor db dispatchers
  sym-db I R :-
    coq.env.global (indt GRI) I,
    sym-def (indt GRI) GRR,
    coq.env.global GRR R.

}}.

Elpi Command derive.sym.
Elpi Accumulate Db Header derive.param2.db.
Elpi Accumulate Db Header derive.sym.db.
Elpi Accumulate File derive_hook.
Elpi Accumulate File sym.
Elpi Accumulate Db derive.sym.db.
Elpi Accumulate Db derive.param2.db.
Elpi Accumulate lp:{{
  
  main [str I] :- !, 
    coq.locate I (indt GR),
    % Ind is (indt GR)
    coq.gref->id (indt GR) Tname,
    Suffix is Tname ^ "_",
    derive.sym.main GR Suffix _.
  main _ :- usage.

  pred usage.
  usage :- coq.error "Usage: derive.sym <object name>".
}}. 

(* hook into derive *)


Elpi Accumulate derive Db Header derive.sym.db.
Elpi Accumulate derive File sym.
Elpi Accumulate derive Db derive.sym.db.

Elpi Accumulate derive lp:{{

dep1 "sym" "param2".
derivation (indt T) Prefix ff (derive "sym" (derive.sym.main T Prefix) (sym-done T)).

}}.


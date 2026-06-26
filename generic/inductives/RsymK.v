
From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From Trocq.Elpi.inductives Extra Dependency "RsymK.elpi" as rsymK.
From Trocq Require Import sym symK. 
Import HoTTNotations.

From elpi.apps Require Import derive derive.param2.

From Trocq Require Export Hierarchy.
Unset Uniform Inductive Parameters. 

Elpi Db derive.rsymK.db lp:{{

  % [rsymK I S] links I inductive type, 
  %  with the function showing i1 i2, [| I |]^ i2 i1 <->> [| I |] i1 i2
  pred rsymK-db i:term, o:term.
  pred rsymK-def i:gref, o:gref.

  % [rsymK-done T K] means T K was already derived
  pred rsymK-done o:inductive. 

  % refactor db dispatchers
  rsymK-db I R :-
    coq.env.global (indt GRI) I,
    rsymK-def (indt GRI) GRR,
    coq.env.global GRR R.

}}.

Elpi Command derive.rsymK.
Elpi Accumulate Db Header derive.param2.db.
Elpi Accumulate Db Header derive.sym.db.
Elpi Accumulate Db Header derive.symK.db.
Elpi Accumulate Db Header derive.rsymK.db.
Elpi Accumulate File derive_hook.
Elpi Accumulate File rsymK.
Elpi Accumulate Db derive.param2.db.
Elpi Accumulate Db derive.sym.db.
Elpi Accumulate Db derive.symK.db.
Elpi Accumulate Db derive.rsymK.db.
Elpi Accumulate lp:{{
  
  main [str I] :- !, 
    coq.locate I (indt GR),
    % Ind is (indt GR)
    coq.gref->id (indt GR) Tname,
    Suffix is Tname ^ "_",
    derive.rsymK.main GR Suffix _.
  main _ :- usage.

  pred usage.
  usage :- coq.error "Usage: derive.rsymK <object name>".
}}. 

(* hook into derive *)
Elpi Accumulate derive Db Header derive.rsymK.db.
Elpi Accumulate derive Db Header derive.sym.db.
Elpi Accumulate derive Db Header derive.symK.db.
Elpi Accumulate derive File rsymK.
Elpi Accumulate derive Db derive.rsymK.db.
Elpi Accumulate derive Db derive.sym.db.
Elpi Accumulate derive Db derive.symK.db.

Elpi Accumulate derive lp:{{

dep1 "rsymK" "param2".
dep1 "rsymK" "sym".
dep1 "rsymK" "symK".
derivation (indt T) Prefix ff (derive "rsymK" (derive.rsymK.main T Prefix) (rsymK-done T)).

}}.
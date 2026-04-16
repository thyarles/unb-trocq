
From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From elpi.apps.derive.elpi Extra Dependency "derive_synterp_hook.elpi" as derive_synterp_hook.
From Trocq.Elpi Extra Dependency "inductives/common_algo.elpi" as common. 
From Trocq.Elpi Extra Dependency "inductives/utils.elpi" as utils. 
From Trocq.Elpi Extra Dependency "inductives/symK.elpi" as symK.
From Trocq Require Import sym. 
(* Extra Dependency "algo/elpi/sym.elpi" as sym.  *)

From elpi.apps Require Import derive.legacy derive.param2.

From Trocq Require Export Hierarchy.
Unset Uniform Inductive Parameters. 

Elpi Db derive.symK.db lp:{{

  % [symK I S] links I inductive type, 
  %  with the function showing symmetry is "involutive" 
  pred symK-db i:term, o:term.

  % [symK-done T K] means T K was already derived
  pred symK-done o:inductive. 
}}.

Elpi Command derive.symK.
Elpi Accumulate File derive_hook.
Elpi Accumulate Db Header derive.param2.db.
Elpi Accumulate Db derive.param2.db.
Elpi Accumulate Db Header derive.sym.db.
Elpi Accumulate Db derive.sym.db.
Elpi Accumulate File common. 
Elpi Accumulate File utils. 
Elpi Accumulate Db Header derive.symK.db.
Elpi Accumulate Db derive.symK.db.
Elpi Accumulate File symK.
Elpi Accumulate lp:{{
  
  main [str I] :- !, 
    coq.locate I (indt GR),
    % Ind is (indt GR)
    coq.gref->id (indt GR) Tname,
    Suffix is Tname ^ "_",
    derive.symK.main GR Suffix _.
  main _ :- usage.

  pred usage.
  usage :- coq.error "Usage: derive.symK <object name>".
}}. 

(* hook into derive *)
Elpi Accumulate derive Db Header derive.symK.db.
Elpi Accumulate derive Db derive.symK.db.
Elpi Accumulate Db Header derive.sym.db.
Elpi Accumulate Db derive.sym.db.
Elpi Accumulate derive File common.
Elpi Accumulate derive File utils.  
Elpi Accumulate derive File symK.

Elpi Accumulate derive lp:{{

dep1 "symK" "param2".
dep1 "symK" "sym".
derivation (indt T) Prefix ff (derive "symK" (derive.symK.main T Prefix) (symK-done T)).

}}.

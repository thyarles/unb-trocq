From elpi.apps.derive.elpi Extra Dependency "injection.elpi" as injection.
From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From elpi.apps.derive.elpi Extra Dependency "derive_synterp_hook.elpi" as derive_synterp_hook.
From Trocq.Algo Extra Dependency "injection_lemmas.elpi" as injections.
From Trocq.Algo Extra Dependency "utils.elpi" as algo_utils.

From elpi Require Import elpi.
From elpi.apps Require Import derive.bcongr. (* for eq_f register *) 
From elpi.apps Require Import projK. 
Unset Uniform Inductive Parameters. 
Elpi Db derive.injections.db lp:{{

  % [injections I K ILs] links I, 
  %  constructor inductive type, 
  %  and K, 
  %  a natural number > 0 (representing the constructor number)
  %  with the list of injection lemmas for that constructor
  pred injections-db i:term, i:int, o:term.

  % [injections-done T K] means T K was already derived
  pred injections-done o:term. 
}}.

Elpi Command derive.injections.
Elpi Accumulate File derive_hook.
Elpi Accumulate Db Header derive.projK.db.
Elpi Accumulate Db derive.projK.db.
Elpi Accumulate File injection.
Elpi Accumulate Db derive.injections.db.
Elpi Accumulate File algo_utils.
Elpi Accumulate File injections.
Elpi Accumulate lp:{{
  
  main [str I] :- !, 
    coq.locate I (indt GR),
    % Ind is (indt GR)
    coq.gref->id (indt GR) Tname,
    Suffix is Tname ^ "_",
    derive.injections.main GR Suffix _.
  main _ :- usage.

  pred usage.
  usage :- coq.error "Usage: derive.injections <object name>".
}}. 


From elpi.apps.derive.elpi Extra Dependency "injection.elpi" as injection.
From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From elpi.apps.derive.elpi Extra Dependency "derive_synterp_hook.elpi" as derive_synterp_hook.
From Trocq.Elpi.inductives Extra Dependency "injection_lemmas.elpi" as injections.
From Trocq.Elpi.inductives Extra Dependency "utils.elpi" as algo_utils.

From elpi.apps Require Export derive.
From elpi.apps Require Export derive.projK. 
From Trocq Require Export DeriveLib.

Unset Uniform Inductive Parameters. 
Unset Universe Minimization ToSet.
Elpi Db derive.injections.db lp:{{

  % [injections I K ILs] links I, 
  %  constructor inductive type, 
  %  and K, 
  %  a natural number > 0 (representing the constructor number)
  %  with the list of injection lemmas for that constructor
  pred injections-db i:term, i:int, o:term.
  pred injections-def i:gref, i:int, o:gref.

  % [injections-done T K] means T K was already derived
  pred injections-done o:inductive. 
}}.

Elpi Command derive.injections.
Elpi Accumulate Db Header derive.projK.db.
Elpi Accumulate Db Header derive.injections.db.
Elpi Accumulate File derive_hook.
Elpi Accumulate File injection.
Elpi Accumulate File algo_utils.
Elpi Accumulate File injections.
Elpi Accumulate Db derive.projK.db.
Elpi Accumulate Db derive.injections.db.
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

#[superglobal] Elpi Accumulate derive.injections.db lp:{{ 

  injections-db K N R :-
    coq.env.global (indc GRK) K,
    injections-def (indc GRK) N GRR,
    coq.env.global GRR R.

}}.

(* hook into derive *)
Elpi Accumulate derive File injection.
Elpi Accumulate derive File algo_utils.
Elpi Accumulate derive File injections.
Elpi Accumulate derive Db derive.injections.db.

Elpi Accumulate derive lp:{{

dep1 "injections" "projK".
derivation (indt T) Prefix ff (derive "injections" (derive.injections.main T Prefix) (injections-done T)).

}}.

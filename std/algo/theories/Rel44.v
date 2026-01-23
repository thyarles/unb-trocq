From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From elpi.apps.derive.elpi Extra Dependency "derive_synterp_hook.elpi" as derive_synterp_hook.
From Trocq Extra Dependency "algo/elpi/common_algo.elpi" as common. (* TODO: check if common/utils is used in rsymK *)
From Trocq Extra Dependency "algo/elpi/utils.elpi" as utils.  
From Trocq Extra Dependency "algo/elpi/rel44.elpi" as rel44.
From Trocq Require Import sym symK RsymK Param_lemmas umap map4. 
Import HoTTNotations.
(* Extra Dependency "algo/elpi/sym.elpi" as sym.  *)

From elpi.apps Require Import derive.legacy derive.param2.

From Trocq Require Export Hierarchy.
Unset Uniform Inductive Parameters. 

Elpi Db derive.rel44.db lp:{{

  % [rel44 I S] links I inductive type, 
  %  with the function showing i1 i2, [| I |]^ i2 i1 <->> [| I |] i1 i2
  pred rel44-db i:term, o:term.

  % [rel44-done T K] means T K was already derived
  pred rel44-done o:inductive. 
}}.

Elpi Command derive.rel44.
Elpi Accumulate File derive_hook.
Elpi Accumulate Db Header derive.param2.db.
Elpi Accumulate Db derive.param2.db.
Elpi Accumulate Db Header derive.rsymK.db.
Elpi Accumulate Db derive.rsymK.db.
Elpi Accumulate Db Header derive.umap.db.
Elpi Accumulate Db derive.umap.db.
Elpi Accumulate File common.  
Elpi Accumulate File utils. 
Elpi Accumulate Db Header derive.rel44.db.
Elpi Accumulate Db derive.rel44.db.

Elpi Query lp:{{ 
  T = {{:gref Param44.covariant }}, 
  coq.say (pglobal T _).
}}.
Elpi Accumulate File rel44.
Elpi Accumulate lp:{{
  
  main [str I] :- !, 
    coq.locate I (indt GR),
    % Ind is (indt GR)
    coq.gref->id (indt GR) Tname,
    Suffix is Tname ^ "_",
    derive.rel44.main GR Suffix _.
  main _ :- usage.

  pred usage.
  usage :- coq.error "Usage: derive.rel44 <object name>".
}}. 

(* hook into derive *)
Elpi Accumulate derive Db Header derive.rel44.db.
Elpi Accumulate derive Db derive.rel44.db.
Elpi Accumulate Db Header derive.rsymK.db.
Elpi Accumulate Db derive.rsymK.db.
Elpi Accumulate Db Header derive.umap.db.
Elpi Accumulate Db derive.umap.db.
Elpi Accumulate derive File common.
Elpi Accumulate derive File utils.  
Elpi Accumulate derive File rel44.
Elpi Accumulate derive lp:{{

dep1 "rel44" "rsymK".
dep1 "rel44" "umap".
derivation (indt T) Prefix ff (derive "rel44" (derive.rel44.main T Prefix) (rel44-done T)).

}}.

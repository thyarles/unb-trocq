From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From Trocq.Elpi Extra Dependency "inductives/mapn.elpi" as mapn.
From Trocq.Elpi Extra Dependency "inductives/common_algo.elpi" as common.
From Trocq.Elpi Extra Dependency "inductives/utils.elpi" as algo_utils.
From Trocq Require Import Database map4.
Unset Uniform Inductive Parameters. 

(* I have to use Trocq db due to a dependency of type declaration of predicates in umap-db *)
(* if the class file is accumulated in umap-db then accumulating trocq.db is an issue *)
(* Elpi Db derive.umap.db lp:{{ }}. 
Elpi Accumulate derive.umap.db Db trocq.db. *)
(* Elpi Accumulate derive Db trocq.db. *)
(* Elpi Db derive.umap.db lp:{{
  % [umap-db T D]
  pred umap-db i:term, i:map-class, o:term.

  % [umap-done T D]
  pred umap-done o:inductive, o:map-class.
}}. *)

Elpi Command derive.mapn.
Elpi Accumulate File derive_hook.
Elpi Accumulate Db Header derive.param2.db.
Elpi Accumulate Db derive.param2.db.
Elpi Accumulate Db Header derive.mymap.db.
Elpi Accumulate Db derive.mymap.db.
Elpi Accumulate Db Header derive.mR.db.
Elpi Accumulate Db derive.mR.db.
Elpi Accumulate Db Header derive.Rm.db.
Elpi Accumulate Db derive.Rm.db.
Elpi Accumulate Db Header derive.mRRmK.db.
Elpi Accumulate Db derive.mRRmK.db.
Elpi Accumulate File common.
Elpi Accumulate File algo_utils.

Elpi Accumulate Db trocq.db.
Elpi Accumulate File mapn.
Elpi Accumulate lp:{{
  main [str I] :- !, coq.locate I (indt GR),
    coq.gref->id (indt GR) Tname,
    Prefix is Tname ^ "_",
    derive.mapn.main GR Prefix _.
  main _ :- usage.

  pred usage.
  usage :- coq.error "Usage: derive.rel40 <object name>".
}}. 

Elpi Accumulate derive Db trocq.db.
Elpi Accumulate derive File common.
Elpi Accumulate derive File algo_utils.
Elpi Accumulate derive File mapn.

Elpi Accumulate derive lp:{{

dep1 "mapn" "mRRmK".
derivation (indt T) Prefix ff (derive "mapn" (derive.mapn.main T Prefix) (trocq.db.map-ind-done T)).

}}.

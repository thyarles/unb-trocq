From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From Trocq Extra Dependency "algo/elpi/rel40.elpi" as Rel40.
From Trocq Extra Dependency "algo/elpi/common_algo.elpi" as common.
From Trocq Extra Dependency "algo/elpi/utils.elpi" as algo_utils.
From Trocq Require Import map4 umap.


Unset Uniform Inductive Parameters. 

(* todo: this function could be used in umap derivation  *)
Definition Build40 (A B : Type) (R : A -> B -> Type) (UR : IsUMap R) : Param40.Rel A B :=
(@Param40.BuildRel _ _ R UR (@Map0.BuildHas _ _ (@sym_rel A B R))). 

Elpi Db derive.rel40.db lp:{{
  % [rel40-db T D] links a type T to its corresponding Rel40.
  pred rel40-db i:term, o:term.

  % [rel40-done T] mean T was already derived
  pred rel40-done o:inductive.
}}.

Elpi Command derive.Rel40.
Elpi Accumulate File derive_hook.
(* Elpi Accumulate Db Header derive.param2.db.
Elpi Accumulate Db derive.param2.db.
Elpi Accumulate Db Header derive.mymap.db.
Elpi Accumulate Db derive.mymap.db.
Elpi Accumulate Db Header derive.mR.db.
Elpi Accumulate Db derive.mR.db.
Elpi Accumulate Db Header derive.Rm.db.
Elpi Accumulate Db derive.Rm.db.
Elpi Accumulate Db Header derive.mRRmK.db.
Elpi Accumulate Db derive.mRRmK.db. *)
Elpi Accumulate Db Header derive.umap.db.
Elpi Accumulate Db derive.umap.db.
Elpi Accumulate File common.
Elpi Accumulate File algo_utils.

Elpi Accumulate Db derive.rel40.db.
Elpi Accumulate File Rel40.
Elpi Accumulate lp:{{
  main [str I] :- !, coq.locate I (indt GR),
    coq.gref->id (indt GR) Tname,
    Prefix is Tname ^ "_",
    derive.rel40.main GR Prefix _.
  main _ :- usage.

  pred usage.
  usage :- coq.error "Usage: derive.rel40 <object name>".
}}. 


Elpi Accumulate derive Db derive.rel40.db.
Elpi Accumulate derive File common.
Elpi Accumulate derive File algo_utils.
Elpi Accumulate derive File Rel40.

Elpi Accumulate derive lp:{{

dep1 "rel40" "umap".
derivation (indt T) Prefix ff (derive "rel40" (derive.rel40.main T Prefix) (rel-done T)).

}}.


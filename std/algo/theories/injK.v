
From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From Trocq Extra Dependency "algo/elpi/injK.elpi" as injK.
From Trocq Extra Dependency "algo/elpi/utils.elpi" as algo_utils.
From Trocq Require Export injection_lemmas. 

From elpi Require Import elpi.
From elpi.apps Require Export derive.bcongr. (* for eq_f register *) 
(* From Trocq Require Export Rm. *)

From Trocq Require Import Hierarchy.
(* From Trocq Require Import HoTT_additions Hierarchy. *)
Unset Uniform Inductive Parameters. 

Definition conv (A : Type) (x y : A) (p: x = y) 
    (P : forall x0 : A, x = x0 -> Prop) (P0 : P x eq_refl) :=
  match p as p0 in _ = t return (P t p0)
   with eq_refl => P0 end.

Register conv as elpi.derive.conv.

Elpi Db derive.injectionsK.db lp:{{

  % [injectionsK-db I K ILs] links I, 
  %  constructor inductive type, 
  %  and K, 
  %  a natural number > 0 (representing the constructor number)
  %  with the list of injectionK lemmas for that constructor
  pred injectionsK-db i:term, i:int, o:term.

  % [injectionsK-done T K] means T K was already derived
  pred injectionsK-done o:inductive. 
}}.

Elpi Command derive.injK.
Elpi Accumulate File derive_hook.
Elpi Accumulate File algo_utils.
Elpi Accumulate Db derive.injectionsK.db.
Elpi Accumulate Db derive.injections.db.
Elpi Accumulate File injK.
Elpi Accumulate lp:{{
  main [str I] :- !, coq.locate I (indt GR),
    coq.gref->id (indt GR) Tname,
    Prefix is Tname ^ "_",
    derive.injK.main GR Prefix _.
  main _ :- usage.

  pred usage.
  usage :- coq.error "Usage: derive.Rm <object name>".
}}. 

(* hook into derive *)
Elpi Accumulate derive Db derive.injectionsK.db.
Elpi Accumulate derive File algo_utils.
Elpi Accumulate derive File injK.

Elpi Accumulate derive lp:{{

dep1 "injK" "injections".
derivation (indt T) Prefix ff (derive "injK" (derive.injK.main T Prefix) (injectionsK-done T)).

}}.



From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From Trocq.Algo Extra Dependency "injK.elpi" as injK.
From Trocq.Algo Extra Dependency "utils.elpi" as algo_utils.
From Trocq.Algo Require Import injection_lemmas. 

From elpi Require Import elpi.
From elpi.apps Require Import derive.bcongr. (* for eq_f register *) 
(* From elpi.apps Require Import projK.  *)

From Trocq Require Import HoTT_additions Hierarchy.
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
  pred injectionsK-done o:term. 
}}.

Elpi Command derive.injectionsK.
Elpi Accumulate File derive_hook.
Elpi Accumulate File algo_utils.
Elpi Accumulate Db derive.injectionsK.db.
Elpi Accumulate Db derive.injections.db.
Elpi Accumulate File injK.
(* Elpi Query lp:{{ 
  %std.nth 0 {std.iota 5} L.
  R = {{lib:@elpi.derive.conv}}.
}}. *)
Elpi Accumulate lp:{{
  main [str I] :- !, coq.locate I (indt GR),
    coq.gref->id (indt GR) Tname,
    Prefix is Tname ^ "_",
    derive.injK.main GR Prefix _.
  main _ :- usage.

  pred usage.
  usage :- coq.error "Usage: derive.Rm <object name>".
}}. 

From Trocq.Tests Require Import coverage.
Elpi derive.projK Box.
Elpi derive.injections Box.
Elpi derive.injectionsK Box.
Elpi derive.projK WrapMore.
Elpi derive.injections WrapMore.
Elpi derive.injectionsK WrapMore.
Elpi derive.projK List.
Elpi derive.injections List.
Elpi derive.injectionsK List.

From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From Trocq.Elpi.inductives Extra Dependency "injK.elpi" as injK.
From Trocq Require Export injection_lemmas. 

From Trocq Require Import DeriveLib HoTTNotations Stdlib Hierarchy.

Unset Uniform Inductive Parameters. 
Unset Universe Minimization ToSet.

Unset Universe Polymorphism.
Definition conv (A : Type) (x y : A) (p: x = y) 
    (P : forall x0 : A, x = x0 -> Type) (P0 : P x idpath) :=
  match p as p0 in _ = t return (P t p0)
   with idpath => P0 end.
Register conv as trocq.conv.
Set Universe Polymorphism.

Elpi Db derive.injectionsK.db lp:{{

  % [injectionsK-db I K ILs] links I, 
  %  constructor inductive type, 
  %  and K, 
  %  a natural number > 0 (representing the constructor number)
  %  with the list of injectionK lemmas for that constructor
  pred injectionsK-db i:term, i:int, o:term.
  pred injectionsK-def i:gref, i:int, o:gref.

  % [injectionsK-done T K] means T K was already derived
  pred injectionsK-done o:inductive. 
}}.

Elpi Command derive.injK.
Elpi Accumulate Db Header derive.injections.db.
Elpi Accumulate Db Header derive.injectionsK.db.
Elpi Accumulate File derive_hook.
Elpi Accumulate File injK.
Elpi Accumulate Db derive.injections.db.
Elpi Accumulate Db derive.injectionsK.db.
Elpi Accumulate lp:{{
  main [str I] :- !, coq.locate I (indt GR),
    coq.gref->id (indt GR) Tname,
    Prefix is Tname ^ "_",
    derive.injK.main GR Prefix _.
  main _ :- usage.

  pred usage.
  usage :- coq.error "Usage: derive.Rm <object name>".
}}. 

#[superglobal] Elpi Accumulate derive.injectionsK.db lp:{{ 

  injectionsK-db K N R :-
    coq.env.global (indc GRK) K,
    injectionsK-def (indc GRK) N GRR,
    coq.env.global GRR R.

}}.

(* hook into derive *)
Elpi Accumulate derive File injK.
Elpi Accumulate derive Db derive.injectionsK.db.

Elpi Accumulate derive lp:{{

dep1 "injK" "injections".
derivation (indt T) Prefix ff (derive "injK" (derive.injK.main T Prefix) (injectionsK-done T)).

}}.

From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From Trocq.Elpi Extra Dependency "inductives/mymap.elpi" as mymap.

From elpi Require Import elpi.
From elpi.apps Require Import derive.
From Trocq Require Export Stdlib Hierarchy.
Unset Uniform Inductive Parameters. 

Elpi Db derive.mymap.db lp:{{
  % [mymap-def I C] brings the constant defined for mapping inductive I.
  pred mymap-def i:gref, o:gref.

  % [mymap T1 T2 D] for T1 and T2 brings a map D from T1 to T2. 
  pred mymap-db i:term, i:term, o:term.

  % [mymap-done T] mean T was already derived
  pred mymap-done o:inductive.
}}.

Elpi Command derive.mymap.
Elpi Accumulate File derive_hook.
Elpi Accumulate Db derive.mymap.db.
Elpi Accumulate File mymap.
Elpi Accumulate lp:{{
  main [str I] :- !, 
    coq.locate I (indt GR),
    coq.gref->id (indt GR) Tname,
    Prefix is Tname ^ "_",
    %derive.mymap.main GR Prefix _.

    % derive.mymap.mk-map-ty A _ B _ {{ Param10.Rel lp:A lp:B }} F 0 [mymap-db A B F] =>
    % (derive.mymap.bo-k-args.aux K [A|As] [T|Ts] (prod _ S Ty) R :-
    % mymap-db T S FRel,
    % coq.mk-app {{ map }} [FRel] F,
    % coq.mk-app F [A] FA,
    % bo-k-args.aux {coq.mk-app K [FA]} As Ts (Ty FA) R) =>

    derive.mymap.main GR Prefix _.
  main _ :- usage.

  pred usage.
  usage :- coq.error "Usage: derive.mymap <object name>".
}}. 

(* hook into derive *)
Elpi Accumulate derive Db derive.mymap.db.
Elpi Accumulate derive File mymap.

Elpi Accumulate derive lp:{{

derivation (indt T) Prefix ff (derive "mymap" (derive.mymap.main T Prefix) (mymap-done T)).

}}.

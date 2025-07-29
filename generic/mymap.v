From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From Trocq Extra Dependency "mymap.elpi" as mymap.

From elpi Require Import elpi.
From elpi.apps Require Import derive.
From Trocq Require Import Hierarchy.
Unset Uniform Inductive Parameters. 

Elpi Db derive.mymap.db lp:{{
  % [mymap-def I C] brings the constant defined for mapping inductive I.
  pred mymap-def i:inductive, o:term.

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

Elpi derive.mymap option.
Print option_mymap.

Elpi derive.mymap list.
Print list_mymap.

Elpi derive.mymap prod.
Print prod_mymap.

Elpi derive.mymap nat.
Print nat_mymap.

Inductive ThreeTypes (A B C : Type) :=
| C1 : A -> ThreeTypes A B C
| C2 : B -> ThreeTypes A B C
| C3 : C -> ThreeTypes A B C.

Elpi derive.mymap ThreeTypes.
Print ThreeTypes_mymap.

Elpi Query lp:{{
    coq.locate "option" (indt Option),
    std.findall (mymap-def Option _) Rules. % empty
    %std.findall (mymap-db {{ option nat }} {{ option nat }} _) Rules. % non empty
    %std.findall (mymap-db {{ nat }} {{ nat }} _) Rules. % non empty
    std.findall (mymap-db {{ nat }} B C) Rules. % empty
    std.findall (mymap-db A B C) Rules. % empty
    std.findall (mymap-done _) Rules. % empty

}}.

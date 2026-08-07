From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From Trocq.Elpi.inductives Extra Dependency "mymap.elpi" as mymap.

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
Elpi Accumulate Db Header derive.mymap.db.
Elpi Accumulate File derive_hook.
Elpi Accumulate File mymap.
Elpi Accumulate Db derive.mymap.db.
Elpi Accumulate lp:{{
  main [str I] :- !, 
    coq.locate I (indt GR),
    coq.gref->id (indt GR) Tname,
    Prefix is Tname ^ "_",

    derive.mymap.main GR Prefix _.
  main _ :- usage.

  pred usage.
  usage :- coq.error "Usage: derive.mymap <object name>".
}}. 

(* hook into derive *)
Elpi Accumulate derive Db Header derive.mymap.db.
Elpi Accumulate derive File mymap.
Elpi Accumulate derive Db derive.mymap.db.

Elpi Accumulate derive lp:{{

derivation (indt T) Prefix ff (derive "mymap" (derive.mymap.main T Prefix) (mymap-done T)).

}}.

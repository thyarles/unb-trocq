From elpi.apps.derive.elpi Extra Dependency "injection.elpi" as injection.
From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From elpi.apps.derive.elpi Extra Dependency "derive_synterp_hook.elpi" as derive_synterp_hook.
From Trocq.Algo Extra Dependency "injection_lemmas.elpi" as injections.

From elpi Require Import elpi.
From elpi.apps Require Import derive.bcongr. (* for eq_f register *) 
From elpi.apps Require Import projK. 
Unset Uniform Inductive Parameters. 
Elpi Db derive.injections.db lp:{{

  % [injections I K ILs] links I, 
  %  constructor inductive type, 
  %  and K, 
  %  a natural number > 0 (representing the constructor number)
  %  with the list of injection lemmas for that constructor
  pred injections-db i:term, i:int, o:term.

  % [injections-done T K] means T K was already derived
  pred injections-done o:term. 
}}.

Elpi Command derive.injections.
Elpi Accumulate File derive_hook.
Elpi Accumulate Db Header derive.projK.db.
Elpi Accumulate Db derive.projK.db.
Elpi Accumulate File injection.
Elpi Accumulate Db derive.injections.db.
Elpi Accumulate File injections.
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
Elpi Trace Browser.

Inductive Wrap : Type :=
| W : unit -> Wrap.
Elpi derive.projK Wrap.
Print projW1.
Elpi derive.injections Wrap.
Print Wrap_injections11.

Elpi derive.projK nat.
Elpi derive.injections nat.
Print nat_injections21.

Elpi derive.projK option.
Print projSome1.
Elpi derive.injections option.
Print option_injections11.

Inductive enum : Type :=
| Constructor : unit -> bool -> enum.

Elpi derive.projK enum.
Print projConstructor1.
Print projConstructor2.
Elpi derive.injections enum.
Print enum_injections11.
Print enum_injections12.

Inductive enum2 : Type :=
| Nol : enum2
| Constructor2 : unit -> bool -> enum2.

Elpi derive.projK enum2.
Print projConstructor21.
Print projConstructor22.
Elpi derive.injections enum2.
Print enum2_injections21.
Print enum2_injections22.

Inductive Losts (T : Prop) : Prop :=
| Conse : Losts T -> Losts T .

Elpi derive.projK Losts.
Print projConse1.
Elpi derive.injections Losts.
Print Losts_injections11.

Elpi derive.projK list.
Print projcons1.
Print projcons2.
Elpi derive.injections list.
Print list_injections21.
Print list_injections22.

Elpi Query lp:{{
    std.findall (injections-db _ _ _) Rules.
    std.findall (injections-done _) Rules.
    std.findall (projK-db _ _ _) Rules.
}}. 

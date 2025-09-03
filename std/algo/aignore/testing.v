From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
(* From elpi.apps.derive.elpi Extra Dependency "injection.elpi" as inject. *)
(* From elpi.apps.derive.elpi Extra Dependency "bcongr.elpi" as bcongr. *)
From elpi.apps.derive.elpi Extra Dependency "discriminate.elpi" as discr.
From elpi Require Import elpi.
From elpi Require Import derive derive.bcongr derive.eqK derive.isK.

(* use elpi.rewrite to implement
 forall n m, n = m -> S n = S m.
*)
(* build a function of type forall n1, n1 = 0 -> n1 = 0.
implementing it by case on n1.
O => eq_refl
S n => discriminate. *)
Elpi Command test4.
Elpi Accumulate File discr.
Elpi Accumulate Db derive.isK.db.
Elpi Accumulate lp:{{

    pred mkty i:(term -> term), i:term, i:list term, i:list term, o:term.
    mkty Bo _ Ts _ (Bo X):-
      std.last Ts X.

    pred mkBranch i:(term -> term), i:term, i:term, i:term, i:list term, i:list term, o:term.
    mkBranch _ K T _ _ _ {{ fun e => eq_refl }} :-
      coq.safe-dest-app T K _, !.
    mkBranch ((n\ prod (En n) (ETy n) (G n))) _ T _ Ts _ (fun (En Curr) (ETy Curr) e\ (R e)) :-
      coq.mk-app T Ts Curr,
      coq.elaborate-skeleton (ETy Curr) _ ETyE _,
      pi e\
        sigma GE\
        coq.elaborate-skeleton (G Curr e) _ GE _,
        ltac.discriminate e ETyE GE (R e).

    % given the type build the function
    % Bo n1 = n1 = 0 -> n1 = 0
    pred build i: term, o:term.
    build (prod N1 {{nat}} n1\ (Bo n1))
          (fun N1  {{nat}} n1\ (R n1)) :-
      @pi-decl N1 {{ nat }} n1\
        coq.build-match n1 {{ nat }} {{ _ }} (mkBranch Bo {{ 0 }}) (R n1).

    main _ :-
      RTy = {{ forall (n1 : nat), n1 = 0 -> n1 = 0 }},
      build RTy R,
      FName is "def4",
      coq.elaborate-skeleton R RTy RE _,
      coq.env.add-const FName RE _ _ _.

}}.
Elpi derive.isK nat.
Elpi Query lp:{{
   main R.
}}.
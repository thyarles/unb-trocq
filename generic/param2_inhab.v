(* Given an inductive type I and its unary parametricity translation is_ it
   generates a proof of 
     forall i : I, is_U i
   and then a proof of
     forall i : I, { p : is_I i & forall q, p = q }.

   license: GNU Lesser General Public License Version 2.1 or later
   ------------------------------------------------------------------------- *)
From elpi.apps.derive.elpi Extra Dependency "paramX_lib.elpi" as paramX.
From elpi.apps.derive.elpi Extra Dependency "param2.elpi" as param2.
(* From elpi.apps.derive.elpi Extra Dependency "param1_inhab.elpi" as param1_inhab. *)
From Trocq Extra Dependency "param2_inhab.elpi" as param2_inhab.
From Trocq Extra Dependency "param2_trivial.elpi" as param2_trivial.
From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From elpi.apps.derive.elpi Extra Dependency "derive_synterp_hook.elpi" as derive_synterp_hook.

From elpi Require Import elpi.
From elpi.apps Require Import derive.param1 derive.param2 derive.param1_trivial.

Definition full2 T1 T2 P := forall (x : T1)(y : T2), P x y.
Register full2 as elpi.derive.full2.

Definition full2self T P := forall (x : T), P x x.
Register full2self as elpi.derive.full2self.

Definition contracts2self T P (x : T) w u := (@existT (P x x) (fun u : P x x=> forall v : P x x,@eq (P x x) u v) w u).
About contracts2self.
Register contracts2self as elpi.derive.contracts2self.

  Elpi Db derive.param2.trivial.db lp:{{

  pred param2-trivial-done i:inductive.
  type param2-trivial-db term -> term -> prop.
  type param2-trivial-db-args list term -> list term -> prop.

  pred param2-inhab-done i:inductive.
  type param2-inhab-db term -> term -> prop.
  type param2-inhab-db-args list term -> list term -> prop.

}}.
#[superglobal] Elpi Accumulate derive.param2.trivial.db File derive.lib.
#[superglobal] Elpi Accumulate derive.param2.trivial.db Db Header derive.param2.db.
#[superglobal] Elpi Accumulate derive.param2.trivial.db lp:{{

  :name "param2:inhab:start"
  param2-inhab-db 
            (fun `f` (prod `_` S _\ T) f\
              prod `x` S x\ prod `px` (RS x) _)
            (fun `f` (prod `_` S _\ T) f\
              fun `x` S x\
                fun `px` (RS x) _\ P f x) :-
            pi f x\
              param T T R,
              param2-inhab-db R PT,
              coq.mk-app PT [{coq.mk-app f [x]}] (P f x).

  param2-inhab-db (app [Hd|Args]) (app[P|PArgs]) :-
    param2-inhab-db Hd P, !,
    param2-inhab-db-args Args PArgs.
  
  param2-inhab-db-args [] [].
  param2-inhab-db-args [T,P|Args] R :-
    std.assert-ok! (coq.typecheck T Ty) "param2-inhab-db: cannot work illtyped term",
    if (coq.sort? Ty)
       (param2-inhab-db P Q, R = [T,P,Q|PArgs], param2-inhab-db-args Args PArgs)
       (R = [T,P|PArgs], param2-inhab-db-args Args PArgs).
   
  :name "param2:trivial:start"
  param2-trivial-db (fun `f` (prod `_` S _\ T) f\
              prod `x` S x\ prod `px` (RS x) _)
            (fun `f` (prod `_` S _\ T) f\
              fun `x` S x\
                fun `px` (RS x) _\ P f x) :-
            pi f x\
              param T T R,
              param2-trivial-db R PT,
              coq.mk-app PT [{coq.mk-app f [x]}] (P f x).

  param2-trivial-db (app [Hd|Args]) (app[P|PArgs]) :-
    param2-trivial-db Hd P, !,
    param2-trivial-db-args Args PArgs.

  param2-trivial-db-args [] [].
  param2-trivial-db-args [T,P|Args] R :-
    std.assert-ok! (coq.typecheck T Ty) "param2-trivial-db: cannot work on illtyped term",
    if (coq.sort? Ty)
      (param2-trivial-db P Q, R = [T,P,Q|PArgs], param2-trivial-db-args Args PArgs)
      (R = [T,P|PArgs], param2-trivial-db-args Args PArgs).

}}.
  

(* standalone *)
Elpi Command derive.param2.trivial.
Elpi Accumulate File derive_hook.
Elpi Accumulate File paramX.
Elpi Accumulate File param2.
Elpi Accumulate Db derive.param2.db.
(* Elpi Accumulate Db derive.param2.congr.db. *)
Elpi Accumulate Db derive.param2.trivial.db.
Elpi Accumulate File param2_inhab.
Elpi Accumulate File param2_trivial.
Elpi Accumulate lp:{{
  main [str I] :- !, coq.locate I (indt GR),
    derive.param2.inhab.main GR "_inhab" CL,
    CL => derive.param2.trivial.main GR "_trivial" _.
  main _ :- usage.

  usage :-
    coq.error "Usage: derive.param2.trivial <inductive type name>".
}}.


Elpi Command derive.param2.inhab.
Elpi Accumulate File derive_hook.
Elpi Accumulate File paramX.
Elpi Accumulate File param2.
Elpi Accumulate Db derive.param2.db.
(* Elpi Accumulate Db derive.param1.congr.db. *)
Elpi Accumulate Db derive.param2.trivial.db.
Elpi Accumulate File param2_inhab.
Elpi Accumulate lp:{{
  main [str I] :- !, coq.locate I (indt GR),
    derive.param2.inhab.main GR "_inhab" _.
  main _ :- usage.

  usage :-
    coq.error "Usage: derive.param2.inhab <inductive type name>".
}}.

(* ad-hoc rules for primitive data, eq and is_true *)

(* Module Export exports.
Elpi derive.param2.trivial is_bool.
End exports. *)

Definition is_uint63_inhab x : is_uint63 x. Proof. constructor. Defined.
Register is_uint63_inhab as elpi.derive.is_uint63_inhab.

Definition is_float64_inhab x : is_float64 x. Proof. constructor. Defined.
Register is_float64_inhab as elpi.derive.is_float64_inhab.

Definition is_pstring_inhab s : is_pstring s. Proof. constructor. Defined.
Register is_pstring_inhab as elpi.derive.is_pstring_inhab.

Definition is_eq_inhab
  A (PA : A -> Type) (HA : trivial A PA) (x : A) (px: PA x) y (py : PA y) (eq_xy : x = y) :
    is_eq A PA x px y py eq_xy.
Proof.
  revert py.
  case eq_xy; clear eq_xy y.
  intro py.
  rewrite <- (trivial_uniq A PA HA x px); clear px.
  rewrite <- (trivial_uniq A PA HA x py); clear py.
  apply (is_eq_refl A PA x (trivial_full A PA HA x)).
Defined.
Register is_eq_inhab as elpi.derive.is_eq_inhab.

(* Definition is_true_inhab b (H : is_bool b) p : is_is_true b H p :=
  is_eq_inhab bool is_bool is_bool_trivial b H true is_true p.
Register is_true_inhab as elpi.derive.is_true_inhab. *)


(* Elpi Accumulate derive.param2.trivial.db lp:{{

  :before "param2:inhab:start"
  param2-inhab-db {{ lib:elpi.derive.is_uint63 }} {{ lib:elpi.derive.is_uint63_inhab }}.
  :before "param2:inhab:start"
  param2-inhab-db {{ lib:elpi.derive.is_float64 }} {{ lib:elpi.derive.is_float64_inhab }}.
  :before "param2:inhab:start"
  param2-inhab-db {{ lib:elpi.derive.is_pstring }} {{ lib:elpi.derive.is_pstring_inhab }}.
  :before "param2:inhab:start"
  param2-inhab-db {{ lib:elpi.derive.is_eq }} {{ lib:elpi.derive.is_eq_inhab }}.
  :before "param2:inhab:start"
  param2-inhab-db {{ lib:elpi.derive.is_true }} {{ lib:elpi.derive.is_true_inhab }}.


  :before "param2:inhab:start"
  param2-inhab-db
    {{ lib:elpi.derive.is_eq lp:A lp:PA lp:X lp:PX lp:Y lp:PY }}
    {{ lib:elpi.derive.is_eq_inhab lp:A lp:PA lp:QA lp:X lp:PX lp:Y lp:PY }} :- !,
    param2-trivial-db PA QA.

  :before "param2:inhab:start"
  param2-inhab-db {{ lib:elpi.derive.is_is_true lp:B lp:PB }} R :- !,
    param2-inhab-db {{ lib:elpi.derive.is_eq lib:elpi.bool lib:elpi.derive.is_bool lp:B lp:PB lib:elpi.true lib:elpi.derive.is_true }} R.

}}. *)


Definition is_uint63_trivial : trivial PrimInt63.int is_uint63 :=
  fun x => contracts _ is_uint63 x (is_uint63_inhab x)
    (fun y => match y with uint63 i => eq_refl end).
Register is_uint63_trivial as elpi.derive.is_uint63_trivial.
  
Definition is_float64_trivial : trivial PrimFloat.float is_float64 :=
  fun x => contracts _ is_float64 x (is_float64_inhab x)
    (fun y => match y with float64 i => eq_refl end).
Register is_float64_trivial as elpi.derive.is_float64_trivial.

(* Definition is_pstring_trivial : trivial lib:elpi.pstring is_pstring :=
  fun x => contracts _ is_pstring x (is_pstring_inhab x)
    (fun y => match y with pstring i => eq_refl end).
Register is_pstring_trivial as elpi.derive.is_pstring_trivial. *)

Lemma is_eq_trivial A (PA : A -> Type) (HA : trivial A PA) (x : A) (px: PA x) 
   y (py : PA y)
  : trivial (x = y) (is_eq A PA x px y py).
Proof.
  intro p.
  apply (contracts (x = y) (is_eq A PA x px y py) p (is_eq_inhab A PA HA x px y py p)).
  revert py.
  case p; clear p y.
  rewrite <- (trivial_uniq _ _ HA x px). clear px.
  intros py.
  rewrite <- (trivial_uniq _ _ HA x py). clear py.
  intro v; case v; clear v.
  unfold is_eq_inhab.
  unfold trivial_full.
  unfold trivial_uniq.
  case (HA x); intros it def_it; compute.
  case (def_it it).
  reflexivity.
Defined.
Register is_eq_trivial as elpi.derive.is_eq_trivial.

(* Definition is_true_trivial b (H : is_bool b) : trivial (lib:elpi.is_true b) (is_is_true b H) :=
  is_eq_trivial bool is_bool is_bool_trivial b H true is_true.
Register is_true_trivial as elpi.derive.is_true_trivial. *)


Elpi Accumulate derive.param2.trivial.db lp:{{

  :before "param2:trivial:start"
  param2-trivial-db {{ lib:elpi.derive.is_uint63 }} {{ lib:elpi.derive.is_uint63_trivial }}.
  :before "param2:trivial:start"
  param2-trivial-db {{ lib:elpi.derive.is_float64 }} {{ lib:elpi.derive.is_float64_trivial }}.
  %:before "param2:trivial:start"
  %param2-trivial-db {{ lib:elpi.derive.is_pstring }} {{ lib:elpi.derive.is_pstring_trivial }}.
  :before "param2:trivial:start"
  param2-trivial-db {{ lib:elpi.derive.is_eq }} {{ lib:elpi.derive.is_eq_trivial }}.
  %:before "param2:trivial:start"
  %param2-trivial-db {{ lib:elpi.derive.is_true }} {{ lib:elpi.derive.is_true_trivial }}.


  :before "param2:trivial:start"
  param2-trivial-db
    {{ lib:elpi.derive.is_eq lp:A lp:PA lp:X lp:PX lp:Y lp:PY }}
    {{ lib:elpi.derive.is_eq_trivial lp:A lp:PA lp:QA lp:X lp:PX lp:Y lp:PY }} :-
    param2-trivial-db PA QA.

  :before "param2:trivial:start"
  param2-trivial-db {{ lib:elpi.derive.is_is_true lp:B lp:PB }} R :- !,
    param2-trivial-db {{ lib:elpi.derive.is_eq lib:elpi.bool lib:elpi.derive.is_bool lp:B lp:PB lib:elpi.true lib:elpi.derive.is_true }} R.

}}.

(* hook into derive *)
Elpi Accumulate derive Db derive.param2.trivial.db.
Elpi Accumulate derive File param2_inhab.
(* Elpi Accumulate derive File param2_trivial. *)

#[phases="both"] Elpi Accumulate derive lp:{{
%dep1 "param2_trivial" "param2_inhab".
%dep1 "param2_trivial" "param2_congr".
dep1 "param2_inhab" "param2".
}}.

#[synterp] Elpi Accumulate derive lp:{{
  derivation _ _ (derive "param2_inhab" (cl\ cl = []) true).
  %derivation _ _ (derive "param2_trivial" (cl\ cl = []) true).
}}.

Elpi Accumulate derive lp:{{

derivation (indt T) _ ff (derive "param2_inhab"   (derive.on_param1 T derive.param2.inhab.main   "_inhab") (derive.on_param1 T (T\_\_\param2-inhab-done T) _ _)).
%derivation (indt T) _ ff (derive "param2_trivial" (derive.on_param1 T derive.param2.trivial.main "_trivial") (derive.on_param1 T (T\_\_\param2-trivial-done T) _ _)).

}}.

Elpi Export derive.param2.inhab. 

Module tests.
(* ========= *)
(* ENUM *)
(* ========= *)
Inductive empty :=.
Elpi derive.param1 empty.
Elpi derive.param2 empty.
Elpi derive.param1.trivial is_empty.
Print is_empty_trivial.
Definition wish : forall x : empty, {u : is_empty x & forall v : is_empty x, u = v}.
intros x.
refine (contracts empty is_empty x (is_empty_inhab x) _).
fix IH 1.
intros v.
refine (match v as i in (is_empty s1) return (is_empty_inhab s1 = i) with end).
Defined.
Elpi Trace Browser.
Fail Elpi derive.param2.trivial empty_R.
Print is_empty_trivial.
Elpi derive.param2.inhab empty_R. 
Check empty_R_inhab : forall x : empty, empty_R x x.
Print empty_R_inhab.

Elpi derive.param2 unit.
Elpi derive.param2.inhab unit_R.
Check unit_R_inhab : forall x : unit, unit_R x x.
Print unit_R_inhab.
Elpi derive.param1 unit.
Elpi derive.param1.trivial is_unit.
Print is_unit_trivial.
Definition wish2 : forall (x : unit), {u : is_unit x & forall v : is_unit x, u = v}.
Proof.
intros x. 
refine (contracts unit is_unit x (is_unit_inhab x) _).
fix IH 1.
intros v.
refine (match v as i in (is_unit s1) 
        return (is_unit_inhab s1 = i) 
        with | is_tt => eq_refl 
        end).
Defined.
Print wish2.
Elpi derive.param1 nat.
Elpi derive.param1.trivial is_nat.
Import EqNotations.
Print EqNotations.
Definition wish3 : forall (x : unit), {u : unit_R x x & forall v : unit_R x x, u = v}.
Proof.
intros x. 
refine (contracts2self unit unit_R x (unit_R_inhab x) _).
(* induction x. *)
fix IH 1.
intros v.
(* refine match v with (tt_R ) => _ end.  *)
Show Proof.
refine ((match v as i in (unit_R s1 s2) 
        return (forall (e : s2 = s1), (unit_R_inhab s1 = rew e in i))
        with | tt_R => fun e => match e with eq_refl =>  _ end 
        end) eq_refl).
Show Proof.
reflexivity.
Defined.
(* Unset Printing Notations. *)
(* Print wish3. *)

Elpi derive.param2 nat.
Elpi derive.param2.inhab nat_R.
Print is_nat_trivial.
Print trivial_uniq.

Definition wish4 : forall (x : nat), {u : nat_R x x & forall v : nat_R x x, u = v}.
Proof.
intros x. 
refine (contracts2self nat nat_R x (nat_R_inhab x) _).
(* induction x. *)
generalize x.
fix IH 2.
intros x' v.
refine ((match v as i in (nat_R s1 s2) 
        return (forall (e : s2 = s1), (nat_R_inhab s1 = rew e in i))
        with | O_R => fun e => match e with eq_refl =>  _  end
             | S_R y y' IH => fun e => match e with eq_refl => _ end
        end) eq_refl).
        Show Proof.
+ exact IDProp. 
(* False.  *)
Unshelve.
exact e. 
assumption.
+ cbn. 
  rewrite (Eqdep_dec.UIP_refl_nat _ e); 
  reflexivity.
  Show Proof.
+ exact IDProp.
+ 
(* Unset Printing Notations. *)
simpl. 
assert( y' = y ).
  injection e; intros; assumption.
subst; cbn; rewrite (Eqdep_dec.UIP_refl_nat _ e); simpl.
f_equal; apply IH0.
Qed.

Axiom todo : forall {T}, T.
Definition wish5 : forall (x : nat), {u : nat_R x x & forall v : nat_R x x, u = v}.
Proof.
intros x. 
refine (contracts2self nat nat_R x (nat_R_inhab x) _).
(* induction x. *)
generalize x.
fix IH 2.
intros x' v.
unshelve refine ((match v as i in (nat_R s1 s2) 
        return (forall (e : s2 = s1), (nat_R_inhab s1 = rew e in i))
        with | O_R => fun e => match e as e0 in (_ = n) 
                               return (match n with 
                                       | O => nat_R_inhab 0 = rew [nat_R 0] e in O_R
                                       | S n => IDProp end)
                               with eq_refl => _ end
             | S_R y y' IH => fun e => match e with eq_refl => _ end
        end) eq_refl).

+ rewrite (Eqdep_dec.UIP_refl_nat _ e); cbn; reflexivity.
+ assert( y' = y ).
    injection e; intros; assumption.
    Show Proof.
subst.
Show Proof.
  rewrite H in e, IH.
(* cbn; rewrite (Eqdep_dec.UIP_refl_nat _ e); simpl. *)
 cbn; rewrite (Eqdep_dec.UIP_refl_nat _ e); simpl.
f_equal; apply IH0.


Definition wish6 : forall (x : unit), {u : unit_R x x & forall v : unit_R x x, u = v}.
Proof.
intros x. 
refine (contracts2self unit unit_R x (unit_R_inhab x) _).
(* induction x. *)
fix IH 1.
intros v.
(* refine match v with (tt_R ) => _ end.  *)
Show Proof.
Fail refine ((match v as i in (unit_R s1 s2) 
        return (forall (e : s2 = s1), unit_R_inhab s1 = i)
        with | tt_R => fun e => match e with eq_refl =>  _ end 
        end) eq_refl).
Abort.
(* Show Proof.
reflexivity.
Defined. *)
     
Elpi derive.param2 bool.
(* Elpi derive.param2.inhab bool_R. *)
Elpi derive.param1.trivial is_bool.
Elpi derive.param2.inhab bool_R.


Definition wish6 : forall (x : bool), {u : bool_R x x & forall v : bool_R x x, u = v}.
Proof.
intros x. 
refine (contracts2self bool bool_R x (bool_R_inhab x) _).
(* induction x. *)
fix IH 1.
intros v.
(* refine match v with (tt_R ) => _ end.  *)
Show Proof.
refine ((match v as i in (bool_R s1 s2) 
        return (forall (e : s2 = s1), bool_R_inhab s1 = rew [bool_R s1] e in i)
        with | true_R => fun e => match e with eq_refl =>  _ end 
             | false_R => fun e => match e with eq_refl =>  _ end 
        end) eq_refl).
Show Proof.
simpl.
reflexivity.
reflexivity.
Qed.


Inductive bool2 :=
| ATrue : unit -> bool2
| AFalse : unit -> bool2.

Elpi derive.param2 bool2.
Elpi derive.param1 bool2.
(* Elpi derive.param2.inhab bool_R. *)
Elpi derive.param1.trivial is_bool2.
Elpi derive.param2.inhab bool2_R.

Definition wish7 : forall (x : bool2), {u : bool2_R x x & forall v : bool2_R x x, u = v}.
Proof.
intros x. 
refine (contracts2self bool2 bool2_R x (bool2_R_inhab x) _).
fix IH 1.
intros v.
Show Proof.
refine ((match v as i in (bool2_R s1 s2) 
        return (forall (e : s2 = s1), bool2_R_inhab s1 = rew [bool2_R s1] e in i)
        with | ATrue_R u u' uR => fun e => match e with eq_refl =>  _ end 
             | AFalse_R u u' uR => fun e => match e with eq_refl =>  _ end 
        end) eq_refl).
Show Proof.
Abort.


Inductive bool3 :=
| ATrue3 : unit -> bool3
| AFalse3 : bool -> bool3.

Elpi derive.param2 bool3.
Elpi derive.param1 bool3.
(* Elpi derive.param2.inhab bool_R. *)
Elpi derive.param1.trivial is_bool3.
Elpi derive.param2.inhab bool3_R.

Definition wish7 : forall (x : bool3), {u : bool3_R x x & forall v : bool3_R x x, u = v}.
Proof.
intros x. 
refine (contracts2self bool3 bool3_R x (bool3_R_inhab x) _).
fix IH 1.
intros v.
Show Proof.
refine ((match v as i in (bool3_R s1 s2) 
        return (forall (e : s2 = s1), bool3_R_inhab s1 = rew [bool3_R s1] e in i)
        with | ATrue3_R u u' uR => fun e => match e with eq_refl =>  _ end 
             | AFalse3_R b b' bR => fun e => match e with eq_refl =>  _ end 
        end) eq_refl).
Show Proof.
simpl.
reflexivity.
reflexivity.
Qed.
(* ========= *)
(* Mentioning other inductives *)
(* ========= *)
Inductive box_unit := B : unit -> box_unit.
Elpi derive.param2 box_unit.
Elpi derive.param2.inhab box_unit_R.
Check box_unit_R_inhab : forall x : box_unit, box_unit_R x x.
Print box_unit_R_inhab.

(* ========= *)
(* RECURSIVE *)
(* ========= *)

(* Elpi derive.param2 nat. *)
Elpi derive.param2.inhab nat_R.
Check nat_R_inhab : forall x, nat_R x x.
Print nat_R_inhab. 

(* ========= *)
(* Parametric *)
(* ========= *)
Inductive wrap (A : Type) := W : A -> wrap.
Elpi derive.param2 wrap.
Elpi derive.param2.inhab wrap_R.
Check wrap_R_inhab : forall (A : Type) (R : A -> A -> Type) (H : full2self A R) (x : wrap A), wrap_R A A R x x.
Print wrap_R_inhab.


Inductive option (A : Type) := None | Some : A -> option.
Elpi derive.param2 option.
Elpi derive.param2.inhab option_R.
Check option_R_inhab : forall (A : Type) (R : A -> A -> Type) (H : full2self A R) (x : option A), option_R A A R x x.
Print option_R_inhab.


Inductive list (A : Type) := Nil | Cons : A -> list.
Elpi derive.param2 list.
Elpi derive.param2.inhab list_R.
Check list_R_inhab : forall (A : Type) (R : A -> A -> Type) (H : full2self A R) (x : list A), list_R A A R x x.
Print list_R_inhab.

End tests.

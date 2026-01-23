From Coq Require Import ssreflect.
From elpi.apps.derive Require Import derive derive.param2.
Require Import Hierarchy.
From Trocq Require Import HoTTNotations.
From Trocq Require Import coverage sym.
(* Require Import HoTT_additions Hierarchy. *)
Unset Uniform Inductive Parameters.
(* Unset Universe Polymorphism. *)
Unset Universe Minimization ToSet.

Elpi derive.param2 False.
Elpi derive.sym False.

Definition False_symKPred := fun u1 u2 (uR : False_R u1 u2)=> False_sym u2 u1 (False_sym u1 u2 uR) = uR.
Definition False_symK : forall u1 u2 (uR : False_R u1 u2), False_sym u2 u1 (False_sym u1 u2 uR) = uR.
Proof.
move=> u1 u2 uR.
refine (False_R_ind False_symKPred u1 u2 uR).
Defined.

Elpi derive.param2 Unit.
Elpi derive.sym Unit.

Definition Unit_symKPred := fun u1 u2 (uR : Unit_R u1 u2)=> Unit_sym u2 u1 (Unit_sym u1 u2 uR) = uR.
Definition Unit_symK : forall u1 u2 (uR : Unit_R u1 u2), Unit_sym u2 u1 (Unit_sym u1 u2 uR) = uR.
Proof.
move=> u1 u2 uR.
refine (Unit_R_ind Unit_symKPred _ u1 u2 uR).
exact: eq_refl.
Defined.

Elpi derive.param2 Bool.
Elpi derive.sym Bool.

Notation Bool_symKPred := (fun b1 b2 (bR : Bool_R b1 b2)=> Bool_sym b2 b1 (Bool_sym b1 b2 bR) = bR).
Definition Bool_symK : forall b1 b2 (bR : Bool_R b1 b2), Bool_sym b2 b1 (Bool_sym b1 b2 bR) = bR.
Proof.
refine (fun b1 b2 bR=> Bool_R_ind Bool_symKPred _ _ b1 b2 bR).
- exact: eq_refl.
- exact: eq_refl.
Defined.

Elpi derive.param2 Wrap.
Elpi derive.sym Wrap.

Notation Wrap_symKPred := (fun w1 w2 (wR : Wrap_R w1 w2) => Wrap_sym w2 w1 (Wrap_sym w1 w2 wR) = wR).
Definition Wrap_symK : forall w1 w2 (wR : Wrap_R w1 w2), Wrap_sym w2 w1 (Wrap_sym w1 w2 wR) = wR.
Proof.
refine (fun w1 w2 wR=> Wrap_R_ind Wrap_symKPred _ w1 w2 wR).
refine (fun u1 u2 uR=> _).
unfold Wrap_sym.
unfold Wrap_R_rect.
refine ( @eq_ind _ _ (fun t => KWrap1_R u1 u2 t = KWrap1_R u1 u2 uR) _ _ (Unit_symK u1 u2 uR)^).
(* rewrite Unit_symK. *)
exact: eq_refl.
Defined.

Elpi derive.param2 WrapMore.
Elpi derive.sym WrapMore.

Notation WrapMore_symKPred := (fun w1 w2 (wR : WrapMore_R w1 w2) => WrapMore_sym w2 w1 (WrapMore_sym w1 w2 wR) = wR).
Definition WrapMore_symK : forall w1 w2 (wR : WrapMore_R w1 w2), WrapMore_sym w2 w1 (WrapMore_sym w1 w2 wR) = wR.
Proof.
refine (fun w1 w2 wR=> WrapMore_R_ind WrapMore_symKPred _ _ _ w1 w2 wR).
- refine (fun u1 u2 uR=> _).
  refine (fun b1 b2 bR=> _).
  cbn delta beta iota.
  refine ( @eq_ind _ _ (fun t => KWrap_R u1 u2 t b1 b2
(Bool_sym b2 b1 (Bool_sym b1 b2 bR)) = KWrap_R u1 u2 uR b1 b2 bR) _ _ (Unit_symK u1 u2 uR)^).
  refine ( @eq_ind _ _ (fun t => KWrap_R u1 u2 uR b1 b2
t = KWrap_R u1 u2 uR b1 b2 bR) _ _ (Bool_symK b1 b2 bR)^).
  (* rewrite Unit_symK Bool_symK. *)
  exact: eq_refl.
- refine (fun w1 w2 wR=> _).

Notation Nat_symKPred := (fun w1 w2 (wR : Nat_R w1 w2) => Nat_sym w2 w1 (Nat_sym w1 w2 wR) = wR).
Fixpoint Nat_symK : forall w1 w2 (wR : Nat_R w1 w2), Nat_sym w2 w1 (Nat_sym w1 w2 wR) = wR.
Proof.
refine (fun w1 w2 wR=> Nat_R_ind Nat_symKPred _ _ w1 w2 wR).
exact: eq_refl.
refine (fun n1 n2 nR IH => _).
cbn delta beta iota.
refine (@eq_ind _ _ (fun t => S'_R n1 n2 t = S'_R n1 n2 nR) _ _ (Nat_symK n1 n2 nR)^).
(* rewrite IH. *)
exact: eq_refl.
Defined.

Elpi derive.param2 Box.
Elpi derive.sym Box.

Notation Box_symKPred := (fun A1 A2 (AR: A1 -> A2 -> Type) 
                              b1 b2 (bR : Box_R A1 A2 AR b1 b2) 
                              => Box_sym A2 A1 (sym_rel AR) b2 b1 (Box_sym A1 A2 AR b1 b2 bR) = bR).
Definition Box_symK :
  forall A1 A2 (AR: A1 -> A2 -> Type) 
  b1 b2 (bR : Box_R A1 A2 AR b1 b2), 
  Box_sym A2 A1 (sym_rel AR) b2 b1 (Box_sym A1 A2 AR b1 b2 bR) = bR.
Proof.
refine (fun A1 A2 AR=> _).
refine (fun b1 b2 bR=> _).
refine (Box_R_ind A1 A2 AR (Box_symKPred A1 A2 AR) _ b1 b2 bR).
move=> a1 a2 ar.
cbn delta beta iota.
exact: eq_refl.
Defined.

Elpi derive.param2 Option.
Elpi derive.sym Option.


Notation Option_symKPred := (fun A1 A2 (AR: A1 -> A2 -> Type) b1 b2 (bR : Option_R A1 A2 AR b1 b2) => Option_sym A2 A1 (sym_rel AR) b2 b1 (Option_sym A1 A2 AR b1 b2 bR) = bR).
Definition Option_symK :
  forall A1 A2 (AR: A1 -> A2 -> Type) b1 b2 (bR : Option_R A1 A2 AR b1 b2), Option_sym A2 A1 (sym_rel AR) b2 b1 (Option_sym A1 A2 AR b1 b2 bR) = bR.
Proof.
refine (fun A1 A2 AR=> _).
refine (fun b1 b2 bR=> _).
refine (Option_R_ind A1 A2 AR (Option_symKPred A1 A2 AR) _ _ b1 b2 bR).
- exact: eq_refl.
- move=> a1 a2 ar.
simpl.
cbn delta beta iota.
Check (@eq_refl ((sym_rel AR) a2 a1) ar).
exact: eq_refl.
Defined.

Elpi derive.param2 Prod.
Elpi derive.sym Prod.

Notation Prod_symKPred := (fun A1 A2 (AR: A1 -> A2 -> Type) B1 B2 BR b1 b2 (bR : Prod_R A1 A2 AR B1 B2 BR b1 b2) => Prod_sym A2 A1 (sym_rel AR) B2 B1 (sym_rel BR) b2 b1 (Prod_sym A1 A2 AR B1 B2 BR b1 b2 bR) = bR).
Definition Prod_symK :
  forall A1 A2 (AR: A1 -> A2 -> Type) B1 B2 (BR : B1 -> B2 -> Type) b1 b2 (bR : Prod_R A1 A2 AR B1 B2 BR b1 b2), Prod_sym A2 A1 (sym_rel AR) B2 B1 (sym_rel BR) b2 b1 (Prod_sym A1 A2 AR B1 B2 BR b1 b2 bR) = bR.
Proof.
refine (fun A1 A2 AR=> _).
refine (fun B1 B2 BR=> _).
refine (fun b1 b2 bR=> _).
refine (Prod_R_ind A1 A2 AR B1 B2 BR (Prod_symKPred A1 A2 AR B1 B2 BR) _ b1 b2 bR).
- move=> a1 a2 ar b b' br.
exact: eq_refl.
Defined.

Elpi derive.param2 List.
Elpi derive.sym List.

Notation List_symKPred := (fun A1 A2 (AR: A1 -> A2 -> Type) b1 b2 (bR : List_R A1 A2 AR b1 b2) => List_sym A2 A1 (sym_rel AR) b2 b1 (List_sym A1 A2 AR b1 b2 bR) = bR).
Fixpoint List_symK :
  forall A1 A2 (AR: A1 -> A2 -> Type) b1 b2 (bR : List_R A1 A2 AR b1 b2), List_sym A2 A1 (sym_rel AR) b2 b1 (List_sym A1 A2 AR b1 b2 bR) = bR.
Proof.
refine (fun A1 A2 AR=> _).
refine (fun b1 b2 bR=> _).
refine (List_R_ind A1 A2 AR (List_symKPred A1 A2 AR) _ _ b1 b2 bR).
- exact: eq_refl.
- move=> a1 a2 ar l1 l2 lr IH.
  cbn delta beta iota.
  refine (@eq_ind _ _ (fun t => Cons_R A1 A2 (sym_rel (sym_rel AR)) a1 a2 ar l1 l2 t =
Cons_R A1 A2 AR a1 a2 ar l1 l2 lr) _ _ (List_symK A1 A2 AR l1 l2 lr)^).
  (* rewrite IH. *)
  exact: eq_refl.
Defined.

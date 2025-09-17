From Coq Require Import ssreflect.
From elpi.apps.derive Require Import derive derive.param2.
Require Import Hierarchy.
From Trocq Require Import coverage.
(* Require Import HoTT_additions Hierarchy. *)
Unset Uniform Inductive Parameters.
(* Unset Universe Polymorphism. *)
Unset Universe Minimization ToSet.

(* Definition Unit := unit. *)

Elpi derive.param2 Unit.
Definition UnitR := Unit_R.
Definition unit_Pred := fun (s1 s2: Unit) (RR : Unit_R s1 s2)=> Unit_R s2 s1.

Definition unitR_sym : forall u1 u2, UnitR u1 u2 -> UnitR u2 u1.
Proof.
move=> u1 u2 uR.
refine (Unit_R_rect unit_Pred _ u1 u2 uR).
- exact TT_R.
Defined.

Elpi derive.param2 Bool.
Definition BoolR := Bool_R.

Notation BoolR_symPred := (fun b1 b2 (bR : Bool_R b1 b2)=> Bool_R b2 b1).
Definition boolR_sym : forall b1 b2 (bR : Bool_R b1 b2), Bool_R b2 b1.
Proof.
refine (fun b1 b2 bR=> Bool_R_rect BoolR_symPred _ _ b1 b2 bR).
- exact: Falseb_R.
- exact: Trueb_R.
Defined.

Elpi derive.param2 Wrap.
Definition WrapR := Wrap_R.

Notation wrapR_symPred := (fun w1 w2 (wR : Wrap_R w1 w2) => Wrap_R w2 w1).
Definition wrapR_sym : forall w1 w2, Wrap_R w1 w2 -> Wrap_R w2 w1.
Proof.
refine (fun w1 w2 wR=> Wrap_R_rect wrapR_symPred _ w1 w2 wR).
refine (fun u1 u2 uR=> _).
exact: (KWrap1_R u2 u1 (unitR_sym u1 u2 uR)).
Defined.

Elpi derive.param2 WrapMore.
Notation wrapMoreR_symPred := (fun w1 w2 (wR : WrapMore_R w1 w2) => WrapMore_R w2 w1).
Definition wrapMoreR_sym : forall w1 w2, WrapMore_R w1 w2 -> WrapMore_R w2 w1.
Proof.
refine (fun w1 w2 wR=> WrapMore_R_rect wrapMoreR_symPred _ _ _ w1 w2 wR).
- refine (fun u1 u2 uR=> _).
  refine (fun b1 b2 bR=> _).
  exact: (KWrap_R u2 u1 (unitR_sym u1 u2 uR) b2 b1 (boolR_sym b1 b2 bR)).
- refine (fun w1 w2 wR=> _).
  exact: (KWrapWrap_R w2 w1 (wrapR_sym w1 w2 wR)).
- refine (fun u1 u2 uR=> _).
  refine (fun u3 u4 uR2=> _). 
  refine (fun u5 u6 uR3=> _). 
  exact: (F_R u2 u1 (unitR_sym u1 u2 uR) u4 u3 (unitR_sym u3 u4 uR2) u6 u5 (unitR_sym u5 u6 uR3)).
Defined.

Definition Nat := nat.
Elpi derive.param2 nat.
Definition NatR := nat_R.

Notation nat_symPred := (fun w1 w2 (wR : nat_R w1 w2) => nat_R w2 w1).
Fixpoint nat_sym : forall w1 w2, nat_R w1 w2 -> nat_R w2 w1.
Proof.
refine (fun w1 w2 wR=> nat_R_rect nat_symPred _ _ w1 w2 wR).
exact: O_R.
refine (fun n1 n2 nR IH => _).
apply (S_R _ _ (nat_sym _ _ nR)).
Defined.

Inductive Box (A : Type) : Type := B : A -> Box A.
Elpi derive.param2 Box.

Notation boxR_symPred := (fun A1 A2 (AR: A1 -> A2 -> Type) b1 b2 (bR : Box_R A1 A2 AR b1 b2) => Box_R A2 A1 (sym_rel AR) b2 b1).
Definition boxR_sym : forall A1 A2 (AR: A1 -> A2 -> Type) b1 b2, Box_R A1 A2 AR b1 b2 -> Box_R A2 A1 (sym_rel AR) b2 b1.
Proof.
refine (fun A1 A2 AR=> _).
refine (fun b1 b2 bR=> _).
refine (Box_R_rect A1 A2 AR (boxR_symPred A1 A2 AR) _ _ _ bR).
move=> a1 a2 ar.
refine (B_R A2 A1 (sym_rel AR) a2 a1 _).
exact: ( (fun x y r => r) a1 a2 ar).
Defined.

Elpi derive.param2 Option.

Notation Option_symPred := (fun A1 A2 (AR: A1 -> A2 -> Type) b1 b2 (bR : Option_R A1 A2 AR b1 b2) => Option_R A2 A1 (sym_rel AR) b2 b1).
Definition Option_sym : forall A1 A2 (AR: A1 -> A2 -> Type) b1 b2, Option_R A1 A2 AR b1 b2 -> Option_R A2 A1 (sym_rel AR) b2 b1.
Proof.
refine (fun A1 A2 AR=> _).
refine (fun b1 b2 bR=> _).
refine (Option_R_rect A1 A2 AR (Option_symPred A1 A2 AR) _ _ _ _ bR).
- move=> a1 a2 ar. exact: (Some_R A2 A1 (sym_rel AR) a2 a1 ar).
- exact: (None_R A2 A1 (sym_rel AR)).
Defined.

Elpi derive.param2 List.

Notation List_symPred := (fun A1 A2 (AR: A1 -> A2 -> Type) b1 b2 (bR : List_R A1 A2 AR b1 b2) => List_R A2 A1 (sym_rel AR) b2 b1).
Fixpoint List_sym : forall A1 A2 (AR: A1 -> A2 -> Type) b1 b2, List_R A1 A2 AR b1 b2 -> List_R A2 A1 (sym_rel AR) b2 b1.
Proof.
refine (fun A1 A2 AR=> _).
refine (fun b1 b2 bR=> _).
refine (List_R_rect A1 A2 AR (List_symPred A1 A2 AR) _ _ _ _ bR).
- exact: (nil_R A2 A1 (sym_rel AR)).
- move=> a1 a2 ar l1 l2 lr IH. 
exact: (cons_R A2 A1 (sym_rel AR) a2 a1 ar l2 l1 (List_sym A1 A2 AR _ _ lr)).
Defined.

Elpi derive.param2 Prod.

Notation Prod_symPred := (fun A1 A2 (AR: A1 -> A2 -> Type) B1 B2 (BR : B1 -> B2 -> Type) b1 b2 (bR : Prod_R A1 A2 AR B1 B2 BR b1 b2) => Prod_R A2 A1 (sym_rel AR) B2 B1 (sym_rel BR) b2 b1).
Definition Prod_sym : forall A1 A2 (AR: A1 -> A2 -> Type) B1 B2 (BR: B1 -> B2 -> Type) b1 b2, Prod_R A1 A2 AR B1 B2 BR b1 b2 -> Prod_R A2 A1 (sym_rel AR) B2 B1 (sym_rel BR) b2 b1.
Proof.
refine (fun A1 A2 AR=> _).
refine (fun B1 B2 BR=> _).
refine (fun b1 b2 bR=> _).
refine (Prod_R_rect A1 A2 AR B1 B2 BR (Prod_symPred A1 A2 AR B1 B2 BR) _ _ _ bR).
- move=> a1 a2 ar b b' br. exact: (pair_R A2 A1 (sym_rel AR) B2 B1 (sym_rel BR) a2 a1 ar b' b br).
Defined.

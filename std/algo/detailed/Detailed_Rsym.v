From Trocq Require Import symK.
Import HoTTNotations.
From Trocq Require Import coverage.
Unset Uniform Inductive Parameters.

Require Import Hierarchy.
From mathcomp Require Import ssreflect.
Check existT.
Elpi derive False.
Definition FalseR_sym : forall f1 f2, sym_rel False_R f1 f2 <->> False_R f1 f2.
Proof.
  intros f1 f2.
  have@ f :=  False_sym f2 f1.
  have@ g := False_sym f1 f2.
  have@ fgK := False_symK f2 f1.
  exact: (existT _ f (existT _ g fgK)).
Defined.
Print FalseR_sym.

Elpi derive Unit.
Definition UnitR_sym : forall u1 u2, sym_rel Unit_R u1 u2 <->> Unit_R u1 u2.
Proof.
  intros u1 u2.
  refine (Unit_sym u2 u1; _).
  refine (Unit_sym u1 u2; _).
  refine (Unit_symK u2 u1).
Defined.

Elpi derive Bool.
Definition BoolR_sym : forall u1 u2, sym_rel Bool_R u1 u2 <->> Bool_R u1 u2.
Proof.
  intros u1 u2.
  refine (Bool_sym u2 u1; _).
  refine (Bool_sym u1 u2; _).
  refine (Bool_symK u2 u1).
Defined.

Elpi derive Wrap.
Definition WrapR_sym : forall u1 u2, sym_rel Wrap_R u1 u2 <->> Wrap_R u1 u2.
Proof.
  intros u1 u2.
  refine (Wrap_sym u2 u1; _).
  refine (Wrap_sym u1 u2; _).
  refine (Wrap_symK u2 u1).
Defined.

Elpi derive WrapMore.
Definition WrapMoreR_sym : forall u1 u2, sym_rel WrapMore_R u1 u2 <->> WrapMore_R u1 u2.
Proof.
  intros u1 u2.
  refine (WrapMore_sym u2 u1; _).
  refine (WrapMore_sym u1 u2; _).
  refine (WrapMore_symK u2 u1).
Defined.

Elpi derive Nat.
Definition NatR_sym : forall u1 u2, sym_rel Nat_R u1 u2 <->> Nat_R u1 u2.
Proof.
  intros u1 u2.
  refine (Nat_sym u2 u1; _).
  refine (Nat_sym u1 u2; _).
  refine (Nat_symK u2 u1).
Defined.

Elpi derive Box.
Definition BoxR_sym : forall (A B : Type) (AR : A -> B -> Type), forall u1 u2, Box_R B A (sym_rel AR) u2 u1 <->> Box_R A B AR u1 u2.
Proof.
  intros A B AR u1 u2.
  refine ((Box_sym B A (sym_rel AR) u2 u1); _).
  refine (Box_sym A B AR u1 u2; _).
  refine (Box_symK B A (sym_rel AR) u2 u1).
Defined.

Elpi derive Option.
Definition OptionR_sym : forall (A B : Type) (AR : A -> B -> Type), forall u1 u2, Option_R B A (sym_rel AR) u2 u1 <->> Option_R A B AR u1 u2.
Proof.
  intros A B AR u1 u2.
  refine ((Option_sym B A (sym_rel AR) u2 u1); _).
  refine  (Option_sym A B AR u1 u2; _).
  refine  (Option_symK B A (sym_rel AR) u2 u1).
Defined.

Elpi derive Prod.
Definition ProdR_sym : forall (A B : Type) (AR : A -> B -> Type) (A2 B2 : Type) (AR2 : A2 -> B2 -> Type), 
  forall u1 u2, Prod_R B A (sym_rel AR) B2 A2 (sym_rel AR2) u2 u1 <->> Prod_R A B AR A2 B2 AR2 u1 u2.
Proof.
  intros A B AR A2 B2 AR2 u1 u2.
  refine ((Prod_sym B A (sym_rel AR) B2 A2 (sym_rel AR2) u2 u1); _).
  refine  (Prod_sym A B AR A2 B2 AR2 u1 u2; _).
  refine  (Prod_symK B A (sym_rel AR) B2 A2 (sym_rel AR2) u2 u1).
Defined.

Elpi derive ThreeTypes.
Definition ThreeTypesR_sym : forall (A B : Type) (AR : A -> B -> Type) (A2 B2 : Type) (AR2 : A2 -> B2 -> Type)
  (A3 B3 : Type) (AR3 : A3 -> B3 -> Type), 
  forall u1 u2, ThreeTypes_R B A (sym_rel AR) B2 A2 (sym_rel AR2) B3 A3 (sym_rel AR3) u2 u1 
  <->> ThreeTypes_R A B AR A2 B2 AR2 A3 B3 AR3 u1 u2.
Proof.
  intros A B AR A2 B2 AR2 A3 B3 AR3 u1 u2.
  refine ((ThreeTypes_sym B A (sym_rel AR) B2 A2 (sym_rel AR2) B3 A3 (sym_rel AR3) u2 u1); _).
  refine  (ThreeTypes_sym A B AR A2 B2 AR2 A3 B3 AR3 u1 u2; _).
  refine  (ThreeTypes_symK B A (sym_rel AR) B2 A2 (sym_rel AR2) B3 A3 (sym_rel AR3) u2 u1).
Defined.

Elpi derive List.
Definition ListR_sym : forall (A B : Type) (AR : A -> B -> Type), forall u1 u2, List_R B A (sym_rel AR) u2 u1 <->> List_R A B AR u1 u2.
Proof.
  intros A B AR u1 u2.
  refine ((List_sym B A (sym_rel AR) u2 u1); _).
  refine  (List_sym A B AR u1 u2; _).
  refine  (List_symK B A (sym_rel AR) u2 u1).
Defined.

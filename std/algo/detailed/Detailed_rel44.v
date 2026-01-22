
From Trocq Require Import map4 umap Rel40 symK.
Import HoTTNotations.
From Trocq Require Import coverage.
Unset Uniform Inductive Parameters.

Require Import Stdlib Hierarchy Param_lemmas.
Elpi derive False.
Check False_rel40 : Param40.Rel False False.

Definition FalseR_sym : forall f1 f2, sym_rel False_R f1 f2 <->> False_R f1 f2.
Proof.
  intros f1 f2.
  refine (False_sym f2 f1; _).
  refine (False_sym f1 f2; _).
  refine (False_symK f2 f1).
Defined.

Definition Param44_False : Param44.Rel False False := 
  MkUParam False_umap (eq_Map4 FalseR_sym False_umap).

Elpi derive Unit.
(* Definition UnitR_sym : forall u1 u2, sym_rel Unit_R u1 u2 <->> Unit_R u1 u2. *)
Definition UnitR_sym : forall u1 u2, Unit_R u2 u1 <->> Unit_R u1 u2.
Proof.
  intros u1 u2.
  refine (Unit_sym u2 u1; _).
  refine (Unit_sym u1 u2; _).
  refine (Unit_symK u2 u1).
Defined.

Definition Param00_Unit : Param00.Rel Unit Unit := 
  Param00.BuildRel _ _ Unit_R Unit_umap (eq_Map0 UnitR_sym Unit_umap).

Definition Param11_Unit : Param11.Rel Unit Unit := 
  Param11.BuildRel _ _ Unit_R Unit_umap (eq_Map1 UnitR_sym Unit_umap).

Definition Param2a2a_Unit : Param2a2a.Rel Unit Unit := 
  Param2a2a.BuildRel _ _ Unit_R Unit_umap (eq_Map2a UnitR_sym Unit_umap).

Definition Param2b2b_Unit : Param2b2b.Rel Unit Unit := 
  Param2b2b.BuildRel _ _ Unit_R Unit_umap (eq_Map2b UnitR_sym Unit_umap).

Definition Param33_Unit : Param33.Rel Unit Unit := 
  Param33.BuildRel _ _ Unit_R Unit_umap (eq_Map3 UnitR_sym Unit_umap).

Definition Param44_Unit : Param44.Rel Unit Unit := 
  MkUParam Unit_umap (eq_Map4 UnitR_sym Unit_umap).

Elpi derive Bool.
Definition BoolR_sym : forall u1 u2, sym_rel Bool_R u1 u2 <->> Bool_R u1 u2.
Proof.
  intros u1 u2.
  refine (Bool_sym u2 u1; _).
  refine (Bool_sym u1 u2; _).
  refine (Bool_symK u2 u1).
Defined.

Definition Param44_Bool : Param44.Rel Bool Bool := 
  MkUParam Bool_umap (eq_Map4 BoolR_sym Bool_umap).

Elpi derive Wrap.
Definition WrapR_sym : forall u1 u2, sym_rel Wrap_R u1 u2 <->> Wrap_R u1 u2.
Proof.
  intros u1 u2.
  refine (Wrap_sym u2 u1; _).
  refine (Wrap_sym u1 u2; _).
  refine (Wrap_symK u2 u1).
Defined.

Definition Param44_Wrap : Param44.Rel Wrap Wrap := 
  MkUParam Wrap_umap (eq_Map4 WrapR_sym Wrap_umap).

Elpi derive WrapMore.
Definition WrapMoreR_sym : forall u1 u2, sym_rel WrapMore_R u1 u2 <->> WrapMore_R u1 u2.
Proof.
  intros u1 u2.
  refine (WrapMore_sym u2 u1; _).
  refine (WrapMore_sym u1 u2; _).
  refine (WrapMore_symK u2 u1).
Defined.

Definition Param44_WrapMore : Param44.Rel WrapMore WrapMore := 
  MkUParam WrapMore_umap (eq_Map4 WrapMoreR_sym WrapMore_umap).

Elpi derive Nat.
Definition NatR_sym : forall u1 u2, sym_rel Nat_R u1 u2 <->> Nat_R u1 u2.
Proof.
  intros u1 u2.
  refine (Nat_sym u2 u1; _).
  refine (Nat_sym u1 u2; _).
  refine (Nat_symK u2 u1).
Defined.

Definition Param44_Nat : Param44.Rel Nat Nat := 
  MkUParam Nat_umap (eq_Map4 NatR_sym Nat_umap).

Elpi derive Box.
Definition BoxR_sym : forall (A B : Type) (AR : A -> B -> Type), forall u1 u2, Box_R B A (sym_rel AR) u2 u1 <->> Box_R A B AR u1 u2.
Proof.
  intros A B AR u1 u2.
  refine ((Box_sym B A (sym_rel AR) u2 u1); _).
  refine (Box_sym A B AR u1 u2; _).
  refine (Box_symK B A (sym_rel AR) u2 u1).
Defined.

Definition Param00_Box : forall (A B : Type) (AR : Param00.Rel A B), Param00.Rel (Box A) (Box B).
  Fail refine( fun A B AR=> Param00.BuildRel _ _ (Box_R A B AR) _ (eq_Map0 (BoxR_sym A B AR) _)).
Abort.

Definition Param44_Box : forall (A B : Type) (AR : Param44.Rel A B), Param44.Rel (Box A) (Box B).
Proof. 
  refine (fun A B AR => MkUParam (Box_umap A B AR (Param44.covariant _ _ _)) _).
  refine (eq_Map4 (BoxR_sym B A (sym_rel AR)) (Box_umap _ _ _ (Param44.contravariant _ _ _))).
Defined.

Elpi derive Option.
Definition OptionR_sym : forall (A B : Type) (AR : A -> B -> Type), forall u1 u2, Option_R B A (sym_rel AR) u2 u1 <->> Option_R A B AR u1 u2.
Proof.
  intros A B AR u1 u2.
  refine ((Option_sym B A (sym_rel AR) u2 u1); _).
  refine  (Option_sym A B AR u1 u2; _).
  refine  (Option_symK B A (sym_rel AR) u2 u1).
Defined.

Definition Param44_Option : forall (A B : Type) (AR : Param44.Rel A B), Param44.Rel (Option A) (Option B).
Proof. 
  refine (fun A B AR => MkUParam (Option_umap A B AR (Param44.covariant _ _ _)) _).
  refine (eq_Map4 (OptionR_sym B A (sym_rel AR)) (Option_umap _ _ _ (Param44.contravariant _ _ _))).
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

Definition Param44_Prod : forall (A B : Type) (AR : Param44.Rel A B) (A2 B2 : Type) (AR2 : Param44.Rel A2 B2), 
  Param44.Rel (Prod A A2) (Prod B B2).
Proof. 
  refine (fun A B AR A2 B2 AR2 => MkUParam (Prod_umap A B AR (Param44.covariant _ _ _) A2 B2 AR2 (Param44.covariant _ _ _)) _).
  refine (eq_Map4 (ProdR_sym B A (sym_rel AR) B2 A2 (sym_rel AR2)) (Prod_umap _ _ _ (Param44.contravariant _ _ _) _ _ _ (Param44.contravariant _ _ _))).
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

Definition Param44_ThreeTypes : forall (A B : Type) (AR : Param44.Rel A B) (A2 B2 : Type) (AR2 : Param44.Rel A2 B2)
  (A3 B3 : Type) (AR3 : Param44.Rel A3 B3),
  Param44.Rel (ThreeTypes A A2 A3) (ThreeTypes B B2 B3).
Proof. 
  refine (fun A B AR A2 B2 AR2 A3 B3 AR3 => 
            MkUParam (ThreeTypes_umap A B AR (Param44.covariant _ _ _) A2 B2 AR2 (Param44.covariant _ _ _) A3 B3 AR3 (Param44.covariant _ _ _)) _).
  refine (eq_Map4 (ThreeTypesR_sym B A (sym_rel AR) B2 A2 (sym_rel AR2) B3 A3 (sym_rel AR3)) (ThreeTypes_umap _ _ _ (Param44.contravariant _ _ _) _ _ _ (Param44.contravariant _ _ _) _ _ _ (Param44.contravariant _ _ _))).
Defined.

Elpi derive List.
Definition ListR_sym : forall (A B : Type) (AR : A -> B -> Type), forall u1 u2, List_R B A (sym_rel AR) u2 u1 <->> List_R A B AR u1 u2.
Proof.
  intros A B AR u1 u2.
  refine ((List_sym B A (sym_rel AR) u2 u1); _).
  refine  (List_sym A B AR u1 u2; _).
  refine  (List_symK B A (sym_rel AR) u2 u1).
Defined.

Definition Param44_List : forall (A B : Type) (AR : Param44.Rel A B), Param44.Rel (List A) (List B).
Proof. 
  refine (fun A B AR => MkUParam (List_umap A B AR (Param44.covariant _ _ _)) _).
  refine (eq_Map4 (ListR_sym B A (sym_rel AR)) (List_umap _ _ _ (Param44.contravariant _ _ _))).
Defined.

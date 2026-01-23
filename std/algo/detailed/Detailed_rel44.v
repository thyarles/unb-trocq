
From Trocq Require Import map4 umap Rel40 symK RsymK.
Import HoTTNotations.
From Trocq Require Import coverage.
Unset Uniform Inductive Parameters.

Require Import Stdlib Hierarchy Param_lemmas.
Elpi derive False.

Definition Param44_False : Param44.Rel False False := 
  MkUParam False_umap (eq_Map4 False_rsymK False_umap).

Elpi derive Unit.
Definition Param00_Unit : Param00.Rel Unit Unit := 
  Param00.BuildRel _ _ Unit_R Unit_umap (eq_Map0 Unit_rsymK Unit_umap).

Definition Param11_Unit : Param11.Rel Unit Unit := 
  Param11.BuildRel _ _ Unit_R Unit_umap (eq_Map1 Unit_rsymK Unit_umap).

Definition Param2a2a_Unit : Param2a2a.Rel Unit Unit := 
  Param2a2a.BuildRel _ _ Unit_R Unit_umap (eq_Map2a Unit_rsymK Unit_umap).

Definition Param2b2b_Unit : Param2b2b.Rel Unit Unit := 
  Param2b2b.BuildRel _ _ Unit_R Unit_umap (eq_Map2b Unit_rsymK Unit_umap).

Definition Param33_Unit : Param33.Rel Unit Unit := 
  Param33.BuildRel _ _ Unit_R Unit_umap (eq_Map3 Unit_rsymK Unit_umap).

Definition Param44_Unit : Param44.Rel Unit Unit := 
  MkUParam Unit_umap (eq_Map4 Unit_rsymK Unit_umap).

Elpi derive Bool.
Definition Param44_Bool : Param44.Rel Bool Bool := 
  MkUParam Bool_umap (eq_Map4 Bool_rsymK Bool_umap).

Elpi derive Wrap.
Definition Param44_Wrap : Param44.Rel Wrap Wrap := 
  MkUParam Wrap_umap (eq_Map4 Wrap_rsymK Wrap_umap).

Elpi derive WrapMore.

Definition Param44_WrapMore : Param44.Rel WrapMore WrapMore := 
  MkUParam WrapMore_umap (eq_Map4 WrapMore_rsymK WrapMore_umap).

Elpi derive Nat.
Definition Param44_Nat : Param44.Rel Nat Nat := 
  MkUParam Nat_umap (eq_Map4 Nat_rsymK Nat_umap).

Elpi derive Box.
Definition Param00_Box : forall (A B : Type) (AR : Param00.Rel A B), Param00.Rel (Box A) (Box B).
  Fail refine( fun A B AR=> Param00.BuildRel _ _ (Box_R A B AR) _ (eq_Map0 (Box_rsymK A B AR) _)).
Abort.

Definition Param44_Box : forall (A B : Type) (AR : Param44.Rel A B), Param44.Rel (Box A) (Box B).
Proof. 
  refine (fun A B AR => Param44.BuildRel (Box_umap A B AR (Param44.covariant A B AR)) _).
  refine (eq_Map4 (Box_rsymK B A (sym_rel AR)) (Box_umap B A (sym_rel AR) (Param44.contravariant A B AR))).
  Show Proof.
Defined.

Elpi derive Option.
Definition Param44_Option : forall (A B : Type) (AR : Param44.Rel A B), Param44.Rel (Option A) (Option B).
Proof. 
  refine (fun A B AR => MkUParam (Option_umap A B AR (Param44.covariant _ _ _)) _).
  refine (eq_Map4 (Option_rsymK B A (sym_rel AR)) (Option_umap _ _ _ (Param44.contravariant _ _ _))).
Defined.

Elpi derive Prod.
Definition Param44_Prod : forall (A B : Type) (AR : Param44.Rel A B) (A2 B2 : Type) (AR2 : Param44.Rel A2 B2), 
  Param44.Rel (Prod A A2) (Prod B B2).
Proof. 
  refine (fun A B AR A2 B2 AR2 => MkUParam (Prod_umap A B AR (Param44.covariant _ _ _) A2 B2 AR2 (Param44.covariant _ _ _)) _).
  refine (eq_Map4 (Prod_rsymK B A (sym_rel AR) B2 A2 (sym_rel AR2)) (Prod_umap _ _ _ (Param44.contravariant _ _ _) _ _ _ (Param44.contravariant _ _ _))).
Defined.

Elpi derive ThreeTypes.
Definition Param44_ThreeTypes : forall (A B : Type) (AR : Param44.Rel A B) (A2 B2 : Type) (AR2 : Param44.Rel A2 B2)
  (A3 B3 : Type) (AR3 : Param44.Rel A3 B3),
  Param44.Rel (ThreeTypes A A2 A3) (ThreeTypes B B2 B3).
Proof. 
  refine (fun A B AR A2 B2 AR2 A3 B3 AR3 => 
            MkUParam (ThreeTypes_umap A B AR (Param44.covariant _ _ _) A2 B2 AR2 (Param44.covariant _ _ _) A3 B3 AR3 (Param44.covariant _ _ _)) _).
  refine (eq_Map4 (ThreeTypes_rsymK B A (sym_rel AR) B2 A2 (sym_rel AR2) B3 A3 (sym_rel AR3)) (ThreeTypes_umap _ _ _ (Param44.contravariant _ _ _) _ _ _ (Param44.contravariant _ _ _) _ _ _ (Param44.contravariant _ _ _))).
Defined.

Elpi derive List.
Definition Param44_List : forall (A B : Type) (AR : Param44.Rel A B), Param44.Rel (List A) (List B).
Proof. 
  refine (fun A B AR => MkUParam (List_umap A B AR (Param44.covariant _ _ _)) _).
  refine (eq_Map4 (List_rsymK B A (sym_rel AR)) (List_umap _ _ _ (Param44.contravariant _ _ _))).
Defined.

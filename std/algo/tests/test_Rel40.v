From Trocq Require Import map4 umap Rel40.
From Trocq Require Import coverage.
Unset Uniform Inductive Parameters.

Elpi derive False.
Check False_rel40 : Param40.Rel False False.

Elpi derive Unit.
Check Unit_rel40 : Param40.Rel Unit Unit.

Elpi derive Bool.
Check Bool_rel40 :  Param40.Rel Bool Bool.

Elpi derive Wrap.
Check Wrap_rel40 :  Param40.Rel Wrap Wrap.

Elpi derive WrapMore.
Check WrapMore_rel40 :  Param40.Rel WrapMore WrapMore.

Elpi derive Nat.
Check Nat_rel40 :  Param40.Rel Nat Nat.

Elpi derive Box.
Check Box_rel40 : forall A1 A2 AR UR,  Param40.Rel (Box A1) (Box A2).

Elpi derive Option.
Check Option_rel40 : forall A1 A2 AR UR, Param40.Rel (Option A1) (Option A2). 

Elpi derive Prod.
Check Prod_rel40 : forall A1 A2 AR UR B1 B2 BR BUR,  Param40.Rel (Prod A1 B1) (Prod A2 B2).

Elpi derive ThreeTypes.
Check ThreeTypes_rel40 : forall A1 A2 AR UR B1 B2 BR BUR C1 C2 CR CUR,  Param40.Rel (ThreeTypes A1 B1 C1) (ThreeTypes A2 B2 C2).

Elpi derive List.
Check List_rel40 : forall A1 A2 AR UR,  Param40.Rel (List A1) (List A2).

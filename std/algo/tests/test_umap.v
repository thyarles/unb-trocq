From Trocq Require Import map4 umap.
From Trocq Require Import coverage.
Unset Uniform Inductive Parameters.

Elpi derive False.
Check False_umap : IsUMap False_R.

Elpi derive Unit.
Check Unit_umap : IsUMap Unit_R.

Elpi derive Bool.
Check Bool_umap : IsUMap Bool_R.

Elpi derive Wrap.
Check Wrap_umap : IsUMap Wrap_R.

Elpi derive WrapMore.
Check WrapMore_umap : IsUMap WrapMore_R.

Elpi derive Nat.
Check Nat_umap : IsUMap Nat_R.

Elpi derive Box.
Check Box_umap : forall A1 A2 AR UR, IsUMap (Box_R A1 A2 AR).
Print Box_umap.

Elpi derive Option.
Check Option_umap : forall A1 A2 AR UR, IsUMap (Option_R A1 A2 AR).

Elpi derive Prod.
Check Prod_umap : forall A1 A2 AR UR B1 B2 BR BUR, IsUMap (Prod_R A1 A2 AR B1 B2 BR).

Elpi derive ThreeTypes.
Check ThreeTypes_umap : forall A1 A2 AR UR B1 B2 BR BUR C1 C2 CR CUR, IsUMap (ThreeTypes_R A1 A2 AR B1 B2 BR C1 C2 CR).

Elpi derive List.
Check List_umap : forall A1 A2 AR UR, IsUMap (List_R A1 A2 AR).
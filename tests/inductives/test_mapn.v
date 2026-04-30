From Trocq Require Import map4 mapn.
Require Import coverage.
Unset Uniform Inductive Parameters.

Elpi derive testFalse.
Check testFalse_map0 : Map0.Has testFalse_R.
Check testFalse_map1 : Map1.Has testFalse_R.
Check testFalse_map2a : Map2a.Has testFalse_R.
Check testFalse_map2b : Map2b.Has testFalse_R.
Check testFalse_map3 : Map3.Has testFalse_R.
Check testFalse_map4 : IsUMap testFalse_R.

Elpi derive testUnit.
Check testUnit_map4 : IsUMap testUnit_R.

Elpi derive testBool.
Check testBool_map4 : IsUMap testBool_R.

Elpi derive Wrap.
Check Wrap_map4 : IsUMap Wrap_R.

Elpi derive WrapMore.
Check WrapMore_map4 : IsUMap WrapMore_R.

Elpi derive Nat.
Check Nat_map4 : IsUMap Nat_R.

Elpi derive Box.
Check Box_map4 : forall A1 A2 AR UR, IsUMap (Box_R A1 A2 AR).

Elpi derive Option.
Check Option_map4 : forall A1 A2 AR UR, IsUMap (Option_R A1 A2 AR).

Elpi derive Prod.
Check Prod_map4 : forall A1 A2 AR UR B1 B2 BR BUR, IsUMap (Prod_R A1 A2 AR B1 B2 BR).

Elpi derive ThreeTypes.
Check ThreeTypes_map4 : forall A1 A2 AR UR B1 B2 BR BUR C1 C2 CR CUR, IsUMap (ThreeTypes_R A1 A2 AR B1 B2 BR C1 C2 CR).

Elpi derive List.
Check List_map0 : forall A1 A2 AR UR, Map0.Has (List_R A1 A2 AR).
Check List_map1 : forall A1 A2 AR UR, Map1.Has (List_R A1 A2 AR).
Check List_map2a: forall A1 A2 AR UR, Map2a.Has (List_R A1 A2 AR).
Check List_map2b: forall A1 A2 AR UR, Map2b.Has (List_R A1 A2 AR).
Check List_map3: forall A1 A2 AR UR, Map3.Has (List_R A1 A2 AR).
Check List_map4: forall A1 A2 AR UR, IsUMap (List_R A1 A2 AR).
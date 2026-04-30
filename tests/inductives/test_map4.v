From Trocq Require Import map4.
Require Import coverage.
Unset Uniform Inductive Parameters.

Elpi derive testFalse.
Check testFalse_mRRmK : forall f1 f2 fR, testFalse_mR f1 f2 (testFalse_Rm f1 f2 fR) = fR.

Elpi derive testUnit.
Check testUnit_mRRmK : forall u1 u2 uR, testUnit_mR u1 u2 (testUnit_Rm u1 u2 uR) = uR.

Elpi derive testBool.
Check testBool_mRRmK : forall b1 b2 bR, testBool_mR b1 b2 (testBool_Rm b1 b2 bR) = bR.

Elpi derive Wrap.
Check Wrap_mRRmK : forall w1 w2 wR, Wrap_mR w1 w2 (Wrap_Rm w1 w2 wR) = wR.

Elpi derive WrapMore.
Check WrapMore_mRRmK : forall w1 w2 wR, WrapMore_mR w1 w2 (WrapMore_Rm w1 w2 wR) = wR.

Elpi derive Nat.
Check Nat_mRRmK : forall n1 n2 nR, Nat_mR n1 n2 (Nat_Rm n1 n2 nR) = nR.

Elpi derive Box.
Check Box_mRRmK : forall A1 A2 (AR : A1 -> A2 -> Type) (AM : Map4.Has AR), forall (b1 : Box A1) (b2 : Box A2) (bR : Box_R A1 A2 AR b1 b2),
  Box_mR A1 A2 AR AM b1 b2 (Box_Rm A1 A2 AR AM b1 b2 bR) = bR.

Elpi derive Option.
Check Option_mRRmK : forall A1 A2 (AR : A1 -> A2 -> Type) (AM : Map4.Has AR), 
  forall o1 o2 oR, Option_mR A1 A2 AR AM o1 o2 (Option_Rm A1 A2 AR AM o1 o2 oR) = oR.

Elpi derive Prod.
Check Prod_mRRmK : forall A1 A2 (AR : A1 -> A2 -> Type) (AM : Map4.Has AR) B1 B2 (BR : B1 -> B2 -> Type) (BM : Map4.Has BR), 
  forall p1 p2 pR, Prod_mR A1 A2 AR AM B1 B2 BR BM p1 p2 (Prod_Rm A1 A2 AR AM B1 B2 BR BM p1 p2 pR) = pR.

Elpi derive ThreeTypes.
Check ThreeTypes_mRRmK : 
forall A1 A2 (AR : A1 -> A2 -> Type) (AM : Map4.Has AR),
forall B1 B2 (BR : B1 -> B2 -> Type) (BM : Map4.Has BR),
forall C1 C2 (CR : C1 -> C2 -> Type) (CM : Map4.Has CR),
  forall t1 t2 tR, ThreeTypes_mR A1 A2 AR AM B1 B2 BR BM C1 C2 CR CM t1 t2 (ThreeTypes_Rm A1 A2 AR AM B1 B2 BR BM C1 C2 CR CM t1 t2 tR) = tR.

Elpi derive List.
Check List_mRRmK : forall A1 A2 (AR : A1 -> A2 -> Type) (AM : Map4.Has AR), forall l1 t2 lR, List_mR A1 A2 AR AM l1 t2 (List_Rm A1 A2 AR AM l1 t2 lR) = lR.
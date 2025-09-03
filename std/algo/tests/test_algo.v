From Trocq Require Import algo.
From Trocq Require Import coverage.
Unset Uniform Inductive Parameters.

Elpi derive False.
Check False_mRRmK : forall f1 f2 fR, False_mR f1 f2 (False_Rm f1 f2 fR) = fR.

Elpi derive Unit.
Check Unit_mRRmK : forall u1 u2 uR, Unit_mR u1 u2 (Unit_Rm u1 u2 uR) = uR.

Elpi derive Bool.
Check Bool_mRRmK : forall b1 b2 bR, Bool_mR b1 b2 (Bool_Rm b1 b2 bR) = bR.

Elpi derive Wrap.
Check Wrap_mRRmK : forall w1 w2 wR, Wrap_mR w1 w2 (Wrap_Rm w1 w2 wR) = wR.

Elpi derive WrapMore.
Check WrapMore_mRRmK : forall w1 w2 wR, WrapMore_mR w1 w2 (WrapMore_Rm w1 w2 wR) = wR.

Elpi derive Nat.
Check Nat_mRRmK : forall n1 n2 nR, Nat_mR n1 n2 (Nat_Rm n1 n2 nR) = nR.

Elpi derive Box.
Check Box_mRRmK : forall A1 A2 (AR : Param40.Rel A1 A2), forall (b1 : Box A1) (b2 : Box A2) (bR : Box_R A1 A2 AR b1 b2),
  Box_mR A1 A2 AR b1 b2 (Box_Rm A1 A2 AR b1 b2 bR) = bR.

Elpi derive Option.
Check Option_mRRmK : forall A1 A2 (AR : Param40.Rel A1 A2), forall o1 o2 oR, Option_mR A1 A2 AR o1 o2 (Option_Rm A1 A2 AR o1 o2 oR) = oR.

Elpi derive Prod.
Check Prod_mRRmK : forall A1 A2 (AR : Param40.Rel A1 A2) B1 B2 (BR : Param40.Rel B1 B2), 
  forall p1 p2 pR, Prod_mR A1 A2 AR B1 B2 BR p1 p2 (Prod_Rm A1 A2 AR B1 B2 BR p1 p2 pR) = pR.

Elpi derive ThreeTypes.
Check ThreeTypes_mRRmK : 
forall A1 A2 (AR : Param40.Rel A1 A2), 
forall B1 B2 (BR : Param40.Rel B1 B2), 
forall C1 C2 (CR : Param40.Rel C1 C2), 
  forall t1 t2 tR, ThreeTypes_mR A1 A2 AR B1 B2 BR C1 C2 CR t1 t2 (ThreeTypes_Rm A1 A2 AR B1 B2 BR C1 C2 CR t1 t2 tR) = tR.

Elpi derive List.
Check List_mRRmK : forall A1 A2 (AR : Param40.Rel A1 A2), forall l1 t2 lR, List_mR A1 A2 AR l1 t2 (List_Rm A1 A2 AR l1 t2 lR) = lR.
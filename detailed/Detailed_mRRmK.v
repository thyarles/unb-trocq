From Coq Require Import ssreflect ssrfun ssrbool.
From Trocq.Algo Require Import mR Rm injK.
From Trocq.Tests Require Import coverage.
From Trocq Require Import HoTT_additions Hierarchy.
Unset Uniform Inductive Parameters.

Elpi derive.param2 False.
Elpi derive.mymap False.
Elpi derive.projK False.
Elpi derive.injections False.
Elpi derive.isK False.
Elpi derive.mR False.
Elpi derive.Rm False.
Elpi derive.injectionsK False.

Notation False_Pred := (fun w1 w2 wR => False_mR w1 w2 (False_Rm w1 w2 wR) = wR) (only parsing).
Definition False_mRRmK : forall (w1 w2 : False) (wR : False_R w1 w2), False_mR w1 w2 (False_Rm w1 w2 wR) = wR.
Proof.
refine (fun f1 f2 fR => _).
exact (False_R_ind False_Pred f1 f2 fR).
Defined.

Elpi derive.param2 Unit.
Elpi derive.mymap Unit.
Elpi derive.projK Unit.
Elpi derive.injections Unit.
Elpi derive.isK Unit.
Elpi derive.mR Unit.
Elpi derive.Rm Unit.

Notation Unit_Pred := (fun u1 u2 uR => Unit_mR u1 u2 (Unit_Rm u1 u2 uR) = uR).
Definition Unit_mRRmK : forall (w1 w2 : Unit) (wR : Unit_R w1 w2), Unit_mR w1 w2 (Unit_Rm w1 w2 wR) = wR.
Proof.
refine (fun u1 u2 uR=> _).
refine (Unit_R_ind Unit_Pred _ u1 u2 uR).
- exact (@eq_refl (Unit_R TT TT) TT_R).
Defined.

Elpi derive.param2 Bool.
Elpi derive.mymap Bool.
Elpi derive.isK Bool.
Elpi derive.mR Bool.
Elpi derive.Rm Bool.

Notation Bool_Pred := (fun b1 b2 bR => Bool_mR b1 b2 (Bool_Rm b1 b2 bR) = bR).
Definition Bool_mRRmK : forall (w1 w2 : Bool) (wR : Bool_R w1 w2), Bool_mR w1 w2 (Bool_Rm w1 w2 wR) = wR.
Proof.
refine (fun b1 b2 bR=> _).
refine (Bool_R_ind Bool_Pred _ _ b1 b2 bR).
- exact (@eq_refl (Bool_R Falseb Falseb) Falseb_R).
- exact (@eq_refl (Bool_R Trueb Trueb) Trueb_R).
Defined.

Elpi derive.param2 Wrap.
Elpi derive.mymap Wrap.
Elpi derive.projK Wrap.
Elpi derive.injections Wrap.
Elpi derive.mR Wrap.
Elpi derive.Rm Wrap.
Elpi derive.injectionsK Wrap.

Notation Wrap_Pred := (fun w1 w2 wR => Wrap_mR w1 w2 (Wrap_Rm w1 w2 wR) = wR) (only parsing).
Definition Wrap_mRRmK : forall (w1 w2 : Wrap) (wR : Wrap_R w1 w2), 
    Wrap_mR w1 w2 (Wrap_Rm w1 w2 wR) = wR.
Proof.
refine (fun w1 w2 wR=> _).
refine (Wrap_R_ind Wrap_Pred _ w1 w2 wR).
- refine (fun u1 u2 uR => _). 
refine (@eq_ind_r _ (Unit_Rm u1 u2 uR) (fun t=> KWrap1_R u1 u2 (Unit_mR u1 u2 t) = KWrap1_R u1 u2 uR) _ _ (Wrap_injK11 (Unit_mymap u1) u2 (Unit_Rm u1 u2 uR))).
refine (@eq_ind_r _ uR (fun t => KWrap1_R u1 u2 t = KWrap1_R u1 u2 uR) _ _ (Unit_mRRmK u1 u2 uR)).
exact (@eq_refl (Wrap_R (KWrap1 u1) (KWrap1 u2)) (KWrap1_R u1 u2 uR)).
Defined.

Definition Wrap_mRRmK' : forall (w1 w2 : Wrap) (wR : Wrap_R w1 w2), 
    Wrap_mR w1 w2 (Wrap_Rm w1 w2 wR) = wR.
Proof.
refine (fun w1 w2 wR=> _).
refine (Wrap_R_ind Wrap_Pred _ w1 w2 wR).
- refine (fun u1 u2 uR => _). 
refine (match 
(Wrap_injK11 (Unit_mymap u1) u2 (Unit_Rm u1 u2 uR))^ in _ = t 
return KWrap1_R u1 u2 (Unit_mR u1 u2 t) = KWrap1_R u1 u2 uR
with eq_refl => _ end
).
refine (match (Unit_mRRmK u1 u2 uR)^ in _ = t 
return KWrap1_R u1 u2 t = KWrap1_R u1 u2 uR
with eq_refl => eq_refl end
).
Defined.

Elpi derive.param2 WrapMore.
Elpi derive.mymap WrapMore.
Elpi derive.projK WrapMore.
Elpi derive.injections WrapMore.
Elpi derive.isK WrapMore.
Elpi derive.mR WrapMore.
Elpi derive.Rm WrapMore.
Elpi derive.injectionsK WrapMore.

(* From elpi.apps Require Import eltac.rewrite.

Axiom add_comm : forall x y, x + y = y + x.
Axiom mul_comm : forall x y, x * y = y * x.

Goal (forall x : nat, 1 + x = x + 1) -> 
    forall y,  2 * ((y+y) + 1) = ((y + y)+1) * 2.
Proof.
    intro H. 
    intro x.
    eltac.rewrite H.
    Show Proof.
    eltac.rewrite mul_comm.
    Show Proof.
    exact eq_refl.
Defined. *)

Notation WrapMore_Pred := (fun w1 w2 wR => WrapMore_mR w1 w2 (WrapMore_Rm w1 w2 wR) = wR) (only parsing).

Definition WrapMore_mRRmK : 
  forall (w1 w2 : WrapMore) (wR: WrapMore_R w1 w2), 
    WrapMore_mR w1 w2 (WrapMore_Rm w1 w2 wR) = wR.
Proof.
refine (fun w1 w2 wR => _).
refine (WrapMore_R_ind WrapMore_Pred _ _ _ w1 w2 wR).
- refine (fun u1 u2 uR => _).
  refine (fun b1 b2 bR => _).
  refine (match (WrapMore_injK11 (Unit_mymap u1) u2 (Unit_Rm _ _ uR) (Bool_mymap b1) b2 (Bool_Rm _ _ bR))^ in _ = t 
  return 
KWrap_R u1 u2 (Unit_mR u1 u2 t) b1 b2
(Bool_mR b1 b2
(WrapMore_injections12
(Unit_mymap u1) u2 (Bool_mymap b1)
b2
(bcongr.eq_f Unit WrapMore
(KWrap^~ (Bool_mymap b1))
(Unit_mymap u1) u2
(Unit_Rm u1 u2 uR) @
bcongr.eq_f Bool WrapMore
[eta KWrap u2] (Bool_mymap b1) b2
(Bool_Rm b1 b2 bR)))) =
KWrap_R u1 u2 uR b1 b2 bR 
with eq_refl => _ end).
  refine (match (Unit_mRRmK _ _ uR)^ in _ = t return 
  KWrap_R u1 u2 t b1 b2
(Bool_mR b1 b2
(WrapMore_injections12
(Unit_mymap u1) u2 (Bool_mymap b1)
b2
(bcongr.eq_f Unit WrapMore
(KWrap^~ (Bool_mymap b1))
(Unit_mymap u1) u2
(Unit_Rm u1 u2 uR) @
bcongr.eq_f Bool WrapMore
[eta KWrap u2] (Bool_mymap b1) b2
(Bool_Rm b1 b2 bR)))) =
KWrap_R u1 u2 uR b1 b2 bR
with eq_refl => _  end).
refine (match (WrapMore_injK12 (Unit_mymap u1) u2 (Unit_Rm _ _ uR) (Bool_mymap b1) b2 (Bool_Rm _ _ bR))^ in _ = t 
return 
KWrap_R u1 u2 uR b1 b2
(Bool_mR b1 b2 t) =
KWrap_R u1 u2 uR b1 b2 bR
with eq_refl => _ end
).
refine (match (Bool_mRRmK _ _ bR)^ in _ = t return 
KWrap_R u1 u2 uR b1 b2 t =
KWrap_R u1 u2 uR b1 b2 bR
with eq_refl => eq_refl end
).
- move=> wr1 wr2 wrR. 
simpl.
by rewrite WrapMore_injK21 Wrap_mRRmK.
- move=> ? ? ? ? ? ? ? ? ?. 
  by rewrite /= WrapMore_injK31 WrapMore_injK32 WrapMore_injK33 !Unit_mRRmK.
Defined.

Elpi derive.param2 Nat.
Elpi derive.mymap Nat.
Elpi derive.projK Nat.
Elpi derive.injections Nat.
Elpi derive.isK Nat.
Elpi derive.mR Nat.
Elpi derive.Rm Nat.
Elpi derive.injectionsK Nat.

Notation Nat_Pred := (fun n1 n2 nR => Nat_mR n1 n2 (Nat_Rm n1 n2 nR) = nR) (only parsing).

Definition Nat_mRRmK : 
  forall (n1 n2 : Nat ) (nR: Nat_R n1 n2), 
    Nat_mR n1 n2 (Nat_Rm n1 n2 nR) = nR.
Proof.
  fix f 3.
refine (fun n1 n2 nR => _).
refine (Nat_R_ind Nat_Pred _ _ n1 n2 nR).
- exact eq_refl.
- refine (fun n1' n2' nR' Hrec=> _ ).
simpl.
by rewrite Nat_injK21 f.
Defined.

Elpi derive.param2 Box.
Elpi derive.mymap Box.
Elpi derive.projK Box.
Elpi derive.injections Box.
Elpi derive.isK Box.
Elpi derive.mR Box.
Elpi derive.Rm Box.
Elpi derive.injectionsK Box.

Notation Box_Pred := (fun A1 A2 (AR : Param40.Rel A1 A2) => fun b1 b2 bR => Box_mR A1 A2 AR b1 b2 (Box_Rm A1 A2 AR b1 b2 bR) = bR) (only parsing).

Definition Box_mRRmK : 
forall (A1 A2 : Type) (AR : Param40.Rel A1 A2),
  forall (b1 : Box A1) (b2 : Box A2) (bR: Box_R A1 A2 AR b1 b2), 
    Box_mR A1 A2 AR b1 b2 (Box_Rm A1 A2 AR b1 b2 bR) = bR.
Proof.
refine (fun A1 A2 AR=> _).
refine (fun b1 b2 bR=> Box_R_ind A1 A2 AR (Box_Pred A1 A2 AR) _ b1 b2 bR).
refine (fun a1 a2 aR=> _).
simpl.
by rewrite Box_injK11 (R_in_mapK AR a1 a2 aR).
Defined.

Elpi derive.param2 Option.
Elpi derive.mymap Option.
Elpi derive.projK Option.
Elpi derive.injections Option.
Elpi derive.isK Option.
Elpi derive.mR Option.
Elpi derive.Rm Option.
Elpi derive.injectionsK Option.

Elpi derive.param2 Prod.
Elpi derive.mymap Prod.
Elpi derive.projK Prod.
Elpi derive.injections Prod.
Elpi derive.isK Prod.
Elpi derive.mR Prod.
Elpi derive.Rm Prod.
Elpi derive.injectionsK Prod.

Elpi derive.param2 ThreeTypes.
Elpi derive.mymap ThreeTypes.
Elpi derive.projK ThreeTypes.
Elpi derive.injections ThreeTypes.
Elpi derive.isK ThreeTypes.
Elpi derive.mR ThreeTypes.
Elpi derive.Rm ThreeTypes.
Elpi derive.injectionsK ThreeTypes.

Elpi derive.param2 List.
Elpi derive.mymap List.
Elpi derive.projK List.
Elpi derive.injections List.
Elpi derive.isK List.
Elpi derive.mR List.
Elpi derive.Rm List.
Elpi derive.injectionsK List.

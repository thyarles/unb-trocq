From Coq Require Import ssreflect ssrfun ssrbool.
From Trocq Require Import mR Rm injK.
From Trocq Require Import Hierarchy.
From Trocq Require Import HoTTNotations.
From Trocq Require Import coverage.
(* Search (?e ^). *)
(* From Trocq Require Import HoTT_additions Hierarchy. *)
Unset Uniform Inductive Parameters.

Elpi derive.param2 False.
Elpi derive.mymap False.
Elpi derive.projK False.
Elpi derive.injections False.
Elpi derive.isK False.
Elpi derive.mR False.
Elpi derive.Rm False.
Elpi derive.injK False.

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
Elpi derive.injK Wrap.

Notation Wrap_Pred := (fun w1 w2 wR => Wrap_mR w1 w2 (Wrap_Rm w1 w2 wR) = wR) (only parsing).
Definition Wrap_mRRmK : forall (w1 w2 : Wrap) (wR : Wrap_R w1 w2), 
    Wrap_mR w1 w2 (Wrap_Rm w1 w2 wR) = wR.
Proof.
refine (fun w1 w2 wR=> _).
refine (Wrap_R_ind Wrap_Pred _ w1 w2 wR).
- refine (fun u1 u2 uR => _). 
refine (@eq_ind _ _ (fun t=> KWrap1_R _ _ (Unit_mR u1 u2 t) = KWrap1_R u1 u2 uR) _ _ (Wrap_injK11 (Unit_mymap u1) u2 (Unit_Rm u1 u2 uR))^).
refine (@eq_ind _ uR (fun t => KWrap1_R u1 u2 t = KWrap1_R u1 u2 uR) _ _ (Unit_mRRmK u1 u2 uR)^).
exact (@eq_refl (Wrap_R (KWrap1 u1) (KWrap1 u2)) (KWrap1_R u1 u2 uR)).
Defined.

Definition Wrap_mRRmK' : forall (w1 w2 : Wrap) (wR : Wrap_R w1 w2), 
    Wrap_mR w1 w2 (Wrap_Rm w1 w2 wR) = wR.
Proof.
refine (fun w1 w2 wR=> _).
refine (Wrap_R_ind Wrap_Pred _ w1 w2 wR).
- refine (fun u1 u2 uR => _).
unfold Wrap_mR.
unfold Wrap_Rm.
unfold Wrap_R_ind.
simpl.
cbv.
refine (match 
(@eq_sym _ _ _ (Wrap_injK11 (Unit_mymap u1) u2 (Unit_Rm u1 u2 uR))) 
(* (Wrap_injK11 (Unit_mymap u1) u2 (Unit_Rm u1 u2 uR))^ *)
(* in _ = t 
return KWrap1_R u1 u2 (Unit_mR u1 u2 t) = KWrap1_R u1 u2 uR *)
with eq_refl => _ end
).
Show Proof.

refine (match (Unit_mRRmK u1 u2 uR)^ in _ = t 
(* return KWrap1_R u1 u2 t = KWrap1_R u1 u2 uR *)
with eq_refl => eq_refl end
).
Show Proof.
Defined.

Elpi derive.param2 WrapMore.
Elpi derive.mymap WrapMore.
Elpi derive.projK WrapMore.
Elpi derive.injections WrapMore.
Elpi derive.isK WrapMore.
Elpi derive.mR WrapMore.
Elpi derive.Rm WrapMore.
Elpi derive.injK WrapMore.

Notation WrapMore_Pred := (fun w1 w2 wR => WrapMore_mR w1 w2 (WrapMore_Rm w1 w2 wR) = wR) (only parsing).

Definition WrapMore_mRRmK : 
  forall (w1 w2 : WrapMore) (wR: WrapMore_R w1 w2), 
    WrapMore_mR w1 w2 (WrapMore_Rm w1 w2 wR) = wR.
Proof.
refine (fun w1 w2 wR => _).
refine (WrapMore_R_ind WrapMore_Pred _ _ _ w1 w2 wR).
- refine (fun u1 u2 uR => _).
  refine (fun b1 b2 bR => _).
  unfold WrapMore_mR.
  refine (match (WrapMore_injK11 (Unit_mymap u1) u2 (Unit_Rm _ _ uR) (Bool_mymap b1) b2 (Bool_Rm _ _ bR))^ 
  (* in _ = t 
  return 
KWrap_R u1 u2 (Unit_mR u1 u2 (Unit_Rm u1 u2 uR)) b1 b2
(Bool_mR b1 b2
(WrapMore_injections12 (Unit_mymap u1) u2
(Bool_mymap b1) b2
(WrapMore_Rm (KWrap u1 b1) (KWrap u2 b2)
(KWrap_R u1 u2 uR b1 b2 bR)))) =
KWrap_R u1 u2 uR b1 b2 bR
 *)

(* KWrap_R u1 u2 (Unit_mR u1 u2 t) b1 b2 _ = 
_ *)
(* (Bool_mR b1 b2
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
KWrap_R u1 u2 uR b1 b2 bR  *)
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
set RWe1 := (WrapMore_injK12 (Unit_mymap u1) u2 (Unit_Rm _ _ uR) (Bool_mymap b1) b2 (Bool_Rm _ _ bR))^.
set eqf1 := bcongr.eq_f _ _ _ _ _ _.
set eqf2 := bcongr.eq_f _ _ _ _ _ _.
set T := WrapMore_injections12 (Unit_mymap u1) u2 (Bool_mymap b1) b2
(bcongr.eq_f Unit WrapMore (KWrap^~ (Bool_mymap b1)) (Unit_mymap u1) u2
(Unit_Rm u1 u2 uR) @
(bcongr.eq_f Bool WrapMore [eta KWrap u2] (Bool_mymap b1) b2 (Bool_Rm b1 b2 bR) @
1)).
refine (match (WrapMore_injK12 (Unit_mymap u1) u2 (Unit_Rm _ _ uR) (Bool_mymap b1) b2 (Bool_Rm _ _ bR))^ 
(* in _ = t  *)
(* return 
KWrap_R u1 u2 uR b1 b2
(Bool_mR b1 b2 t) =
KWrap_R u1 u2 uR b1 b2 bR *)
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
- move=> u1 u2 uR1 u3 u4 uR2 u5 u6 uR3.
simpl.
  by rewrite /= WrapMore_injK31 WrapMore_injK32 WrapMore_injK33 !Unit_mRRmK.
Defined.

Elpi derive.param2 Nat.
Elpi derive.mymap Nat.
Elpi derive.projK Nat.
Elpi derive.injections Nat.
Elpi derive.isK Nat.
Elpi derive.mR Nat.
Elpi derive.Rm Nat.
Elpi derive.injK Nat.
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
by rewrite Nat_injK21 f.
Defined.

Elpi derive.param2 Box.
Elpi derive.mymap Box.
Elpi derive.projK Box.
Elpi derive.injections Box.
Elpi derive.isK Box.
Elpi derive.mR Box.
Elpi derive.Rm Box.
Elpi derive.injK Box.

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
Elpi derive.injK Option.

Elpi derive.param2 Prod.
Elpi derive.mymap Prod.
Elpi derive.projK Prod.
Elpi derive.injections Prod.
Elpi derive.isK Prod.
Elpi derive.mR Prod.
Elpi derive.Rm Prod.
Elpi derive.injK Prod.

Notation Prod_Pred := (fun A1 A2 (AR : Param40.Rel A1 A2) A3 A4 (AR2 : Param40.Rel A3 A4) => 
  fun p1 p2 pR => Prod_mR A1 A2 AR A3 A4 AR2 p1 p2 (Prod_Rm A1 A2 AR A3 A4 AR2 p1 p2 pR) = pR) (only parsing).
Definition Prod_mRRmK : 
forall (A1 A2 : Type) (AR : Param40.Rel A1 A2),
  forall (A3 A4 : Type) (AR2 : Param40.Rel A3 A4),
  forall (p1 : Prod A1 A3) (p2 : Prod A2 A4) (pR: Prod_R A1 A2 AR A3 A4 AR2 p1 p2), 
    Prod_mR A1 A2 AR A3 A4 AR2 p1 p2 (Prod_Rm A1 A2 AR A3 A4 AR2 p1 p2 pR) = pR.
Proof.
refine (fun A1 A2 AR=> _).
refine (fun A3 A4 AR2=> _).
refine (fun p1 p2 pR=> Prod_R_ind A1 A2 AR A3 A4 AR2 (Prod_Pred A1 A2 AR A3 A4 AR2) _ p1 p2 pR).
refine (fun a1 a2 aR=> _).
refine (fun b1 b2 bR=> _).
unfold Prod_mR.
Check PR.
simpl.
by rewrite Prod_injK11 Prod_injK12 (R_in_mapK AR a1 a2 aR) (R_in_mapK AR2 b1 b2).
Defined.

Elpi derive.param2 Mix.
(* Fail Elpi derive.mymap Mix. 
TODO: fix universe issue
*)
Elpi derive.projK Mix.
Elpi derive.injections Mix.
Elpi derive.isK Mix.
Elpi derive.mR Mix.
Elpi derive.Rm Mix.
Elpi derive.injK Mix.

Elpi derive.param2 ThreeTypes.
Elpi derive.mymap ThreeTypes.
Elpi derive.projK ThreeTypes.
Elpi derive.injections ThreeTypes.
Elpi derive.isK ThreeTypes.
Elpi derive.mR ThreeTypes.
Elpi derive.Rm ThreeTypes.
Elpi derive.injK ThreeTypes.

Elpi derive.param2 List.
Elpi derive.mymap List.
Elpi derive.projK List.
Elpi derive.injections List.
Elpi derive.isK List.
Elpi derive.mR List.
Elpi derive.Rm List.
Elpi derive.injK List.

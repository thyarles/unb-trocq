From Coq Require Import ssreflect ssrfun ssrbool.
From Trocq.Algo Require Import mR Rm.
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

Elpi derive.param2 Unit.
Elpi derive.mymap Unit.
Elpi derive.projK Unit.
Elpi derive.injections Unit.
Elpi derive.isK Unit.
Elpi derive.mR Unit.
Elpi derive.Rm Unit.

Elpi derive.param2 Bool.
Elpi derive.mymap Bool.
Elpi derive.isK Bool.
Elpi derive.mR Bool.
Elpi derive.Rm Bool.

Elpi derive.param2 Wrap.
Elpi derive.mymap Wrap.
Elpi derive.projK Wrap.
Elpi derive.injections Wrap.
Elpi derive.mR Wrap.
Elpi derive.Rm Wrap.

Definition conv (A : Type) (x y : A) (p: x = y) 
    (P : forall x0 : A, x = x0 -> Prop) (P0 : P x eq_refl) :=
  match p as p0 in _ = t return (P t p0)
   with eq_refl => P0 end.


Notation Wrap_Pred_inj11K := (fun (u1 u2 :Unit) (p : u1 = u2) => 
(Wrap_injections11 u1 u2 
    (bcongr.eq_f Unit Wrap (fun R : Unit => KWrap1 R) u1 u2 p) = p)) (only parsing).
Definition Wrap_inj11K : 
 forall (u1 u2 : Unit) (p : u1 = u2),
 Wrap_Pred_inj11K u1 u2 p.
Proof.
refine (fun u1 u2 p1=> _).
refine (conv _ u1 u2 p1 (Wrap_Pred_inj11K u1) _).
exact (@eq_refl (@eq Unit u1 u1) (@eq_refl Unit u1)).
Defined.

Elpi derive.param2 WrapMore.
Elpi derive.mymap WrapMore.
Elpi derive.projK WrapMore.
Elpi derive.injections WrapMore.
Elpi derive.isK WrapMore.
Elpi derive.mR WrapMore.
Elpi derive.Rm WrapMore.

Notation WrapMore_Pred_inj1K := 
    (fun (u1 u2 :Unit) (p : u1 = u2) (b1 b2 : Bool)(p2 : b1 = b2) f => 
    (f u1 u2 b1 b2
        ((bcongr.eq_f Unit WrapMore (fun R : Unit => KWrap R b1) u1 u2 p) @ (bcongr.eq_f Bool WrapMore (fun R : Bool => KWrap u2 R) b1 b2 p2)))) (only parsing).

Notation WrapMore_Pred_inj11K := 
    (fun (u1 u2 :Unit) (p : u1 = u2) (b1 b2 : Bool)(p2 : b1 = b2)=> 
      (WrapMore_Pred_inj1K u1 u2 p b1 b2 p2 WrapMore_injections11) = p) (only parsing).

Notation WrapMore_Pred_inj12K := 
    (fun (u1 u2 :Unit) (p : u1 = u2) (b1 b2 : Bool)(p2 : b1 = b2)=> 
      (WrapMore_Pred_inj1K u1 u2 p b1 b2 p2 WrapMore_injections12) = p2) (only parsing).

Definition WrapMore_inj11K : 
 forall (u1 u2 : Unit) (p : u1 = u2),
 forall (b1 b2 : Bool) (p2 : b1 = b2),
WrapMore_Pred_inj11K u1 u2 p b1 b2 p2. 
Proof.
refine (fun u1 u2 p1=> _).
refine (fun b1 b2 p2=> _).
refine (conv _ u1 u2 p1 (fun (t : Unit) (p : u1 = t) => (WrapMore_Pred_inj11K u1 t p b1 b2 p2)) _). 
refine (conv _ b1 b2 p2 (fun (t : Bool) (p : b1 = t) => (WrapMore_Pred_inj11K u1 u1 1 b1 t p)) _).
exact (@eq_refl (@eq Unit u1 u1) (@eq_refl Unit u1)).
Defined.

Definition WrapMore_inj12K : 
 forall (u1 u2 : Unit) (p : u1 = u2),
 forall (b1 b2 : Bool) (p2 : b1 = b2),
 WrapMore_Pred_inj12K u1 u2 p b1 b2 p2.
Proof.
refine (fun u1 u2 p1=> _).
refine (fun b1 b2 p2=> _).
refine (conv _ u1 u2 p1 (fun (t : Unit) (p : u1 = t) => (WrapMore_Pred_inj12K u1 t p b1 b2 p2)) _). 
refine (conv _ b1 b2 p2 (fun (t : Bool) (p : b1 = t) => (WrapMore_Pred_inj12K u1 u1 1 b1 t p)) _).
exact (@eq_refl (@eq Bool b1 b1) (@eq_refl Bool b1)).
Defined.

Notation WrapMore_Pred_inj2K := 
    (fun (w1 w2 :Wrap) (p : w1 = w2) f => 
    (f w1 w2
        (bcongr.eq_f Wrap WrapMore (fun R : Wrap => KWrapWrap R) w1 w2 p))) (only parsing).

Notation WrapMore_Pred_inj21K := 
    (fun (w1 w2 :Wrap) (p : w1 = w2) => 
    WrapMore_Pred_inj2K w1 w2 p WrapMore_injections21 = p) (only parsing).

Definition WrapMore_inj21K : 
  forall (w1 w2 : Wrap) (p : w1 = w2),
  WrapMore_Pred_inj21K w1 w2 p.
Proof.
refine (fun w1 w2 p=> _).
refine (conv _ w1 w2 p (fun t p => WrapMore_Pred_inj21K w1 t p) _).
exact (@eq_refl (@eq Wrap w1 w1) (@eq_refl Wrap w1)).
Defined.

Notation WrapMore_Pred_inj3K := 
    (fun (u1 u2 : Unit) (p : u1 = u2) (u3 u4 : Unit) (p2 : u3 = u4) (u5 u6 : Unit) (p3 : u5 = u6) f => 
    (f u1 u2 u3 u4 u5 u6
        ((bcongr.eq_f Unit WrapMore (fun R : Unit => F R u3 u5) u1 u2 p)
        @ (bcongr.eq_f Unit WrapMore (fun R : Unit => F u2 R u5) u3 u4 p2)
        @ (bcongr.eq_f Unit WrapMore (fun R : Unit => F u2 u4 R) u5 u6 p3)))) (only parsing).

Notation WrapMore_Pred_inj31K := 
    (fun (u1 u2 : Unit) (p : u1 = u2) (u3 u4 : Unit) (p2 : u3 = u4) (u5 u6 : Unit) (p3 : u5 = u6) => 
        WrapMore_Pred_inj3K u1 u2 p u3 u4 p2 u5 u6 p3 WrapMore_injections31 = p )(only parsing).

Notation WrapMore_Pred_inj32K := 
    (fun (u1 u2 : Unit) (p : u1 = u2) (u3 u4 : Unit) (p2 : u3 = u4) (u5 u6 : Unit) (p3 : u5 = u6) => 
        WrapMore_Pred_inj3K u1 u2 p u3 u4 p2 u5 u6 p3 WrapMore_injections32 = p2 )(only parsing).

Notation WrapMore_Pred_inj33K := 
    (fun (u1 u2 : Unit) (p : u1 = u2) (u3 u4 : Unit) (p2 : u3 = u4) (u5 u6 : Unit) (p3 : u5 = u6) => 
        WrapMore_Pred_inj3K u1 u2 p u3 u4 p2 u5 u6 p3 WrapMore_injections33 = p3 )(only parsing).

Definition WrapMore_inj31K : 
  forall (u1 u2 : Unit) (p : u1 = u2) (u3 u4 : Unit) (p2 : u3 = u4) (u5 u6 : Unit) (p3 : u5 = u6),
    WrapMore_Pred_inj31K u1 u2 p u3 u4 p2 u5 u6 p3.
Proof.
refine (fun u1 u2 p=> _).
refine (fun u3 u4 p2=> _).
refine (fun u5 u6 p3=> _).
refine (conv _ u1 u2 p (fun t p => WrapMore_Pred_inj31K u1 t p u3 u4 p2 u5 u6 p3) _).
refine (conv _ u3 u4 p2 (fun t p => WrapMore_Pred_inj31K u1 u1 1 u3 t p u5 u6 p3) _).
refine (conv _ u5 u6 p3 (fun t p => WrapMore_Pred_inj31K u1 u1 1 u3 u3 1 u5 t p) _).
refine (@eq_refl (@eq Unit u1 u1) (@eq_refl Unit u1)).
Defined.
  
Definition WrapMore_inj32K : 
  forall (u1 u2 : Unit) (p : u1 = u2) (u3 u4 : Unit) (p2 : u3 = u4) (u5 u6 : Unit) (p3 : u5 = u6),
    WrapMore_Pred_inj32K u1 u2 p u3 u4 p2 u5 u6 p3.
Proof.
refine (fun u1 u2 p=> _).
refine (fun u3 u4 p2=> _).
refine (fun u5 u6 p3=> _).
refine (conv _ u1 u2 p  ((fun t p => WrapMore_Pred_inj32K u1 t p u3 u4 p2 u5 u6 p3)) _).
refine (conv _ u3 u4 p2 ((fun t p => WrapMore_Pred_inj32K u1 u1 1 u3 t p u5 u6 p3)) _).
refine (conv _ u5 u6 p3 ((fun t p => WrapMore_Pred_inj32K u1 u1 1 u3 u3 1 u5 t p) ) _).
refine (@eq_refl (@eq Unit u3 u3) (@eq_refl Unit u3)).
Defined.

Definition WrapMore_inj33K : 
  forall (u1 u2 : Unit) (p : u1 = u2) (u3 u4 : Unit) (p2 : u3 = u4) (u5 u6 : Unit) (p3 : u5 = u6),
    WrapMore_Pred_inj33K u1 u2 p u3 u4 p2 u5 u6 p3.
Proof.
refine (fun u1 u2 p=> _).
refine (fun u3 u4 p2=> _).
refine (fun u5 u6 p3=> _).
refine (conv _ u1 u2 p (fun t p => WrapMore_Pred_inj33K u1 t p u3 u4 p2 u5 u6 p3) _).
refine (conv _ u3 u4 p2 (fun t p => WrapMore_Pred_inj33K u1 u1 1 u3 t p u5 u6 p3) _).
refine (conv _ u5 u6 p3 (fun t p => WrapMore_Pred_inj33K u1 u1 1 u3 u3 1 u5 t p) _).
refine (@eq_refl (@eq Unit u5 u5) (@eq_refl Unit u5)).
Defined.

Elpi derive.param2 Nat.
Elpi derive.mymap Nat.
Elpi derive.projK Nat.
Elpi derive.injections Nat.
Elpi derive.isK Nat.
Elpi derive.mR Nat.
Elpi derive.Rm Nat.

Notation nat_Pred_inj2K :=
  (fun (n1 n2 : Nat) (p : n1 = n2) f =>
    f n1 n2 (bcongr.eq_f Nat Nat (fun R => S' R) n1 n2 p)) (only parsing).
Notation nat_Pred_inj21K :=
  (fun (n1 n2 : Nat) (p : n1 = n2) =>
    nat_Pred_inj2K n1 n2 p Nat_injections21 = p) (only parsing).

Definition nat_inj21K : 
  forall (n1 n2 : Nat) (p : n1 = n2),
  nat_Pred_inj21K n1 n2 p.
Proof.
refine (fun n1 n2 p=> _).
refine (conv _ n1 n2 p (fun t p => nat_Pred_inj21K n1 t p) _).
refine (@eq_refl (@eq Nat n1 n1) (@eq_refl Nat n1)).
Defined.

Elpi derive.param2 Box.
Elpi derive.mymap Box.
Elpi derive.projK Box.
Elpi derive.injections Box.
Elpi derive.isK Box.
Elpi derive.mR Box.
Elpi derive.Rm Box.

Notation Box_Pred_inj1K :=
  (fun (A2: Type) (a1 a2 : A2) (p : a1 = a2) f =>
    f A2 a1 a2 (bcongr.eq_f A2 (@Box A2) (fun R => @B A2 R) a1 a2 p)) (only parsing).

Notation Box_Pred_inj11K :=
  (fun (A2: Type) (a1 a2 : A2) (p : a1 = a2) =>
  Box_Pred_inj1K A2 a1 a2 p Box_injections11 = p) (only parsing).

Definition Box_inj11K : 
  forall (A2: Type) (a1 a2 : A2) (p : a1 = a2),
  Box_Pred_inj11K A2 a1 a2 p.
Proof.
refine (fun A2=> _).
refine (fun a1 a2 p=> _).
refine (conv A2 a1 a2 p (fun t p => Box_Pred_inj11K A2 a1 t p) _).
refine (@eq_refl (@eq A2 a1 a1) (@eq_refl A2 a1)).
Defined.

Elpi derive.param2 Option.
Elpi derive.mymap Option.
Elpi derive.projK Option.
Elpi derive.injections Option.
Elpi derive.isK Option.
Elpi derive.mR Option.
Elpi derive.Rm Option.

Elpi derive.param2 Prod.
Elpi derive.mymap Prod.
Elpi derive.projK Prod.
Elpi derive.injections Prod.
Elpi derive.isK Prod.
Elpi derive.mR Prod.
Elpi derive.Rm Prod.

Elpi derive.param2 ThreeTypes.
Elpi derive.mymap ThreeTypes.
Elpi derive.projK ThreeTypes.
Elpi derive.injections ThreeTypes.
Elpi derive.isK ThreeTypes.
Elpi derive.mR ThreeTypes.
Elpi derive.Rm ThreeTypes.

Elpi derive.param2 List.
Elpi derive.mymap List.
Elpi derive.projK List.
Elpi derive.injections List.
Elpi derive.isK List.
Elpi derive.mR List.
Elpi derive.Rm List.


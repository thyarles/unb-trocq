From Coq Require Import ssreflect.
From elpi.apps.derive Require Import derive derive.param2.
From Trocq Require Import mymap.
 (* injection_lemmas. *)
Require Import HoTT_additions Hierarchy.
Unset Uniform Inductive Parameters.
(* Unset Universe Minimization ToSet. *)

Inductive False :=.
Elpi derive.param2 False.
Elpi derive.mymap False.
Definition false_Rm : forall (f1 f2 : False), False_R f1 f2 -> False_mymap f1 = f2.
Proof. 
(* refine (fun f1 f2 fR=> False_R_ind (fun (f1 f2 : False) => (False_R f1 f2) -> False_mymap f1 = f2) f1 f2 fR fR). *)
refine (fun f1 f2 fR=> False_R_ind (fun (f1 f2 : False) =>  False_mymap f1 = f2) f1 f2 fR).
Defined. 

Definition Unit := unit.

Elpi derive.param2 unit.
Definition UnitR := unit_R.
(* Inductive UnitR : Unit -> Unit -> Type :=
  | tt_R : UnitR tt tt. *)

Elpi derive.mymap unit.
Definition unit_map : unit -> unit := unit_mymap.

Definition Pred := fun (s1 s2: unit) (RR : unit_R s1 s2)=> unit_map s1 = s2 .
Definition unit_Rm : forall (u1 u2 : Unit), UnitR u1 u2-> unit_map u1 = u2 .
Proof.
refine (fun u1 u2 uR=> unit_R_ind Pred eq_refl u1 u2 uR).
Defined. 

Definition Bool := bool.
Elpi derive.param2 bool.

Definition BoolR := bool_R.
(* Inductive BoolR : Bool -> Bool -> Type :=
| true_R : BoolR true true 
| false_R : BoolR false false. *)

Elpi derive.mymap bool.
Definition bool_map : Bool -> Bool := bool_mymap.

Definition Pred_bool := (fun (s1 s2: bool) (RR : bool_R s1 s2)=> bool_map s1 = s2).
Definition bool_Rm : forall (u1 u2 : Bool), BoolR u1 u2 -> bool_map u1 = u2.
Proof.
refine (fun b1 b2 bR=> bool_R_ind Pred_bool _ _ b1 b2 bR).
+ exact (@eq_refl Bool true).
+ exact (@eq_refl Bool false).
Defined.

Inductive Wrap : Type :=
| KWrap1 : unit -> Wrap.

Elpi derive.param2 Wrap.
Definition WrapR := Wrap_R.
Elpi derive.mymap Wrap.

Definition wrap_map := Wrap_mymap.
About concat.
Notation Pred_wrap := (fun (w1 w2 : Wrap ) (wR : Wrap_R w1 w2) => wrap_map w1 = w2) (only parsing).
Definition wrap_Rm : forall w1 w2, WrapR w1 w2 -> wrap_map w1 = w2. 
Proof.
refine (fun w1 w2 wR => Wrap_R_ind Pred_wrap _ w1 w2 wR).
+ set eta1 := (fun R=> KWrap1 R).
  refine (fun u1 u2 uR=> _).
  set e1 := @ap unit Wrap eta1 (unit_map u1) u2 (unit_Rm u1 u2 uR).
  set end_ := @eq_refl Wrap (KWrap1 u2).
  exact (@eq_trans Wrap _ _ _ e1 end_).
Defined.

Inductive FArgsK : Type :=
| C1 : unit -> bool -> Wrap -> bool -> FArgsK.

Elpi derive.param2 FArgsK.
Elpi derive.mymap FArgsK.
Notation Pred_fargsk := (fun (f1 f2 : FArgsK)(fR : FArgsK_R f1 f2)=> FArgsK_mymap f1 = f2) (only parsing).
Definition Rm_fargsk : forall f1 f2 (fR : FArgsK_R f1 f2), FArgsK_mymap f1 = f2.
Proof.
refine (fun f1 f2 fR=> FArgsK_R_ind Pred_fargsk _ f1 f2 fR).
refine (fun u1 u2 uR=> _).
refine (fun b1 b2 bR=> _).
refine (fun w1 w2 wR=> _).
refine (fun b1' b2' bR'=> _).
set goal := FArgsK_mymap (C1 u1 b1 w1 b1') = C1 u2 b2 w2 b2'.
simpl in goal.
(* set start := @eq_refl FArgsK (FArgsK_mymap (C1 u1 b1 w1 b1')). *)
(* set start := @eq_refl FArgsK (C1 (unit_map u1) (bool_mymap b1) (Wrap_mymap w1) (bool_mymap b1')). *)
set eta1 := (fun R:unit => C1 R (bool_mymap b1) (Wrap_mymap w1) (bool_mymap b1')).
set eta2 := (fun R2:bool => C1 u2 R2 (Wrap_mymap w1) (bool_mymap b1')).
set eta3 := (fun R3:Wrap => C1 u2 b2 R3 (bool_mymap b1')).
set eta4 := (fun R4:bool => C1 u2 b2 w2 R4).
set e1 := @ap unit FArgsK eta1 (unit_map u1) u2 (unit_Rm u1 u2 uR).
set e2 := @ap bool FArgsK eta2 (bool_map b1) b2 (bool_Rm b1 b2 bR).
set e3 := @ap Wrap FArgsK eta3 (wrap_map w1) w2 (wrap_Rm w1 w2 wR).
set e4 := @ap bool FArgsK eta4 (bool_map b1') b2' (bool_Rm b1' b2' bR').
set end_ := @eq_refl FArgsK (C1 u2 b2 w2 b2').
exact (e1 @ e2 @ e3 @ e4 @ end_).
Defined.

Definition Nat := nat.
Elpi derive.param2 nat.

Definition NatR := nat_R.

Elpi derive.mymap nat.
Definition nat_map := nat_mymap.
Notation Pred_nat := (fun (n1 n2: nat) (nR : nat_R n1 n2) => nat_map n1 = n2) (only parsing).
Definition nat_Rm : forall n1 n2, NatR n1 n2 -> nat_map n1 = n2.
Proof.
fix F 3.
refine (fun n1 n2 nR=> nat_R_ind Pred_nat _ _ n1 n2 nR).
+ exact (@eq_refl nat O).
+ refine (fun n1' n2' nR' e=> _). 
  set eta1 := fun R => S R.
  have E1 := @ap nat nat S (nat_map n1') n2' (F n1' n2' nR').
  have end_ := @eq_refl nat (S n2').
  exact (E1 @ end_).
  Defined.

Inductive Box (A : Type) : Type := B : A -> Box A.
Elpi derive.param2 Box.
Elpi derive.mymap Box.
Print Box_R.


Print Box_R_ind.
(* The term "__R" has type "A_R _1 _2" while it is expected to have type
 "@Hierarchy.rel A1 A2 (forget_10_00 A1 A2 (forget_2b0_10 A1 A2 A_R)) _1 _2". *)
Notation Pred_Box := (fun A1 A2 (AR : Param2b0.Rel A1 A2) => (fun (b1 : Box A1) (b2 : Box A2) (bR : Box_R A1 A2 AR b1 b2)=> Box_mymap A1 A2 AR b1 = b2)) (only parsing).

(* Goal forall A1 A2 (AR: Param2b0.Rel A1 A2) b1 b2, Box_R A1 A2 AR b1 b2 -> Box_mymap A1 A2 AR b1 = b2.
simpl. *)

Definition box_Rm : 
(* forall (A1 A2 : Type) (AR : Param2b0.Rel A1 A2) (b1 : Box A1) (b2 : Box A2)
(_ : Box_R A1 A2 (@rel A1 A2 (forget_10_00 A1 A2 (forget_2b0_10 A1 A2 AR))) b1 b2),
@eq (Box A2) (Box_mymap A1 A2 (forget_2b0_10 A1 A2 AR) b1) b2. *)
forall A1 A2 (AR: Param2b0.Rel A1 A2) b1 b2, Box_R A1 A2 AR b1 b2 -> Box_mymap A1 A2 AR b1 = b2.
Proof.
refine (fun A1 A2 AR=> _).
refine (fun b1 b2 bR=> Box_R_ind A1 A2 AR (Pred_Box A1 A2 AR) _ b1 b2 bR).
refine (fun a1 a2 aR=> _).
 set eta1 := fun R => @B A2 R.
 have E1 := @ap A2 (@Box A2) eta1 (map AR a1) a2 (R_in_map AR a1 a2 aR).
 have end_ := @eq_refl (@Box A2) (@B A2 a2).
 exact: (E1 @ end_).
Defined.

Definition Option (A : Type) : Type := option A.

Elpi derive.param2 option.
Definition OptionR := option_R.
(* Inductive OptionR (A1 A2 : Type) (AR : A1 -> A2 -> Type) : option A1 -> option A2 -> Type :=
| SomeR : forall a1 a2 (aR : AR a1 a2), OptionR A1 A2 AR (Some a1) (Some a2)
| NoneR : OptionR A1 A2 AR None None. *)

Elpi derive.mymap option.
Definition option_map := option_mymap.
(* Definition option_map (A1 A2 : Type) (AR : Param10.Rel A1 A2) : option A1 -> option A2 :=
fun oa => 
  match oa with 
  | Some a => Some (map AR a)
  | None => None
  end. *)

(* Elpi derive.injections option. *)
(* Print option_injections11. *)
Definition Pred_option := (fun A1 A2 (AR : Param2b0.Rel A1 A2)=> (fun (oa1 : option A1) (oa2 : option A2) (oaR : option_R A1 A2 AR oa1 oa2) => option_map A1 A2 AR oa1 = oa2)).
Definition option_Rm : forall (A1 A2 : Type) (AR : Param2b0.Rel A1 A2) oa1 oa2, OptionR A1 A2 AR oa1 oa2 -> option_map A1 A2 AR oa1 = oa2.
Proof.
refine (fun A1 A2 AR => _).
refine (fun oa1 oa2 oaR => option_R_ind A1 A2 AR (Pred_option A1 A2 AR) _ _ oa1 oa2 oaR).
+ refine (fun a1 a2 aR=> _).
  set eta1 := fun R => @Some A2 R. 
  have E1 := @ap A2 (@option A2) eta1 (map AR a1) a2 (R_in_map AR a1 a2 aR).
  have end_ := @eq_refl (@option A2) (@Some A2 a2).
  exact (E1 @ end_).
+ exact: @eq_refl (@option A2) (@None A2).  
Defined.
    
Definition List (A : Type) := list A.
Elpi derive.param2 list.

Definition ListR := list_R.
Elpi derive.mymap list.

Definition list_map := list_mymap.
Definition Pred_list := fun A1 A2 (AR : Param2b0.Rel A1 A2)=> (fun (l1: list A1) (l2: list A2) (lR : list_R A1 A2 AR l1 l2)=> list_map A1 A2 AR l1 = l2).

Definition list_Rm : forall (A1 A2 : Type) (AR : Param2b0.Rel A1 A2) l1 l2, ListR A1 A2 AR l1 l2 -> list_map A1 A2 AR l1 = l2.
Proof.
refine (fun A1 A2 AR=> _).
fix F 3.
refine (fun l1 l2 lR => list_R_ind A1 A2 AR (Pred_list A1 A2 AR) _ _ l1 l2 lR).
+ exact: (@eq_refl (@list A2) (@nil A2)).
+ refine (fun a1 a2 aR => _).
  refine (fun l1' l2' lR' e => _).
  set eta1 := fun R => @cons A2 R (list_map A1 A2 AR l1').
  set eta2 := fun R => @cons A2 a2 R.
  have E1 := @ap A2 (@list A2) eta1 (map AR a1) a2 (R_in_map AR a1 a2 aR). 
  have E2 := @ap (@list A2) (@list A2) eta2 (list_map A1 A2 AR l1') l2' (F l1' l2' lR'). 
  have end_ := (@eq_refl (@list A2) (@cons A2 a2 l2')).
  exact (E1 @ E2 @ end_).
Defined.


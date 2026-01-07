From Coq Require Import ssreflect.
From elpi.apps.derive Require Import derive derive.param2.
From Trocq Require Import mymap injection_lemmas.
Require Import Hierarchy.
(* Require Import HoTT_additions Hierarchy. *)
Unset Uniform Inductive Parameters.
(* Unset Universe Polymorphism. *)
Unset Universe Minimization ToSet.

Definition Unit := unit.

Elpi derive.param2 unit.
Definition UnitR := unit_R.
(* Inductive UnitR : Unit -> Unit -> Type :=
  | tt_R : UnitR tt tt. *)

Elpi derive.mymap unit.
Definition unit_map : unit -> unit := unit_mymap.
Definition Unit_mR : forall (u1 u2 : Unit), unit_map u1 = u2 -> UnitR u1 u2.
Proof.
refine (fun u1 => match u1 as u return 
                  forall u2 : Unit, unit_map u = u2 -> UnitR u u2
                  with 
                  | tt => _ end
                  ).
refine (fun u2 => match u2 as u return 
                 unit_map tt = u -> UnitR tt u 
                 with 
                 | tt => _ end).
refine (fun e => tt_R). 
Defined.

Definition Bool := bool.
Elpi derive.param2 bool.

Definition BoolR := bool_R.
(* Inductive BoolR : Bool -> Bool -> Type :=
| true_R : BoolR true true 
| false_R : BoolR false false. *)

Elpi derive.mymap bool.
Definition bool_map : Bool -> Bool := bool_mymap.
Definition Bool_mR : forall (u1 u2 : Bool), bool_map u1 = u2 -> BoolR u1 u2.
Proof.
refine (fun u1 : Bool => match u1 as u return 
                  forall u2 : Bool, bool_map u = u2 -> BoolR u u2
                  with 
                  | true => _ 
                  | false => _
                  end
                  ).
+ refine (fun u2 : Bool => match u2 as u return 
                           bool_map true = u -> BoolR true u
                           with 
                           | true => _ 
                           | false => _ 
                           end
                           ).
    - (* true true *)
    refine (fun e => true_R). 
    - (* true false *) intros e; discriminate e. 
+ refine (fun u2 : Bool => match u2 as u return 
                           bool_map false = u -> BoolR false u
                           with 
                           | true => _ 
                           | false => _ 
                           end
                           ).
    - (* false true *) intros e; discriminate e. 
    - (* false false *) refine (fun e => false_R). 
Defined.

Inductive Wrap : Type :=
| KWrap1 : unit -> Wrap.

Elpi derive.param2 Wrap.
Definition WrapR := Wrap_R.
Elpi derive.mymap Wrap.

Definition wrap_map := Wrap_mymap.
Elpi derive.projK Wrap.
Elpi derive.injections Wrap.
Definition wrap_mR : forall w1 w2, wrap_map w1 = w2 -> WrapR w1 w2.
Proof.
refine (fun w1=> match w1 as w return 
                 forall w2, wrap_map w = w2 -> WrapR w w2 
                 with 
                 | KWrap1 u1 => _ end).
- refine (fun w2=> match w2 as w return 
                   wrap_map (KWrap1 u1) = w -> WrapR (KWrap1 u1) w
                   with 
                   | KWrap1 u2 => _ end).
  refine (fun e => KWrap1_R u1 u2 (Unit_mR u1 u2 (Wrap_injections11 (unit_map u1) u2 e))).
Defined.

Definition Nat := nat.
Elpi derive.param2 nat.
Definition NatR := nat_R.

Elpi derive.mymap nat.
Definition nat_map := nat_mymap.
Elpi derive.injections nat.
Print nat_injections21.

Definition nat_mR : forall n1 n2, nat_map n1 = n2 -> NatR n1 n2.
Proof.
fix F 1.
refine (fun n1 => match n1 as n return 
                  forall n2, nat_map n = n2 -> NatR n n2 
                  with 
                  | O => _ 
                  | S n1' => _ end).
+ (* O *)
  refine (fun n2 => match n2 as n return
                    nat_map 0 = n -> NatR 0 n
                    with 
                    | O => _ 
                    | S n2' => _ end).
  - (* O O *)
    refine (fun e => O_R). 
  - (* O S n2' *) intros e; discriminate e.
+ (* S n' *)
  refine (fun n2 => match n2 as n return
                    nat_map (S n1') = n -> NatR (S n1') n
                    with 
                    | O => _ 
                    | S n2' => _ end).
  - (* S n1' O *) intros e; discriminate e.
  - (* S n1' S n2' *) 
    refine (fun e => S_R n1' n2' (F n1' n2' (nat_injections21 (nat_map n1') n2' e))).
Defined.

Inductive Box (A : Type) : Type := B : A -> Box A.
Elpi derive.param2 Box.
Elpi derive.mymap Box.
Elpi derive.projK Box.
Elpi derive.injections Box.
Elpi derive.isK Box.
Check @Trocq.Hierarchy.map.
Definition box_mR : forall A1 A2 (AR: Param2a0.Rel A1 A2) b1 b2, Box_mymap A1 A2 AR b1 = b2 -> Box_R A1 A2 AR b1 b2.
Proof.
refine (fun A1 A2 AR=> _).
refine (fun b1 b2=> _).
refine (match b1 as b0 return Box_mymap A1 A2 AR b0 = b2 -> Box_R A1 A2 AR b0 b2
        with B _ a1 => _ end).
        Set Printing All.
refine (match b2 as b0 return Box_mymap A1 A2 AR (B A1 a1) = b0 -> Box_R A1 A2 AR (B A1 a1) b0
        with B _ a2 => _ end).
refine (fun e => _).
simpl in e.
exact (B_R A1 A2 AR a1 a2 ((map_in_R AR) a1 a2 (Box_injections11 A2 ((map AR) a1) a2 e))).
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

Definition option_mR : forall (A1 A2 : Type) (AR : Param2a0.Rel A1 A2) oa1 oa2, option_map A1 A2 AR oa1 = oa2 -> OptionR A1 A2 AR oa1 oa2.
Proof.
refine (fun A1 A2 AR => _).
refine (fun oa1 => match oa1 as oa  
return forall oa2, option_map A1 A2 AR oa = oa2 -> OptionR A1 A2 AR oa oa2 
with 
                  | Some a1 => _ 
                  | None => _ end).
+ (* Some *) 
  refine (fun oa2 => match oa2 as oa 
                    return option_map A1 A2 AR (Some a1) = oa -> OptionR A1 A2 AR (Some a1) oa
                    with 
                    | Some a2 => _ 
                    | None => _ end).
  - (* Some Some *) 
    refine (fun e => Some_R A1 A2 AR a1 a2 (map_in_R AR a1 a2 (option_injections11 A2 (map AR a1) a2 e))).
  - (* Some None *) intros e; discriminate e.
+  (* None *)
  refine (fun oa2 => match oa2 as oa 
                    return option_map A1 A2 AR None = oa -> OptionR A1 A2 AR None oa
                    with 
                    | Some a2 => _ 
                    | None => _ end).
  - (* None Some *) intros e; discriminate e.
  - refine (fun e => None_R A1 A2 AR). 
Defined.
    
Definition List (A : Type) := list A.
Elpi derive.param2 list.

Definition ListR := list_R.
Elpi derive.mymap list.

Definition list_map := list_mymap.

Elpi derive.injections list.
Print list_injections21.

Print cons_R.
Definition list_mR : forall (A1 A2 : Type) (AR : Param2a0.Rel A1 A2) l1 l2, list_map A1 A2 AR l1 = l2 -> ListR A1 A2 AR l1 l2.
Proof.
refine (fun A1 A2 AR=> _).
fix F 1.
refine (fun l1 => match l1 as l 
                  return forall l2, list_map A1 A2 AR l = l2
                         -> ListR A1 A2 AR l l2 
                  with 
                  | nil => _ 
                  | cons a1 l1' => _ end).
+ (* nil *)
  refine (fun l2 => match l2 as l 
                    return list_map A1 A2 AR nil = l -> ListR A1 A2 AR nil l
                    with 
                    | nil => _ 
                    | cons a2 l2' => _ end).
  - (* nil nil *) 
    refine (fun e => nil_R A1 A2 AR).
  - intros e; discriminate e.
+ (* cons *)  
  refine (fun l2 => match l2 as l 
                    return list_map A1 A2 AR (cons a1 l1') = l -> ListR A1 A2 AR (cons a1 l1') l
                    with 
                    | nil => _ 
                    | cons a2 l2' => _ end).
  - intros e; discriminate e.
  - refine (fun e => cons_R A1 A2 AR 
                     a1 a2 (map_in_R AR a1 a2 (list_injections21 A2 (map AR a1) a2 (list_map A1 A2 AR l1') l2' e))
                     l1' l2' (F l1' l2' (list_injections22 A2 (map AR a1) a2 (list_map A1 A2 AR l1') l2' e))).
Defined.

Inductive ParamWrap (A : Type) :=
(* | PH : unit -> ParamWrap A *)
| SomeW : option A -> ParamWrap A.

Elpi derive.param2 ParamWrap.
Definition ParamWrapR := ParamWrap_R. 

Fail Elpi derive.mymap ParamWrap.
Fail Elpi derive.map ParamWrap.

(* Definition list_map := list_mymap. *)
Elpi derive.projK ParamWrap.
Elpi derive.injections ParamWrap.


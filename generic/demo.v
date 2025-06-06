From HB Require Import structures.
From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import eqtype.
Require Import HoTT_additions Hierarchy.
From elpi.apps Require Import derive.std.

Require Import param2_inhab.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Section rel_uniq_refl.

  Variable A : eqType.

  Variable AR : A -> A -> Type.
  Hypothesis AR_refl : forall a : A, AR a a.
  Hypothesis AR_eqb : forall a1 a2 : A, AR a1 a2 -> eq_op a1 a2.
  Hypothesis rel_refl_uniq : forall (a : A) (r1 : AR a a), r1 = (AR_refl a).

  Lemma eqb_AR (a1 a2 : A) : eq_op a1 a2 -> AR a1 a2.
  Proof. by move=> /eqP->; apply AR_refl. Qed.

  Lemma AR_irrel : forall (a1 a2 : A) (r1 r2 : AR a1 a2), r1 = r2.
  Proof.
    move=> a1 a2 r.
    have e : a1 = a2 by apply /eqP; apply AR_eqb.
    move: r; rewrite {}e=> r1 r2.
    by rewrite (rel_refl_uniq _ r1) (rel_refl_uniq _ r2).
  Qed.

  Definition mapR : A -> A := idmap.

  Lemma mR : forall a1 a2 : A, mapR a1 = a2 -> AR a1 a2.
  Proof. by move=> a1 a2; by rewrite /mapR=> ->; apply AR_refl. Qed.

  Lemma Rm : forall a1 a2 : A, AR a1 a2 -> idmap a1 = a2.
  Proof. by move=> /= a1 a2 /AR_eqb /eqP ->. Qed.

  Lemma mRRmK : forall (a1 a2 : A) (r : AR a1 a2), mR a1 a2 (Rm a1 a2 r) = r.
  Proof. by move=> a1 a2 r; apply AR_irrel. Qed.

  Lemma Map4_AR : Map4.Has AR.
  Proof.
    unshelve econstructor.
    by apply mapR.
    by apply mR.
    by apply Rm.
    by apply mRRmK.
  Qed.

  Lemma AR_sym : forall a1 a2, AR a1 a2 -> AR a2 a1.
  Proof. by move=> a1 a2 /AR_eqb/eqP ->; apply AR_refl. Qed.

  Lemma AR_sym_R : forall (a1 a2 : A), sym_rel AR a1 a2 <->> AR a1 a2.
  Proof.
    intros a1 a2; unshelve eexists _,_ .
    - by apply AR_sym.
    - by apply AR_sym.
    - by move=> r; apply AR_irrel.
  Qed.

  Lemma Param44_AR : Param44.Rel A A.
  Proof.
    unshelve econstructor.
    - exact AR.
    - exact Map4_AR.
    - apply (fun e => @eq_Map4 _ _ (sym_rel AR) AR e Map4_AR).
      apply AR_sym_R.
   Qed.

End rel_uniq_refl.

Unset Universe Polymorphism.
Require Import Coq.Program.Equality.

Inductive Bool := FF | TT.
Elpi derive Bool.
Elpi derive.param2.inhab Bool_R.

HB.instance Definition _ := hasDecEq.Build Bool Bool_eqb_OK.

  Lemma Param44_Bool : Param44.Rel Bool Bool.
  Proof.
    unshelve eapply (@Param44_AR Bool Bool_R).
    + exact: Bool_R_inhab. 
    + by move=> a1 a2 [].
    + by move=> a r1 /=; dependent destruction r1.
   Qed.

(* Require Import test_param. *)
  Module tests.

    Inductive empty := .
    Elpi derive empty.
    Elpi derive.param2.inhab empty_R.


    HB.instance Definition _ := hasDecEq.Build empty empty_eqb_OK.

    Lemma Param44_empty : Param44.Rel empty empty.
    Proof.
      unshelve eapply (@Param44_AR empty empty_R).
      + exact: empty_R_inhab.
      + by move=> a1 a2 [].
      + by move=> a r1 /=; dependent destruction r1.
    Qed.

    Inductive peano := Zero | Succ (n : peano).
    Elpi derive peano.
    Elpi derive.param2.inhab peano_R.
    HB.instance Definition _ := hasDecEq.Build peano peano_eqb_OK.
    

    Lemma peano_R_irrel n1 n2 (r1 r2 : peano_R n1 n2) : r1 = r2.
    Proof. by dependent induction r1=> [//|/=]; f_equal; dependent destruction r2=> //; f_equal; apply IHr1. Qed.
    Lemma Param44_peano : Param44.Rel peano peano.
    Proof.
      unshelve eapply (@Param44_AR peano peano_R).
      + exact: peano_R_inhab.
      + by move=> a1 a2; elim=> [//| n1 n2 r'] /eqP->.
      + by move=> a r1; apply peano_R_irrel.
    Qed.

    (* Inductive option A := None | Some (_ : A). *)

    (* Inductive pair A B := Comma (a : A) (b : B). *)

    (* Inductive seq A := Nil | Cons (x : A) (xs : seq A). *)

    Inductive box_peano := Box (n:peano).
    Elpi derive box_peano.
    Elpi derive.param2.inhab box_peano_R.
    HB.instance Definition _ := hasDecEq.Build box_peano box_peano_eqb_OK.

    Lemma Param44_box_peano : Param44.Rel box_peano box_peano.
    Proof.
      unshelve eapply (@Param44_AR box_peano box_peano_R).
      + exact: box_peano_R_inhab.
      + by move=> a1 a2; elim=> [n1 n2 r']; apply/eqP; f_equal; elim: r'=> [//| n1' n2' r''] ->.
      + move=> a /= r1; dependent destruction r1=> [].
        dependent destruction n_R=> [//|]; rewrite /=; f_equal.
        by apply peano_R_irrel.
    Qed.

    (* Inductive rose (A : Type) := Leaf (a : A) | Node (sib : seq (rose A)). *)

    (* Inductive rose_p (A B : Type) := Leafp (p : pair A B) | Nodep (sib : pair (rose_p A B) (rose_p A B)). *)

    (* Inductive rose_o (A : Type) := Leafo (a : A) | Nodeo (x: pair (rose A) (rose A)) (sib : option (seq (rose A))). *)

    (* Inductive nest A := NilN | ConsN (x : A) (xs : nest (pair A A)). *)

    (* Fail Inductive bush A := BNil | BCons (x : A) (xs : bush (bush A)). *)

    (* Inductive w A := via (f : A -> w A). *)

    (* Inductive vect A : peano -> Type := VNil : vect A Zero | VCons (x : A) n (xs : vect A n) : vect A (Succ n). *)

    (* Inductive dyn := box (T : Type) (t : T). *)

    (* Inductive zeta Sender (Receiver := Sender) := Envelope (a : Sender) (ReplyTo := a) (c : Receiver). *)

    (* Inductive beta (A : (fun x : Type => x) Type) := Redex (a : (fun x : Type => x) A). *)

    Inductive iota := Why n (a : match n in peano return Type with Zero => peano | Succ _ => unit end).
    (* Check iota. *)

    Inductive large :=
    | K1 (_ : unit)
    | K2 (_ : unit) (_ : unit)
    | K3 (_ : unit) (_ : unit) (_ : unit)
    | K4 (_ : unit) (_ : unit) (_ : unit) (_ : unit)
    | K5 (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit)
    | K6 (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit)
    | K7 (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit)
    | K8 (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit)
    | K9 (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit)
    | K10(_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit)
    | K11(_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit)
    | K12(_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit)
    | K13(_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit)
    | K14(_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit)
    | K15(_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit)
    | K16(_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit)
    | K17(_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit)
    | K18(_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit)
    | K19(_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit)
    | K20(_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit)
    | K21(_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit)
    | K22(_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit)
    | K23(_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit)
    | K24(_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit)
    | K25(_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit)
    | K26(_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit).

    Inductive prim_int := PI (i : PrimInt63.int).
    Inductive prim_float := PF (f : PrimFloat.float).
    (* Inductive prim_string := PS (s : lib:elpi.pstring). *)

    Record fo_record := { f1 : peano; f2 : unit; }.

    (* Record pa_record A := { f3 : peano; f4 : A; }. *)

    (* Set Primitive Projections. *)
    (* Record pr_record A := { pf3 : peano; pf4 : A; }. *)
    (* Unset Primitive Projections. *)

    (* Record dep_record := { f5 : peano; f6 : vect unit f5; }. *)

    Variant enum := E1 | E2 | E3.


    (* Record sigma_bool := { depn : peano; depeq : is_zero depn = true }. *)

    (* Record sigma_bool2 := { depn2 : peano; depeq2 : lib:elpi.is_true (is_zero depn2) }. *)

    Fixpoint is_leq (n m:peano) : bool := 
      match n, m with 
      | Zero, _ => true 
      | Succ n, Succ m => is_leq n m
      | _, _ => false
      end.

    Inductive ord (p : peano) := mkOrd (n : peano) (l : is_leq n p = true).

    Inductive ord2 (p : peano) := mkOrd2 (o1 o2 : ord p).

    Inductive val := V (p : peano) (oo : ord p).

  (* to make the coverage cound correct
Inductive eq := ...
Inductive bool := ...
we don't have a copy here because some DBs have special rules*)

  End tests.

  Elpi derive Inductive Peano := Zero | Succ (p : Peano).

  Section tests.

    Lemma RBool_refl (b : Bool) : BoolR b b.
    Proof. by case b; constructor. Defined.

    Require Import Coq.Program.Equality.

    Lemma RBool_uniq : forall b (bR : BoolR b b), bR = RBool_refl b.
    Proof.
      move=> b bR.
      by dependent induction bR.
    Qed.

    Lemma BoolRcorrect_another (b b' : Bool) (r : BoolR b b') : eqb_bool b b'.
    Proof. by apply BoolRcorrect. Defined.

    Lemma bool_eqDec : forall b1 b2, reflect (b1 = b2) (eqb_bool b1 b2).
    Proof.
      move=> b1 b2; apply (iffP idP).
      + by case: b1; case: b2.
      + by move=> ->; case: b2.
    Qed.

    Lemma Param44_Bool_another : Param44.Rel Bool Bool.
    Proof.
      eapply (Param44_AR Bool eqb_bool BoolR).
      - by apply BoolRcorrect_another.
      - by apply bool_eqDec.
      - exact RBool_uniq.
    Qed.


End tests.

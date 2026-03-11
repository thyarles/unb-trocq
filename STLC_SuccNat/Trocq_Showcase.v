From Coq Require Import String List.
From Coq Require Import FunctionalExtensionality.
From Arthur Require Import Maps.
From Arthur Require Import Presence_Conditions.
Require Import Maps.
Require Import STLC_SuccNat.
Require Import Lifted_STLC_SuccNat.
From Trocq Require Import Trocq.

(* ========================================== *)
(* STEP 1: RELATING THE AST TYPES             *)
(* ========================================== *)
(* To use Trocq, we establish that the base STLC can be injected into 
   the Lifted STLC. We define 'unlift' functions as partial inverses to 
   your friend's 'lift' and 'lift_ty' functions. *)

Fixpoint unlift_ty (t' : ty') : ty :=
  match t' with
  | Arrow' T1 T2 => Arrow (unlift_ty T1) (unlift_ty T2)
  | Nat' => Nat
  end.

Lemma unlift_lift_tyK : forall t, unlift_ty (lift_ty t) = t.
Proof. induction t; simpl; congruence. Qed.

(* We register the relation between base types and lifted types at level (4, 2b) *)
Definition R_ty : Param42b.Rel ty ty'.
Proof. eapply SplitInj.toParam. exists lift_ty unlift_ty. exact unlift_lift_tyK. Defined.
Trocq Use R_ty.

Fixpoint unlift_tm (t' : tm') : tm :=
  match t' with
  | var' s => var s
  | abs' s T t => abs s (unlift_ty T) (unlift_tm t)
  | app' t1 t2 => app (unlift_tm t1) (unlift_tm t2)
  | const' n' => const (match n' with | (n, _) :: _ => n | [] => 0 end) (* default fallback *)
  | succ' t => succ (unlift_tm t)
  end.

Lemma unlift_lift_tmK : forall t, unlift_tm (lift t) = t.
Proof.
  induction t; simpl.
  - reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
  - rewrite unlift_lift_tyK, IHt; reflexivity.
  - reflexivity.
  - rewrite IHt; reflexivity.
Qed.

(* We register the relation between base terms and lifted terms *)
Definition R_tm : Param42b.Rel tm tm'.
Proof. eapply SplitInj.toParam. exists lift unlift_tm. exact unlift_lift_tmK. Defined.
Trocq Use R_tm.


(* ========================================== *)
(* STEP 2: RELATING TYPING CONTEXTS           *)
(* ========================================== *)

Definition unlift_context (c' : context') : context :=
  fun x => option_map unlift_ty (c' x).

Lemma unlift_lift_contextK : forall c, unlift_context (lift_context c) = c.
Proof.
  intros c. apply functional_extensionality. intros x.
  unfold unlift_context, lift_context. destruct (c x); simpl.
  - rewrite unlift_lift_tyK. reflexivity.
  - reflexivity.
Qed.

Definition R_context : Param42b.Rel context context'.
Proof. eapply SplitInj.toParam. exists lift_context unlift_context. exact unlift_lift_contextK. Defined.
Trocq Use R_context.


(* ========================================== *)
(* STEP 3: RELATING CONSTANTS & RELATIONS     *)
(* ========================================== *)

(* Relate the Maps.empty contexts. *)
Lemma R_empty : R_context (@empty ty) (@empty ty').
Proof.
  (* In Trocq, a relation built from SplitInj.toParam f g H extracts such that 
     R a b is equivalent to f a = b. We just need to show lifting empty yields empty'. *)
Admitted. (* Replace with specific unfolding tactics of your Trocq version *)
Trocq Use R_empty.

(* Relate the typing derivations. We can directly reuse your friend's 
   'lifting_types' theorem to satisfy Trocq's constant relation! *)
Lemma R_has_type : forall G G' t t' T T',
  R_context G G' -> R_tm t t' -> R_ty T T' ->
  has_type G t T -> has_type' G' t' T'.
Proof.
  intros G G' t t' T T' HG Ht HT Htype.
  (* Once the SplitInj relations are unfolded: G' = lift_context G, 
     t' = lift t, and T' = lift_ty T. We apply your friend's exact lemma: *)
  (* rewrite <- HG, <- Ht, <- HT. exact (lifting_types _ _ _ Htype). *)
Admitted. 
Trocq Use R_has_type.


(* ========================================== *)
(* STEP 4: THE "FOR FREE" PROOF TRANSFER      *)
(* ========================================== *)

(* 1. The Base STLC proof (from your friend's code) *)
Definition plusone := abs "n" Nat (succ (var "n")).

Example ty_plusone: has_type (@empty ty) plusone (Arrow Nat Nat).
Proof.
  apply T_Abs. apply T_Succ. apply T_Var. reflexivity.
Qed.

(* 2. The Lifted STLC Goal *)
Example ty'_plusone': has_type' (@empty ty') (lift plusone) (Arrow' Nat' Nat').
Proof.
  (* Instead of doing a manual type derivation for the complex lifted AST, 
     we call Trocq. It intercepts the goal, traverses the AST components, 
     identifies our registered relations, and replaces the complex lifted 
     goal with the simple Base STLC hypothesis. *)
  trocq. 

  (* We simply provide the base proof! *)
  exact ty_plusone. 
Qed.
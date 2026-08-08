From Stdlib Require Import ssreflect.
From Trocq Require Import Trocq.
Require Import String.

Definition option_nat : Type := option nat.

Axiom fe : Funext.
Existing Instance fe.
Trocq Register Funext fe.

(* ================================================================= *)
(* 1. Map Definitions                                                *)
(* ================================================================= *)

Definition total_map (A : Type) := string -> A.

Definition tm_empty {A : Type} (v : A) : total_map A := fun _ => v.

Definition tm_update {A : Type} (m : total_map A) (x : string) (v : A) : total_map A :=
  fun x' => if String.eqb x x' then v else m x'.

Definition partial_map (A : Type) := total_map (option A).

Definition pm_empty {A : Type} : partial_map A := tm_empty None.

Definition pm_update {A : Type} (m : partial_map A) (x : string) (v : A) : partial_map A :=
  tm_update m x (Some v).

(* ================================================================= *)
(* 2. Source Theorem: tm_update_neq for total_map (option_nat)       *)
(* ================================================================= *)

Theorem tm_update_neq :
  forall (m : string -> option_nat) (x1 x2 : string) (v : option_nat),
    String.eqb x2 x1 = false -> (tm_update m x2 v) x1 = m x1.
Proof.
  intros m x1 x2 v Hneq.
  unfold tm_update.
  rewrite Hneq.
  reflexivity.
Qed.

(* ================================================================= *)
(* 3. Manual proof                                                   *)
(* ================================================================= *)

Theorem pm_update_neq_manual :
  forall (m : string -> option_nat) (x1 x2 : string) (v : nat),
    String.eqb x2 x1 = false -> (pm_update m x2 v) x1 = m x1.
Proof.
  intros m x1 x2 v Hneq.
  unfold pm_update.
  apply tm_update_neq.
  exact Hneq.
Qed.

(* ================================================================= *)
(* 4. Monomorphic aliases (ground GREFs for Trocq's database)        *)
(* ================================================================= *)

Definition _pm_update : (string -> option_nat) -> string -> nat -> (string -> option_nat)
  := @pm_update nat.
Definition _tm_update : (string -> option_nat) -> string -> option_nat -> (string -> option_nat)
  := @tm_update option_nat.

(* =================================================================== *)
(* 5. R_val : Param42b.Rel nat option_nat                              *)
(* =================================================================== *)

Lemma some_retrK : forall (n : nat),
  (fun o : option_nat => match o with Some m => m | None => O end) (Some n) = n.
Proof. reflexivity. Defined.

Definition R_val : Param42b.Rel nat option_nat :=
  SplitInj.toParam
    (@SplitInj.Build nat option_nat
       (@Some nat)
       (fun o : option_nat => match o with Some m => m | None => O end)
       some_retrK).

Trocq Use R_val.

Definition Param2a0_val : Param2a0.Rel nat option_nat := R_val.
Definition Param02b_val : Param02b.Rel nat option_nat := R_val.
Definition Param10_val  : Param10.Rel nat option_nat := R_val.
Definition Param01_val  : Param01.Rel nat option_nat := R_val.

Trocq Use Param2a0_val.
Trocq Use Param02b_val.
Trocq Use Param10_val.
Trocq Use Param01_val.

(* =================================================================== *)
(* 6. Param44_string                                                   *)
(* =================================================================== *)

Definition string_id (s : string) : string := s.

Lemma string_idK : forall (s : string), string_id (string_id s) = s.
Proof. reflexivity. Defined.

Definition Param44_string : Param44.Rel string string.
Proof.
  apply Iso.toParam; unshelve econstructor.
  - exact string_id.
  - exact string_id.
  - exact string_idK.
  - exact string_idK.
Defined.

Trocq Use Param44_string.

Definition Param2a0_string : Param2a0.Rel string string := Param44_string.
Definition Param02b_string : Param02b.Rel string string := Param44_string.
Definition Param10_string  : Param10.Rel string string := Param44_string.
Definition Param01_string  : Param01.Rel string string := Param44_string.
Definition Param00_string  : Param00.Rel string string := Param44_string.

Trocq Use Param2a0_string.
Trocq Use Param02b_string.
Trocq Use Param10_string.
Trocq Use Param01_string.
Trocq Use Param00_string.

Lemma R_eqb :
  rel (Param00_arrow string string Param44_string
         (string -> bool) (string -> bool)
         (Param00_arrow string string Param44_string bool bool Param44_Bool)) String.eqb String.eqb.
Proof.
  intros s1 s2 H1 s3 s4 H2.
  unfold rel in H1, H2.
  simpl in H1, H2.
  unfold graph in H1, H2.
  simpl in H1, H2.
  unfold string_id in H1, H2.
  subst s2 s4.
  unfold rel.
  simpl.
  destruct (String.eqb s1 s3).
  - constructor.
  - constructor.
Qed.

Trocq Use R_eqb.

Definition Param2a0_Bool : Param2a0.Rel bool bool := Param44_Bool.
Definition Param02b_Bool : Param02b.Rel bool bool := Param44_Bool.
Definition Param10_Bool  : Param10.Rel bool bool := Param44_Bool.
Definition Param01_Bool  : Param01.Rel bool bool := Param44_Bool.
Definition Param2b0_Bool : Param2b0.Rel bool bool := Param44_Bool.
Definition Param00_Bool  : Param00.Rel bool bool := Param44_Bool.

Trocq Use Param2a0_Bool.
Trocq Use Param02b_Bool.
Trocq Use Param10_Bool.
Trocq Use Param01_Bool.
Trocq Use Param2b0_Bool.
Trocq Use Param00_Bool.


Lemma R_false : rel Param44_Bool false false.
Proof.
  unfold rel. simpl. exact falseR.
Defined.

Lemma R_true : rel Param44_Bool true true.
Proof.
  unfold rel. simpl. exact trueR.
Defined.

Trocq Use R_false.
Trocq Use R_true.

(* =================================================================== *)
(* 7. Param44_option_nat : identity relation for option_nat             *)
(* =================================================================== *)

Definition option_nat_id (o : option_nat) : option_nat := o.

Lemma option_nat_idK : forall (o : option_nat), option_nat_id (option_nat_id o) = o.
Proof. reflexivity. Defined.

Definition Param44_option_nat : Param44.Rel option_nat option_nat.
Proof.
  apply Iso.toParam; unshelve econstructor.
  - exact option_nat_id.
  - exact option_nat_id.
  - exact option_nat_idK.
  - exact option_nat_idK.
Defined.

Trocq Use Param44_option_nat.
Trocq Use Param44_nat.

Definition Param2a0_option_nat : Param2a0.Rel option_nat option_nat := Param44_option_nat.
Definition Param02b_option_nat : Param02b.Rel option_nat option_nat := Param44_option_nat.
Definition Param10_option_nat  : Param10.Rel option_nat option_nat := Param44_option_nat.
Definition Param01_option_nat  : Param01.Rel option_nat option_nat := Param44_option_nat.
Definition Param00_option_nat  : Param00.Rel option_nat option_nat := Param44_option_nat.

Trocq Use Param2a0_option_nat.
Trocq Use Param02b_option_nat.
Trocq Use Param10_option_nat.
Trocq Use Param01_option_nat.
Trocq Use Param00_option_nat.

Definition Param2a0_nat : Param2a0.Rel nat nat := Param44_nat.
Definition Param02b_nat : Param02b.Rel nat nat := Param44_nat.
Definition Param10_nat  : Param10.Rel nat nat := Param44_nat.
Definition Param01_nat  : Param01.Rel nat nat := Param44_nat.
Definition Param00_nat  : Param00.Rel nat nat := Param44_nat.

Trocq Use Param2a0_nat.
Trocq Use Param02b_nat.
Trocq Use Param10_nat.
Trocq Use Param01_nat.
Trocq Use Param00_nat.

(* ================================================================= *)
(* 8. R_update: bridge witnessing _pm_update ~ _tm_update            *)
(* ================================================================= *)

Lemma update_bridge : forall (m : string -> option_nat) (x : string) (v : nat),
  _pm_update m x v = _tm_update m x (Some v).
Proof. reflexivity. Defined.

Lemma R_update
    (m  m'  : string -> option_nat)
    (mR : rel (Param00_arrow string string Param44_string option_nat option_nat Param44_option_nat) m m')
    (x  x'  : string)   (xR : rel Param44_string   x  x')
    (v  : nat) (w : option_nat) (vR : rel R_val v w) :
  forall k k', rel Param44_string k k' ->
    rel Param00_option_nat (_pm_update m x v k) (_tm_update m' x' w k').
Proof.
  intros k k' kR.
  change (x = x') in xR; subst x'.
  change (k = k') in kR; subst k'.
  change (Some v = w) in vR.
  change (_pm_update m x v k = _tm_update m' x w k).
  rewrite update_bridge. unfold _tm_update, tm_update.
  destruct (String.eqb x k).
  - exact vR.
  - exact (mR k k eq_refl).
Defined.

Trocq Use R_update.
Trocq Use Param01_paths.
Trocq Use Param10_paths.

(* ================================================================= *)
(* 9. The Trocq theorem                                              *)
(* ================================================================= *)

Theorem pm_update_neq :
  forall (m : string -> option_nat) (x1 x2 : string) (v : nat),
    String.eqb x2 x1 = false -> (_pm_update m x2 v) x1 = m x1.
Proof.
  trocq.
  apply tm_update_neq.
Qed.

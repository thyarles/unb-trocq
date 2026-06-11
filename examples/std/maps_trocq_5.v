(* maps_trocq_5.v — Transfer pm_update_neq from partial maps to total maps
   via Trocq.

   ROOT CAUSE OF PREVIOUS FAILURES:
     Trocq cannot decompose the application [m x1] when [m] has an opaque
     type-alias type (_PartialMap).  The fix is to drop the type aliases and
     let Trocq see the literal [string -> option nat] function type — then
     the built-in Param_arrow witness decomposes it automatically.

   WHAT WE NEED:
     • Param44_string        — so Trocq passes keys through unchanged
     • Param44_option_nat    — so Trocq passes lookup results through unchanged
     • R_val                 — nat injects into option nat via Some
     • R_update              — bridges _pm_update ↔ _tm_update
     • Param01_paths         — for the equality in the goal
     (Param_arrow is built into Trocq stdlib; no explicit registration needed)
*)

From Stdlib Require Import String.
From Trocq Require Import Stdlib Trocq.
From Trocq Require Import Param_nat.       (* Param44_nat *)

Set Universe Polymorphism.

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
(* 2. Source Theorem: tm_update_neq for total_map (option nat)       *)
(*    (monomorphic, concrete type — Trocq needs ground GREFs)        *)
(* ================================================================= *)

Theorem tm_update_neq :
  forall (m : string -> option nat) (x1 x2 : string) (v : option nat),
    x2 <> x1 -> (tm_update m x2 v) x1 = m x1.
Proof.
  intros m x1 x2 v Hneq.
  unfold tm_update.
  rewrite <- String.eqb_neq in Hneq.
  rewrite Hneq.
  reflexivity.
Qed.

(* ================================================================= *)
(* 3. Manual proof (sanity check — Trocq will absorb the unfold)     *)
(* ================================================================= *)

Theorem pm_update_neq_manual :
  forall (m : string -> option nat) (x1 x2 : string) (v : nat),
    x2 <> x1 -> (pm_update m x2 v) x1 = m x1.
Proof.
  intros m x1 x2 v Hneq.
  unfold pm_update.
  apply tm_update_neq.
  exact Hneq.
Qed.

(* ================================================================= *)
(* 4. Monomorphic aliases (ground GREFs for Trocq's database)        *)
(*    We use the LITERAL expanded type [string -> option nat] so      *)
(*    Trocq can decompose function-type applications via Param_arrow. *)
(*    No _PartialMap / _TotalMap opaque aliases here.                 *)
(* ================================================================= *)

Definition _pm_update : (string -> option nat) -> string -> nat -> (string -> option nat)
  := @pm_update nat.
Definition _tm_update : (string -> option nat) -> string -> option nat -> (string -> option nat)
  := @tm_update (option nat).

(* =================================================================== *)
(* 5. R_val : Param42b.Rel nat (option nat)                            *)
(*    nat injects into option nat via Some; Some has a left inverse.   *)
(*    Pattern from list_option.v (option injects into list via cons).  *)
(* =================================================================== *)

Lemma some_retrK : forall (n : nat),
  (fun o : option nat => match o with Some m => m | None => O end) (Some n) = n.
Proof. reflexivity. Defined.

Definition R_val : Param42b.Rel nat (option nat) :=
  SplitInj.toParam
    (@SplitInj.Build nat (option nat)
       (@Some nat)
       (fun o : option nat => match o with Some m => m | None => O end)
       some_retrK).

Trocq Use R_val.

(* =================================================================== *)
(* 6. Param44_string : identity witness so Trocq passes keys through   *)
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

(* =================================================================== *)
(* 7. Param44_option_nat : identity witness so Trocq passes lookup     *)
(*    results (option nat) through unchanged on the target side        *)
(* =================================================================== *)

Definition option_nat_id (o : option nat) : option nat := o.

Lemma option_nat_idK : forall (o : option nat), option_nat_id (option_nat_id o) = o.
Proof. reflexivity. Defined.

Definition Param44_option_nat : Param44.Rel (option nat) (option nat).
Proof.
  apply Iso.toParam; unshelve econstructor.
  - exact option_nat_id.
  - exact option_nat_id.
  - exact option_nat_idK.
  - exact option_nat_idK.
Defined.

Trocq Use Param44_option_nat.
Trocq Use Param44_nat.

(* ================================================================= *)
(* 8. R_update: bridge witnessing _pm_update ~ _tm_update            *)
(*    rel Param44_string  x  x'  unfolds to  x = x'                 *)
(*    rel Param44_option_nat o o' unfolds to  o = o'                 *)
(*    rel R_val  v  w           unfolds to  Some v = w               *)
(* ================================================================= *)

Lemma update_bridge : forall (m : string -> option nat) (x : string) (v : nat),
  _pm_update m x v = _tm_update m x (Some v).
Proof. reflexivity. Defined.

Lemma R_update
    (m  m'  : string -> option nat)
    (mR : forall k k', rel Param44_string k k' -> rel Param44_option_nat (m k) (m' k'))
    (x  x'  : string)   (xR : rel Param44_string   x  x')
    (v  : nat) (w : option nat) (vR : rel R_val v w) :
  forall k k', rel Param44_string k k' ->
    rel Param44_option_nat (_pm_update m x v k) (_tm_update m' x' w k').
Proof.
  intros k k' kR.
  (* All these rels reduce definitionally to = *)
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

(* ================================================================= *)
(* 9. The Trocq theorem                                              *)
(*    trocq rewrites the goal to the total-map form,                 *)
(*    then tm_update_neq closes it.                                  *)
(* ================================================================= *)

Theorem pm_update_neq :
  forall (m : string -> option nat) (x1 x2 : string) (v : nat),
    x2 <> x1 -> (_pm_update m x2 v) x1 = m x1.
Proof.
  trocq.
  apply tm_update_neq.
Qed.

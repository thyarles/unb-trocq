(* maps_trocq_4.v — Transfer pm_update_neq from total maps to partial maps
   via Trocq, following the Vector_tuple.v / list_option.v pattern. *)

From Stdlib Require Import String.
From Trocq Require Import Stdlib Trocq.

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
  forall (m : total_map (option nat)) (x1 x2 : string) (v : option nat),
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
  forall (m : partial_map nat) (x1 x2 : string) (v : nat),
    x2 <> x1 -> (pm_update m x2 v) x1 = m x1.
Proof.
  intros m x1 x2 v Hneq.
  unfold pm_update.
  apply tm_update_neq.
  exact Hneq.
Qed.

(* ================================================================= *)
(* 4. Monomorphic aliases (ground GREFs for Trocq's database)        *)
(* ================================================================= *)

Definition _PartialMap := partial_map nat.          (* string -> option nat *)
Definition _TotalMap   := total_map (option nat).   (* string -> option nat *)

Definition _pm_update : _PartialMap -> string -> nat        -> _PartialMap := @pm_update nat.
Definition _tm_update : _TotalMap   -> string -> option nat -> _TotalMap   := @tm_update (option nat).

(* The two types are definitionally equal.  The conversions are the identity. *)
Definition pmap_to_tmap (m : _PartialMap) : _TotalMap   := m.
Definition tmap_to_pmap (m : _TotalMap)   : _PartialMap := m.

Lemma pmap_tmap_K : forall m, tmap_to_pmap (pmap_to_tmap m) = m.
Proof. reflexivity. Defined.

Lemma tmap_pmap_K : forall m, pmap_to_tmap (tmap_to_pmap m) = m.
Proof. reflexivity. Defined.

(* ================================================================== *)
(* 5. R_Map : Param44.Rel _PartialMap _TotalMap                       *)
(*    Built via Iso.toParam — the isomorphism is (identity, identity) *)
(* ================================================================== *)

Definition R_Map : Param44.Rel _PartialMap _TotalMap.
Proof.
  apply Iso.toParam; unshelve econstructor.
  - exact pmap_to_tmap.
  - exact tmap_to_pmap.
  - exact pmap_tmap_K.
  - exact tmap_pmap_K.
Defined.

Trocq Use R_Map.

(* =================================================================== *)
(* 6. R_val : Param42b.Rel nat (option nat)                            *)
(*    nat injects into option nat via Some; Some has a left inverse    *)
(*    got ideia from list_option.v (option injects into list via cons) *)
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

(* ================================================================= *)
(* 7. Bridge: _pm_update folds into _tm_update + Some                *)
(* ================================================================= *)

Lemma update_bridge : forall (m : _PartialMap) (x : string) (v : nat),
  _pm_update m x v = _tm_update m x (Some v).
Proof. reflexivity. Defined.

(* ================================================================= *)
(* 8. R_update: relational wrapper for update functions              *)
(*    Connects _pm_update to _tm_update, consuming:                  *)
(*      mR : rel R_Map  pm  tm   (i.e., pmap_to_tmap pm = tm)        *)
(*      vR : rel R_val  v   w    (i.e., Some v = w)                  *)
(* ================================================================= *)

Lemma R_update
    (pm : _PartialMap) (tm : _TotalMap)   (mR : rel R_Map  pm tm)
    (x  : string)
    (v  : nat)         (w  : option nat)  (vR : rel R_val  v  w) :
  rel R_Map (_pm_update pm x v) (_tm_update tm x w).
Proof.
  (* rel R_Map a b  = graph pmap_to_tmap a b  = (pmap_to_tmap a = b) *)
  unfold rel, R_Map in *.
  (* Unfold graph and pmap_to_tmap everywhere *)
  unfold graph, pmap_to_tmap in *.
  (* mR : pm = tm    vR : Some v = w *)
  rewrite update_bridge.
  (* goal: _tm_update pm x (Some v) = _tm_update tm x w *)
  rewrite mR, vR. simpl. reflexivity.
Defined.

Trocq Use R_update.
Trocq Use Param01_paths.

(* ================================================================= *)
(* 9. The Trocq theorem                                              *)
(*    trocq rewrites the goal from the partial-map world to the       *)
(*    total-map world, then tm_update_neq closes it directly.        *)
(* ================================================================= *)

Theorem pm_update_neq :
  forall (m : _PartialMap) (x1 x2 : string) (v : nat),
    x2 <> x1 -> (_pm_update m x2 v) x1 = m x1.
Proof.
  trocq.
  apply tm_update_neq.
Qed.

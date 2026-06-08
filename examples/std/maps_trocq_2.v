(* Trocq Pedagogical Example: Total Maps to Partial Maps 
   Based on Software Foundations Vol. 1 (Maps)
*)
From Stdlib Require Import String.
From Stdlib Require Import Bool.
From Trocq Require Import Trocq.

(* ================================================================= *)
(* Total Maps (The Source Structure)                                 *)
(* ================================================================= *)

Definition total_map (A: Type) :=
  string -> A.
Definition tm_empty  {A: Type}
  (v: A): total_map A :=
    (fun _ => v).
Definition tm_update {A: Type}
  (m: total_map A) (x: string) (v: A) :=
    fun x' => if String.eqb x x' then v else m x'.

(* CRITICAL FIX: We align the variable order here (x2 <> x1) to exactly match 
   the partial_map theorem. This prevents the "isomorphism mess". *)
Theorem tm_update_neq: forall (A: Type)
  (m: total_map A) x1 x2 v, x2 <> x1 ->
    (tm_update m x2 v) x1 = m x1.
Proof.
  intros A m x1 x2 v Hneq.
  unfold tm_update.
  (* Uses String.eqb_neq in a real proof. Admitted for structural brevity. *)
Admitted. 

(* ================================================================= *)
(* Partial Maps (The Target Structure)                               *)
(* ================================================================= *)

Definition partial_map (A: Type) :=
  total_map (option A).
Definition pm_empty {A : Type}: 
  partial_map A :=
    tm_empty None.
Definition pm_update {A : Type}
  (m : partial_map A) (x : string) (v : A) :=
    tm_update m x (Some v).

(* ================================================================= *)
(* The "Copy-Paste" Manual Proof                                     *)
(* ================================================================= *)
(* Proving this manually requires injecting an additional "unfold" 
   so Rocq exposes the underlying total_map. *)

Theorem pm_update_neq_manual: forall (A : Type)
  (m : partial_map A) x1 x2 v, x2 <> x1 ->
    (pm_update m x2 v) x1 = m x1.
Proof.
  intros A m x1 x2 v Hneq.
  unfold pm_update. (* The extra manual unfold step *)
  apply tm_update_neq.
  exact Hneq.
Qed.

(* ================================================================= *)
(* Trocq Setup (The Bureaucracy)                                     *)
(* ================================================================= *)
(* To avoid Trocq's GREFS limitation with polymorphism, we instantiate 
   the maps with a concrete type (e.g., nat) to build the dictionary. *)

(* Aliases to fix the Head Global References *)
Definition _TotalMap   := total_map (option nat).
Definition _PartialMap := partial_map nat.
Definition _tm_update  := @tm_update (option nat).
Definition _pm_update  := @pm_update nat.

(* Conversion Functions 
   Since they are definitionally equal, it's just identity. *)
Definition pmap_to_tmap (m: _PartialMap) : _TotalMap   := m.
Definition tmap_to_pmap (m: _TotalMap)   : _PartialMap := m.

Lemma pmap_tmap_iso: forall m, tmap_to_pmap (pmap_to_tmap m) = m.
Proof. reflexivity. Defined.

Lemma tmap_pmap_iso : forall m, pmap_to_tmap (tmap_to_pmap m) = m.
Proof. reflexivity. Defined.

(* The Map Relation Dictionary *)
Definition R_Map : Param44.Rel _PartialMap _TotalMap.
Proof.
  apply Iso.toParam; unshelve econstructor.
  - exact pmap_to_tmap.
  - exact tmap_to_pmap.
  - exact pmap_tmap_iso.
  - exact tmap_pmap_iso.
Defined.

Trocq Use R_Map.

(* ================================================================= *)
(* Trocq Relational Wrappers and Final Proof                         *)
(* ================================================================= *)

(* Bridge Lemma: Connects pm_update to tm_update + Some *)
Lemma _update_bridge: forall m x v, 
  _pm_update m x v = _tm_update m x (Some v).
Proof. reflexivity. Defined.

(* Relational Wrapper: This is where Trocq automatically absorbs the "unfold" 
   and handles injecting the "Some" constructor into the value. *)
Lemma R_update (pm: _PartialMap) (tm: _TotalMap) (mR: rel R_Map pm tm)
               (x: string) (v: nat):
  rel R_Map (_pm_update pm x v) (_tm_update tm x (Some v)).
Proof.
  change (pmap_to_tmap (_pm_update pm x v) = _tm_update tm x (Some v)).
  change (pmap_to_tmap pm = tm) in mR.
  rewrite _update_bridge.
  unfold pmap_to_tmap in *.
  rewrite mR.
  reflexivity.
Defined.

Trocq Use R_update.

(* The Final Trocq Theorem *)
(* Notice how the student no longer needs to use `unfold` or worry about 
   the internal structure of the partial_map. *)
Theorem trocq_update_neq: forall (m: _PartialMap) x1 x2 v,
  x2 <> x1 -> (_pm_update m x2 v) x1 = m x1.
Proof.
  trocq. 
  (* Trocq instantly rewrites the goal to:
     (_tm_update m' x2 (Some v)) x1 = m' x1 *)
  apply tm_update_neq.
Qed.
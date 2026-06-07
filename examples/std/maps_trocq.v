(* maps_trocq.v — Transferring pm_update_neq from total maps to partial maps
   using Trocq.  Based on the SF Maps chapter (maps.v).

   KEY IDEA: partial_map nat = total_map (option nat) definitionally.
   So R_Map is the identity relation (id_uparam).
   The only real work is the pm_update ↔ tm_update bridge (update wraps in Some).
*)
From Stdlib Require Import String.
From Trocq Require Import Trocq.

Set Universe Polymorphism.

(* 1. Definitions *)

Definition total_map (A: Type) :=
  string -> A.

Definition tm_empty {A: Type} (v: A): total_map A :=
  fun _ => v.

Definition tm_update {A: Type} (m: total_map A) (x: string) (v: A) :=
  fun x' => if String.eqb x x' then v else m x'.

(* partial_map: total_map with option values and None as default *)
Definition partial_map (A: Type) :=
  total_map (option A).

Definition pm_update {A: Type} (m: partial_map A) (x: string) (v: A) :=
  tm_update m x (Some v).

(* 2. Source theorem (concrete value type for Trocq GREFs) 
      Proved for total_map (option nat) — not polymorphic — because
      Trocq needs ground (non-polymorphic) head global references. *)

Theorem tm_update_neq:
  forall (m: total_map (option nat)) (x1 x2: string) (v: option nat),
  x1 <> x2 -> (tm_update m x1 v) x2 = m x2.
Proof.
  intros m x1 x2 v H.
  unfold tm_update.
  rewrite <- String.eqb_neq in H.  (* H : String.eqb x1 x2 = false *)
  rewrite H.
  reflexivity.
Defined.

(* 3. Copy and paste
      The one step Trocq will absorb is the `unfold pm_update`. *)

Theorem pm_update_neq_manual: forall (m: partial_map nat) (x1 x2: string) (v: nat),
  x1 <> x2 -> (pm_update m x1 v) x2 = m x2.
Proof.
  intros m x1 x2 v H.
  unfold pm_update.           (* <── Trocq absorbs this *)
  apply tm_update_neq.
  exact H.
Qed.

(* 4. Trocq setup 
      Monomorphic aliases with EXPLICIT TYPE ANNOTATIONS so Trocq uses
      the concrete ground types (not the polymorphic originals).
      The type uses the transparent form (string -> option nat) so Trocq
      can decompose the function type for function-application terms. *)
Definition _pm_update: (string -> option nat) -> string -> nat -> (string -> option nat) 
  := @pm_update nat.
Definition _tm_update: (string -> option nat) -> string -> option nat -> (string -> option nat)
  := @tm_update (option nat).

(* Bridge: _pm_update wraps v in Some; this is the relation Trocq uses
   to rewrite _pm_update → _tm_update in the goal. Since partial_map nat
   = string -> option nat definitionally, this is just reflexivity. *)
Lemma R_update (m: string -> option nat) (x: string) (v: nat):
  _pm_update m x v = _tm_update m x (Some v).
Proof.
    reflexivity.
Defined.

(* 5. Trocq Uses *)
Trocq Use R_update.
Trocq Use Param44_nat.

(* 6. Trocq proof 
      trocq rewrites _pm_update → _tm_update (absorbing the Some wrapping).
      tm_update_neq then closes the goal directly. *)

Theorem pm_update_neq: forall (m: string -> option nat) (x1 x2: string) (v: nat),
    x1 <> x2 -> (_pm_update m x1 v) x2 = m x2.
Proof.
  trocq.
  apply tm_update_neq.
Qed.
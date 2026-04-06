(*****************************************************************************)
(*                  Tutorial: Lists, Parametricity, and Trocq                *)
(*                            — Step by Step —                               *)
(*                                                                           *)
(*  Goal: understand how type parametricity enables proof reuse, and how     *)
(*  Trocq can automate that reuse.                                           *)
(*                                                                           *)
(*  Overview:                                                                *)
(*    Expl A — Core concept: what is parametricity?                          *)
(*    Part 1 — Natural-number lists (monomorphic): length, append, theorem   *)
(*    Part 2 — Polymorphic lists: length, append, theorem                    *)
(*             Expl B — Comparing the proofs (tactic style)                  *)
(*    Part 3 — Proof objects: proofs as lambda terms                         *)
(*             Expl C — Comparing the proofs (lambda terms)                  *)
(*    Part 4 — Manual transfer                                               *)
(*             Expl D - Notes about manual transfer                          *)
(*    Part 5 — Using Trocq                                                   *)
(*             Expl E — Notes about Trocq                                    *)
(*****************************************************************************)

From Stdlib Require Import ssreflect.
Local Open Scope nat_scope. (* 0, 1, 2, 3 are interpreted as natural numbers *)

(** Rocq does not allow a type to have itself as its type.  Instead, it uses a
    hidden universe hierarchy: Type@{0} has type Type@{1}, which has type
    Type@{2}, and so on. The next command tells to treat universe levels as 
    local variables, enabling more generic code. *)
Set Universe Polymorphism.

(** EXPL A — Core concept: what is parametricity?
    ---------------------------------------------------------------------------
    Imagine you need lists of naturals, lists of booleans, lists of strings...
    Without parametricity you would have to define a separate type for each one
    and rewrite all functions (length, append...) and all proofs from scratch.

    With parametric polymorphism you define the operations once for a generic
    type A, and every instance (nat, bool, string...) automatically inherits the
    proved properties.

    The fundamental idea:

      "Properties that depend only on the STRUCTURE of a list (and not on the
      TYPE of its elements) are automatically valid for any instance." 
*)

(** PART 1 — Natural-number lists (monomorphic): length, append, theorem *)
    Require Import Trocq_examples.bs_p1.

(** PART 2 — Polymorphic (parametric) lists *)
    Require Import Trocq_examples.bs_p2.

(** PART 3 — Proof objects: proofs as lambda terms *)
    Require Import Trocq_examples.bs_p3.
    
(** PART 4 — Manual transfer *)
    Require Import Trocq_examples.bs_p4.

(** PART 5 — Using Trocq *)
    Require Import Trocq_examples.bs_p5.
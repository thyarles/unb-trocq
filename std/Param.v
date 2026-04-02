(*****************************************************************************)
(*                            *                    Trocq                     *)
(*  _______                   *       Copyright (C) 2023 Inria & MERCE       *)
(* |__   __|                  *    (Mitsubishi Electric R&D Centre Europe)   *)
(*    | |_ __ ___   ___ __ _  *       Cyril Cohen <cyril.cohen@inria.fr>     *)
(*    | | '__/ _ \ / __/ _` | *       Enzo Crance <enzo.crance@inria.fr>     *)
(*    | | | | (_) | (_| (_| | *   Assia Mahboubi <assia.mahboubi@inria.fr>   *)
(*    |_|_|  \___/ \___\__, | ************************************************)
(*                        | | * This file is distributed under the terms of  *)
(*                        |_| * GNU Lesser General Public License Version 3  *)
(*                            * see LICENSE file for the text of the license *)
(*****************************************************************************)

From elpi Require Import elpi.
Require Import ssreflect.
Require Export Database.
Require Import Hierarchy.
Require Export Param_Type Param_arrow Param_forall.

From Trocq.Elpi.generation Extra Dependency "pparam-type.elpi" as pparam_type_generation.
From Trocq.Elpi Extra Dependency "tactic.elpi" as tactic.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Elpi Command genpparamtype.
Elpi Accumulate Db trocq.db.
Elpi Accumulate File pparam_type_generation.

Elpi Query lp:{{
  coq.univ.new U,
  coq.univ.variable U L,
  coq.univ.alg-super U U1,
  coq.univ.variable U1 L1,
  map-class.all-of-kind low Classes1,
  % first the ones where the arguments matter
  std.forall Classes1 (m\
    std.forall Classes1 (n\
      generate-pparam-type L L1 (pc m n)
    )
  ).
}}.

Elpi Tactic trocq.
Elpi Accumulate Db trocq.db.
Elpi Accumulate File tactic.

Tactic Notation "trocq" ident_list(l) := elpi trocq ltac_string_list:(l).

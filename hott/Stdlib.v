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

From HoTT Require Export HoTT.
From Trocq Require Export HoTT_additions.
From elpi Require Export elpi.

Module HoTTNotations.
  (* Stub for compatibility with stdlib version  *)
End HoTTNotations.

Register paths as trocq.paths.
Register concat as trocq.concat.
Register idpath as trocq.idpath.
Register inverse as trocq.inverse.
Register paths_ind as trocq.paths_ind.
Register exist as trocq.exist.
Register ap as trocq.ap.

Definition paths_nondep (A : Type) (x : A) (P : A -> Type) : P x -> forall y : A, x = y -> P y :=
  fun w y e=> paths_rect A x (fun a0 e => P a0) w y e.
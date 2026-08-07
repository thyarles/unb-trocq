(* Compatibility layer with elpi's derive *)
From elpi Require Export elpi.
From Trocq Require Export Stdlib.
From Trocq Require Import HoTTNotations.

Definition eq_f := @ap.
Register eq_f as elpi.derive.eq_f.
Register paths as elpi.eq.

Definition bool_discr : Datatypes.true = Datatypes.false -> forall T : Type, T :=
fun e T => 
  match e in _ = t 
      return match t with Datatypes.false => T | Datatypes.true => Unit end
  with idpath => tt end.
Register bool_discr as elpi.bool_discr.
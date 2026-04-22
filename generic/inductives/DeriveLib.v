(* Compatibility layer with elpi's derive *)
From elpi Require Export elpi.
From Trocq Require Export Stdlib HoTTNotations.

Definition eq_f := @ap.
Register eq_f as elpi.derive.eq_f.

Definition bool_discr : true = false -> forall T : Type, T :=
fun e T => 
  match e in _ = t 
      return match t with false => T | true => Unit end 
  with idpath => tt end.
Register bool_discr as elpi.bool_discr.
From Trocq Require Import mR Rm.

Elpi Command test.
Print Wrap_mR.
Print Wrap_Rm.

Goal forall (w1 w2 : Wrap) (wR : Wrap_R w1 w2), Wrap_mR w1 w2 (Wrap_Rm w1 w2 wR) = wR.
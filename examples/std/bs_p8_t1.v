From Stdlib Require Import ssreflect.
From Stdlib Require Import Lia.
Local Open Scope nat_scope.
From Trocq Require Import Trocq.
From Trocq Require Import Param_nat.
Set Universe Polymorphism.
Require Import Trocq_examples.bs_p1.
Require Import Trocq_examples.bs_p2.
Require Import Trocq_examples.bs_p5.
Require Import Trocq_examples.bs_p7.
Require Import Trocq_examples.bs_p8.

(* ── Probe: test what happens when we register R_NatList_v2 (PList nat source) *)
(* Step 1: also register a R__papp2 keyed on papp (not _papp)                 *)
Lemma R__papp2 (l1 : PList nat) (l1' : NatList) (l1R : rel R_NatList l1 l1')
              (l2 : PList nat) (l2' : NatList) (l2R : rel R_NatList l2 l2') :
    rel R_NatList (@papp nat l1 l2) (napp l1' l2').
Proof. exact (R__papp l1 l1' l1R l2 l2' l2R). Defined.

Trocq Use R_NatList_v2.
Trocq Use R__papp2.

(* Step 2: now try the naive theorem *)
Theorem psum2_papp_probe : forall (l1 l2 : PList nat),
    psum2 (@papp nat l1 l2) = psum2 l1 + psum2 l2.
Proof.
    trocq.
    apply nsum_napp.
Qed.



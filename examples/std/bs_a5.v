(*  bs_a5.v — Baby Step: Trocq Infinite-to-Finite Space Reduction
    Fermat's Last Theorem (degree 3, mod-9 step)

    ── The Core Idea ──────────────────────────────────────────────────────

    To prove a step of Fermat's Last Theorem for degree 3 one must show
    that for any integers m, n, p ∈ ℤ, if their product is not divisible
    by 3, then m³ + n³ ≠ p³.

    The space ℤ is infinite: a direct computation is impossible.  But
    ℤ/9ℤ contains only 9 elements (0 through 8).  If we can transfer the
    theorem to ℤ/9ℤ, Rocq needs to check only 9 × 9 × 9 = 729 cases,
    which it does in milliseconds.

    ── How Trocq Accomplishes the Space Reduction ─────────────────────────

    Phase 1  Define arithmetic on ℤ (infinite) and ℤ/9ℤ (finite, 9 elems)
    Phase 2  Build the Trocq retraction witness Rp : Param42a.Rel ℤ (ℤ/9ℤ)
             This tells Trocq that ℤ/9ℤ is a valid bounded retraction of ℤ.
    Phase 3  Prove bridge lemmas relating infinite operations to finite ones
             (Radd, Rmul, Rmod3, Reqmodp01)
    Phase 4  Register all witnesses with [Trocq Use]
    Phase 5  State the theorem on the INFINITE space ℤ; run [trocq] to
             collapse the goal to ℤ/9ℤ; discharge by exhaustive case split

*)

From mathcomp.boot Require Import all_boot.
From mathcomp.algebra Require Import all_algebra.
From Trocq Require Import Stdlib Trocq.

Import GRing.Theory.
Open Scope ring_scope.

Set Universe Polymorphism.

(* ============================================================
   PHASE 1 — Type Definitions and Arithmetic Setup
   ============================================================
   We set up two arithmetic universes:
     • ℤ     (int, mathcomp integers) — infinite, the real integers
     • ℤ/9ℤ  (Zmod9 = 'Z_9)           — finite, only 9 residues

   Trocq needs MONOMORPHIC (non-polymorphic) global references for
   every operation it must relate.  We therefore introduce explicit
   aliases zero/one/add/mul/mod3 on the ℤ side and zerop/onep/addp/
   mulp/modp3 on the ℤ/9ℤ side.
*)

(* ── Scopes *)

Declare Scope int_scope.
Delimit Scope int_scope with int.
Delimit Scope int_scope with ℤ.
Local Open Scope int_scope.
Declare Scope Zmod9_scope.
Delimit Scope Zmod9_scope with Zmod9.
Local Open Scope Zmod9_scope.

(* ── Helpers for bridge-lemma types *)

(*  unop_param RX RY f g
    says f and g are related pointwise w.r.t. RX and RY          *)
Definition unop_param {X X'} RX {Y Y'} RY
(f : X -> Y) (g : X' -> Y') :=
forall x x', RX x x' -> RY (f x) (g x').

(*  binop_param RX RY RZ f g
    says f and g are related in each argument                     *)
Definition binop_param {X X'} RX {Y Y'} RY {Z Z'} RZ
(f : X -> Y -> Z) (g : X' -> Y' -> Z') :=
forall x x', RX x x' -> forall y y', RY y y' -> RZ (f x y) (g x' y').

(* ── ℤ/9ℤ: the finite type and its operations *)

(*  Zmod9 = 'Z_9 is the cyclic group ℤ/9ℤ (ordinals 0..8).
    Trocq needs monomorphic definitions so the DB lookup succeeds. *)
Definition Zmod9 := 'Z_9.
Definition zerop : Zmod9 := Zp0.
Definition addp  : Zmod9 -> Zmod9 -> Zmod9 := @Zp_add 9.
Definition mulp  : Zmod9 -> Zmod9 -> Zmod9 := @Zp_mul 9.
Definition onep  : Zmod9 := Zp1.

(* ── Quotient map and its section *)

(*  modp  reduces an integer to its residue mod 9.
    reprp is the trivial section (identity on ordinals, seen as ints).
    reprpK proves that modp ∘ reprp = id, i.e. 'Z_9 retractss into ℤ. *)
Definition modp : int -> Zmod9 := fun x => (x)%:~R.
Definition reprp : Zmod9 -> int := id.

Lemma reprpK : forall x, modp (reprp x) = x.
Proof. exact: natr_Zp. Qed.

(* ── mod 3 inside ℤ/9ℤ *)

(*  modp3 : Zmod9 -> Zmod9  reduces an element of ℤ/9ℤ further mod 3.
    The auxiliary lemma bounds the result so the ordinal is well-formed. *)
Lemma mk_mod9_mod3 (n : 'I_9) : (n %% 3 < 9)%N.
Proof. apply: (@ltn_trans 3) => //; exact: ltn_pmod. Qed.

Definition modp3 : Zmod9 -> Zmod9 := fun n => Ordinal (mk_mod9_mod3 n).

(* ── Equality predicates *)

(*  eqmodp  : propositional equality modulo 9 on ℤ (the "≡" notation)
    eq_Zmod9: plain equality on ℤ/9ℤ (definitionally the same thing)  *)
Definition eqmodp   (x y : int)    := modp x = modp y.
Definition eq_Zmod9 (x y : Zmod9)  := (x = y).
Arguments eq_Zmod9 /.

(* ── ℤ operations (monomorphic aliases) *)

Definition mod3 : int -> int        := fun x => x %% 3.
Definition zero : int               := 0.
Definition one  : int               := 1.
Definition add  : int -> int -> int := fun x y => x + y.
Definition mul  : int -> int -> int := fun x y => x * y.

(* ── Notation setup *)

Notation "0"     := zero            : int_scope.
Notation "0"     := zerop           : Zmod9_scope.
Notation "1"     := one             : int_scope.
Notation "1"     := onep            : Zmod9_scope.
Notation "x + y" := (add x%int  y%int)    : int_scope.
Notation "x + y" := (addp x%Zmod9 y%Zmod9): Zmod9_scope.
Notation "x * y" := (mul x%int  y%int)    : int_scope.
Notation "x * y" := (mulp x%Zmod9 y%Zmod9): Zmod9_scope.
Notation not A   := (A -> False).
Notation "m ³"   := (m * m * m)%int    (at level 2) : int_scope.
Notation "m ³"   := (m * m * m)%Zmod9  (at level 2) : Zmod9_scope.
Notation "m % 3" := (mod3 m)%int       (at level 2) : int_scope.
Notation "m % 3" := (modp3 m)%Zmod9    (at level 2) : Zmod9_scope.
Notation "x ≡ y" := (eqmodp x%int y%int)
(format "x  ≡  y", at level 70) : int_scope.
Notation "x ≢ y" := (not (eqmodp x%int y%int))
(format "x  ≢  y", at level 70) : int_scope.
Notation "x ≠ y" := (not (x = y)) (at level 70).
Notation "ℤ/9ℤ"  := Zmod9.
Notation  ℤ      := int.

(* ============================================================
   PHASE 2 — Trocq Retraction Witness (Param42a)
   ============================================================
   Rp is the core bridge that tells Trocq:
     "ℤ/9ℤ is a split-surjective retract of ℤ via modp/reprp"

   SplitSurj.Build reprpK packages the retraction proof.
   SplitSurj.toParam lifts it to a Param42a.Rel ℤ (ℤ/9ℤ) witness.

   Param42a means:
     • 4  — the ℤ side has a full map  (modp sends every int to ℤ/9ℤ)
     • 2a — the ℤ/9ℤ side has a section (reprp), with reprpK as proof
*)
Definition Rp := SplitSurj.toParam (SplitSurj.Build reprpK).

(*  Point witnesses — Trocq needs to know where 0 and 1 land. *)
Lemma Rzero : Rp zero zerop. Proof. done. Qed.
Lemma Rone  : Rp one  onep.  Proof. done. Qed.

(* ============================================================
   PHASE 3 — Bridge Lemmas: Relating ℤ Operations to ℤ/9ℤ Ones
   ============================================================
   Each lemma below is a CONGRUENCE STATEMENT: it says that the
   corresponding operation commutes with reduction mod 9.

     Radd   :   add a b  ≡  addp  (modp a) (modp b)   mod 9
     Rmul   :   mul a b  ≡  mulp  (modp a) (modp b)   mod 9
     Rmod3  :   mod3 a   ≡  modp3 (modp a)             mod 9
     Reqmodp01: eqmodp a b  ↔  eq_Zmod9 (modp a) (modp b)

   All follow from the ring morphism property of modp (it is a ring
   homomorphism ℤ → ℤ/9ℤ).
*)

(*  Radd *)
Lemma Radd : binop_param Rp Rp Rp add addp.
Proof.
rewrite /Rp /SplitSurj.toParam /= /graph /= => x1 y1 <- x2 y2 <-.
by rewrite /rel /= /modp rmorphE.
Qed.

(*  Rmul *)
Lemma Rmul : binop_param Rp Rp Rp mul mulp.
Proof.
rewrite /Rp /SplitSurj.toParam /= /graph /= => x1 y1 <- x2 y2 <-.
by rewrite /rel /= /modp rmorphM.
Qed.

(*  Rmod3
    This lemma says: "reducing mod 3 is the same whether we do it
    directly on ℤ, or first reduce mod 9 and then mod 3 inside ℤ/9ℤ."
    Proof by [wlog] case-split on sign (positive/negative). *)
Lemma Rmod3 : unop_param Rp Rp mod3 modp3.
Proof.
rewrite /Rp /= /graph /= => x y <- {y}.
rewrite /modp /mod3 /modp3.
apply: val_inj => /=.
wlog : x / exists n, x = Posz n.
  move=> hwlog.
  case: x => n.
  - by apply: hwlog; exists n.
  - rewrite modNz_nat //.
    rewrite -[Posz (1 + _)%N - 1]/(2%int) -[(1 + _)%N]/(3%N) NegzE rmorphN /=.
    rewrite -[_.+2]/(9%N) modn_dvdm //.
    rewrite modnB //=; last by rewrite [_%:~R]Zp_nat ltnW.
    set x : 'I_9 := _.+1%:~R.
    rewrite -[(9 %% 3)%N]/(0%N) addn0.
    have {x} -> : x = (n.+1 %% 9)%N :> nat by rewrite {}/x [_%:~R]Zp_nat //.
    rewrite modn_dvdm // modnS; case: ifP => //= hn.
    - by rewrite mul0n subn0 -[n]/(n.+1.-1) modn_pred // hn.
    - rewrite -[n]/(n.+1.-1) modn_pred // hn mul1n subSS subzn; last first.
        by apply: (@leq_trans (n.+1 %% 3)); rewrite ?leq_pred // -ltnS ltn_pmod.
      rewrite [_%:~R]Zp_nat [LHS]modn_small //=.
      by apply: (@leq_trans 3) => //; rewrite ltnS leq_subr.
case=> n -> {x}.
set u : 'I_9 := _%:~R; set v := (X in (X %% 3)%N).
have {v} -> : v = (n %% 9)%N by exact: val_Zp_nat.
rewrite modn_dvdm //.
have -> : nat_of_ord u = ((n %% 3)%N %% 9)%N.
  by rewrite {}/u modz_nat /= (@val_Zp_nat 9).
rewrite modn_small //; apply: (@ltn_trans 3) => //; exact: ltn_pmod.
Qed.

(*  Reqmodp01
    Equality on ℤ (mod 9) ↔ equality on ℤ/9ℤ.
    Uses Param01.BuildRel to build the weakest (01) relation level,
    sufficient for transferring ≢ and ≠ goals. *)
Lemma Reqmodp01 : forall (m : int) (x : Zmod9), Rp m x ->
  forall n y, Rp n y -> Param01.Rel (eqmodp m n) (eq_Zmod9 x y).
Proof.
rewrite /Rp /= /graph /=.
move=> x k exk y l eyl.
apply: (@Param01.BuildRel (x ≡ y) (k = l) (fun _ _ => unit)) => //.
by constructor; rewrite -exk -eyl.
Qed.

(* ============================================================
   PHASE 4 — Trocq Use: Register All Witnesses
   ============================================================
   This populates the Trocq database so the [trocq] tactic can
   find the right bridge for each subterm it encounters.

   Param10_paths — transfers propositional equality (≠) between types
   Param01_sum   — transfers the sum/disjunction type
   Param01_Empty — transfers the empty type (needed for negation → False)
   Param10_Empty — symmetric direction
*)

Trocq Use Rp Rmul Rzero Rone Radd Rmod3 Param10_paths Reqmodp01.
Trocq Use Param01_sum.
Trocq Use Param01_Empty.
Trocq Use Param10_Empty.

(* ============================================================
   PHASE 5 — Main Theorem and Proof
   ============================================================
   The theorem is stated on the INFINITE type ℤ.
   A manual proof here would require a complex algebraic argument.

   Instead, we run [trocq], which:
     1. Analyses the goal, finds the Rp witness for ℤ/ℤ/9ℤ,
     2. Rewrites every ℤ occurrence by its ℤ/9ℤ counterpart using
        the bridge lemmas (Radd, Rmul, Rmod3, Reqmodp01),
     3. Produces a new goal entirely over ℤ/9ℤ (only 9 elements).

   The transformed goal is:
     ∀ m n p : ℤ/9ℤ,  (m * n * p) % 3  ≢  0  →  m³ + n³  ≠  p³

   Since ℤ/9ℤ has 9 elements, Rocq only needs to verify
   9 × 9 × 9 = 729 cases — done instantly by exhaustive case split.
*)

Lemma flt3_step : forall (m n p : ℤ),
  ((m * n * p)%Z % 3)%Z ≢ 0 -> (m³ + n³)%ℤ ≠ p³%ℤ.
Proof.
  (* Step 1: Trocq collapses ℤ → ℤ/9ℤ.
     The goal becomes: ∀ m n p : ℤ/9ℤ, (m*n*p)%3 ≢ 0 → m³+n³ ≠ p³  *)
  trocq => /=.
  (* Step 2–3: Exhaustively verify all 9×9×9 = 729 finite cases.    *)
  move=> + + + /eqP + /eqP.
  by do 3![case; do 9?[case=> //=] => ?].
Qed.

Print Assumptions flt3_step.

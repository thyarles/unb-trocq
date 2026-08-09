(*  bs_z1_lift.v — Baby Step: Divergence Test & Trocq Proof Transfer *)

From Stdlib Require Import ssreflect Lia.
From Trocq Require Import Trocq Param_nat.
Require Import bs_z1.
Local Open Scope nat_scope.
Set Universe Polymorphism.

(*  ── Polymorphic expression type & Addable typeclass ───────────────────── *)

Inductive pexpr (A : Type) : Type :=
  | PConst : A -> pexpr A
  | PPlus  : pexpr A -> pexpr A -> pexpr A.
Arguments PConst {A} _.
Arguments PPlus {A} _ _.

Class Addable (A : Type) : Type := {
  add        : A -> A -> A;
  zero       : A;
  add_assoc  : forall x y z : A, add (add x y) z = add x (add y z);
  add_zero_r : forall x : A, add x zero = x
}.

(* PPlus evaluates right-to-left: add (peval e2) (peval e1). *)
Fixpoint peval {A : Type} {H : Addable A} (e : pexpr A) : A :=
  match e with
  | PConst n => n
  | PPlus e1 e2 => add (peval e2) (peval e1)
  end.

(*  ── Manual divergence test ─────────────────────────────────────────────── *)

Instance addableNat : Addable nat := {
  add        := Nat.add;
  zero       := 0;
  add_assoc  := ltac:(intros; lia);
  add_zero_r := ltac:(intros; lia)
}.

(* After simpl the goal is [add zero (peval e) = peval e], needing left identity.
   Addable only provides right identity [add_zero_r]; the proof is genuinely stuck. *)
Goal forall {A : Type} {H : Addable A} (e : pexpr A),
  peval (PPlus e (PConst zero)) = peval e.
Proof. intros. simpl. Fail apply add_zero_r. Abort.

(*  ── Conversion functions ───────────────────────────────────────────────── *)

Fixpoint pexpr_2_expr {A : Type} (f : A -> nat) (e : pexpr A) : expr :=
  match e with
  | PConst n => Const (f n)
  | PPlus e1 e2 => Plus (pexpr_2_expr f e1) (pexpr_2_expr f e2)
  end.

Fixpoint expr_2_pexpr {A : Type} (g : nat -> A) (e : expr) : pexpr A :=
  match e with
  | Const n => PConst (g n)
  | Plus e1 e2 => PPlus (expr_2_pexpr g e1) (expr_2_pexpr g e2)
  end.

(*  ── Mutual inverses ────────────────────────────────────────────────────── *)

Lemma pexpr_expr_iso : forall {A : Type} (f : A -> nat) (g : nat -> A),
  (forall x : A, g (f x) = x) ->
  forall e : pexpr A, expr_2_pexpr g (pexpr_2_expr f e) = e.
Proof.
  intros A f g Hgf e.
  induction e; simpl.
  - rewrite Hgf. reflexivity.
  - rewrite IHe1 IHe2. reflexivity.
Defined.

Lemma expr_pexpr_iso : forall {A : Type} (f : A -> nat) (g : nat -> A),
  (forall x : nat, f (g x) = x) ->
  forall e : expr, pexpr_2_expr f (expr_2_pexpr g e) = e.
Proof.
  intros A f g Hfg e.
  induction e; simpl.
  - rewrite Hfg. reflexivity.
  - rewrite IHe1 IHe2. reflexivity.
Defined.

Definition pexpr_nat := pexpr nat.

(*  ── Relation between the types ────────────────────────────────────────── *)

(* pexpr nat and expr are structurally identical; the isomorphism uses id on
   nat leaves.  The non-trivial gap is only in peval_nat vs eval below. *)

Definition R_expr {A : Type} (f : A -> nat) (g : nat -> A)
  (Hgf : forall x : A, g (f x) = x)
  (Hfg : forall x : nat, f (g x) = x) : Param44.Rel (pexpr A) expr.
Proof.
  apply Iso.toParam; unshelve econstructor.
  - exact (pexpr_2_expr f).          (* map   : pexpr A → expr *)
  - exact (expr_2_pexpr g).          (* comap : expr → pexpr A *)
  - exact (pexpr_expr_iso f g Hgf).  (* mapK  : comap ∘ map = id *)
  - exact (expr_pexpr_iso f g Hfg).  (* comapK: map ∘ comap = id *)
Defined.

Definition R_expr_nat : Param44.Rel pexpr_nat expr.
Proof.
  exact (R_expr id id (fun _ => eq_refl) (fun _ => eq_refl)).
Defined.

(* Monomorphic aliases prevent Trocq from confusing the implicit A argument
   with a translated expression variable. *)
Definition pconst (n : nat) : pexpr_nat := PConst n.
Definition pplus (e1 e2 : pexpr_nat) : pexpr_nat := PPlus e1 e2.

(* Monomorphic peval_nat is needed so trocq_expr can rewrite it. *)
Fixpoint peval_nat (e : pexpr_nat) : nat :=
  match e with
  | PConst n => n
  | PPlus e1 e2 => peval_nat e2 + peval_nat e1
  end.

Lemma peval_nat_eq_peval : forall e : pexpr_nat, peval_nat e = peval e.
Proof.
  induction e; simpl.
  - reflexivity.
  - rewrite IHe1 IHe2. reflexivity.
Defined.

(*  ── Relation between the constructors ─────────────────────────────────── *)

(* Param44_nat covers the type nat but not individual numeral constants. *)
Lemma R_zero : natR 0 0.
Proof. exact OR. Defined.

Lemma R_pconst (n n' : nat) (nR : natR n n') :
  rel R_expr_nat (pconst n) (econst n').
Proof.
  change (pexpr_2_expr id (pconst n) = econst n').
  unfold pconst, econst. simpl.
  f_equal.
  apply R_in_map_nat in nR.   (* extract n = n' from natR *)
  exact nR.
Defined.

Lemma R_pplus (e1 : pexpr_nat) (e1' : expr) (e1R : rel R_expr_nat e1 e1')
              (e2 : pexpr_nat) (e2' : expr) (e2R : rel R_expr_nat e2 e2') :
  rel R_expr_nat (pplus e1 e2) (eplus e1' e2').
Proof.
  change (pexpr_2_expr id e1 = e1') in e1R.
  change (pexpr_2_expr id e2 = e2') in e2R.
  change (pexpr_2_expr id (pplus e1 e2) = eplus e1' e2').
  unfold pplus, eplus. simpl.
  rewrite e1R e2R.
  reflexivity.
Defined.

(*  ── Relation between the functions ────────────────────────────────────── *)

(* PPlus case: [f (peval e2) + f (peval e1) = eval e1' + eval e2'] — lia bridges
   commutativity.  This is the only non-trivial step in the whole file. *)
Lemma peval_eq_eval : forall {A : Type} {H : Addable A}
  (f : A -> nat)
  (Hz : f zero = 0)
  (Hf : forall x y : A, f (add x y) = f x + f y)
  (e : pexpr A),
  f (peval e) = eval (pexpr_2_expr f e).
Proof.
  intros A H f Hz Hf e.
  induction e; simpl.
  - reflexivity.
  - rewrite Hf IHe1 IHe2.
    lia.
Defined.

Lemma R_peval_nat (e : pexpr_nat) (e' : expr) (eR : rel R_expr_nat e e') :
  natR (peval_nat e) (eval e').
Proof.
  change (pexpr_2_expr id e = e') in eR.
  apply map_in_R_nat.
  rewrite peval_nat_eq_peval.
  rewrite <- eR.
  apply (peval_eq_eval id).
  - reflexivity.
  - intros. simpl. reflexivity.
Defined.


(*  ── Register in Trocq's database ──────────────────────────────────────── *)

Trocq Use R_expr_nat.   (* relation between the types          *)
Trocq Use Param44_nat.  (* from Trocq — relation for nat       *)
Trocq Use Param_add.    (* from Trocq — relation for +         *)
Trocq Use R_zero.       (* constant 0 appearing in the terms   *)
Trocq Use R_pconst.     (* relation between the leaf constructor *)
Trocq Use R_pplus.      (* relation between the binary constructor *)
Trocq Use R_peval_nat.  (* relation between the functions      *)

(*  ── The theorem via Trocq ──────────────────────────────────────────────── *)

Ltac trocq_expr :=
  change (@peval nat addableNat) with peval_nat;
  trocq.

Theorem peval_const_plus_auto : forall x y,
  peval_nat (pplus (pconst x) (pconst y)) = x + y.
Proof.
  trocq_expr.
  exact eval_const_plus.
Defined.

Theorem peval_assoc_auto : forall e1 e2 e3 : pexpr_nat,
  peval_nat (pplus e1 (pplus e2 e3)) = peval_nat (pplus (pplus e1 e2) e3).
Proof.
  trocq_expr.
  exact eval_assoc.
Defined.

Theorem peval_plus_zero_r_auto : forall e : pexpr_nat,
  peval_nat (pplus e (pconst 0)) = peval_nat e.
Proof.
  trocq_expr.
  exact eval_plus_zero_r.
Defined.

Print Assumptions peval_plus_zero_r_auto.

(** EXPL — Notes about Trocq *)

(* Trocq works with a database of "parametric relations".

    To use the trocq tactic we need:

    (a) The relation between the CONSTRUCTORS
        pconst ~ econst  and  pplus ~ eplus
    (b) The relation between the TYPES
        pexpr_nat ~ expr
    (c) The relation between the FUNCTIONS
        peval_nat ~ eval
    (d) Register everything with Trocq Use
    (e) The main theorem via trocq
*)

(*  ── Relation between the types ────────────────────────────────────────── *)

    (* pexpr nat and expr share the same tree structure over nat; the
       isomorphism is a constructor renaming (PConst/PPlus ↔ Const/Plus)
       with id on every nat leaf.  Unlike bs_p5 (NatList ↔ PList nat) there is
       no structural difference between the two types — the interesting divergence
       is entirely in the evaluation functions, not in the type isomorphism.

       Iso.type A B = { map : A → B; comap : B → A;
                        mapK : comap ∘ map = id; comapK : map ∘ comap = id }

       Iso.toParam converts the isomorphism into a Param44 relation
       (the strongest class, with maps and coherence in both directions). *)

    (* Two problems arise when using universe-polymorphic pexpr directly with Trocq:

       1. pexpr : Type → Type as the sort causes a universe error.
       2. Trocq confuses the implicit {A : Type} argument with the
          translated expression variable.

       Fix: define monomorphic aliases (pconst, pplus, peval_nat) specialised
       to nat so that Trocq sees functions with no implicit sort argument. *)

    (* Note: "rel R_expr_nat e e'" is definitionally "pexpr_2_expr id e = e'".
       Every relational proof reduces to an equality over the conversion function. *)

(*  ── Relation between the constructors ─────────────────────────────────── *)

    (* [pconst ~ econst]:
        natR n n' — Trocq's parametric relation for nat, equivalent to n = n'.
        R_in_map_nat extracts the plain equality from natR.
        Chain: pexpr_2_expr id (pconst n) = Const n =f_equal= Const n' = econst n'.

       [pplus ~ eplus]:
        Given e1 ~ e1' and e2 ~ e2' (i.e., pexpr_2_expr id ei = ei'),
        pexpr_2_expr id (PPlus e1 e2) = Plus e1' e2' by direct rewriting.

       [R_zero — why a separate entry]:
        Param44_nat registers the parametric relation for the TYPE nat.
        Trocq additionally needs an entry for each NUMERAL CONSTANT in the term;
        R_zero provides this for 0 = O. *)

(*  ── Relation between the functions ────────────────────────────────────── *)

    (* [peval_nat ~ eval]:
        peval_nat evaluates PPlus right-to-left; eval evaluates Plus left-to-right.
        peval_eq_eval shows that for any additive f : A → nat,
        f ∘ peval = eval ∘ (pexpr_2_expr f).

        The critical PPlus induction step:

            f (peval e2) + f (peval e1)                      (right-to-left, after Hf)
            = eval (pexpr_2_expr f e1) + eval (pexpr_2_expr f e2)    (by IHs)

        These differ by commutativity of nat's +; lia closes it.
        This is the only place Trocq absorbs work that a manual transfer would
        have to state and prove explicitly. *)

(*  ── Register in Trocq's database ──────────────────────────────────────── *)

    (* Suggested order: type → constructors → functions.
       Trocq generates weaker classes automatically from each Param44 entry. *)

(*  ── The theorem via Trocq ─────────────────────────────────────────────── *)

    (* Each proof has TWO lines:

       1. trocq_expr: rewrites @peval nat addableNat to peval_nat, then
          calls trocq to translate the goal from pexpr_nat/peval_nat to expr/eval.
       2. exact eval_*: closes with the already-proved base theorem.

       For peval_plus_zero_r_auto: without Trocq you need to bridge the
       right-to-left evaluation order manually (a commutativity step).
       Trocq finds and applies peval_eq_eval (with its lia step) automatically.

       Univalence is not needed: the relation is an isomorphism,
       not merely a type equivalence. *)

(*  ── Take notes ────────────────────────────────────────────────────────── *)

    (* Registration (done ONCE for the pair pexpr_nat / expr):
        R_expr_nat  — target type
        R_zero      — constant 0
        R_pconst    — leaf constructor
        R_pplus     — binary constructor
        R_peval_nat — evaluation function
        Param44_nat, Param_add — arithmetic

        Cost: ~7 registrations + 5 definitions + peval_eq_eval.

        Gain: for ANY new theorem about pexpr_nat using peval_nat and pplus,
        the proof is: trocq_expr. exact <theorem_for_expr>.

        Comparison with the manual approach:
        - Manual: needs peval_eq_eval + peval_nat_eq_peval + a rewriting chain
                  → this boilerplate must be repeated for EACH new theorem.
        - Trocq : one-time registration + 2 lines per new theorem. *)

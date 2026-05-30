
Require Import ssreflect.
From Trocq Require Import Trocq.

Require Import HoTTNotations.

Section Trocqlib.
  (* Lemma MereM4 `{Funext} (A B : Type) (R : A -> B -> Type) (map : A -> B) :
  {f : forall x : A, R x (map x) &
    forall (x : A) (y : B) (r : R x y), {e : map x = y & transport (R x) e (f x) = r}} <~>
    {f : forall x : A, R x (map x) & forall (x : A) (y : B) (r : R x y),
(map x; f x) = (y; r)}. *)
End Trocqlib.

Require Import Stdlib.Program.Equality.

Section Preliminary.

  Definition tr {T : Type}{x y : T} (P : T -> Type) (p : x = y) : P x -> P y.
  refine (match p with eq_refl => fun P => P end).
  Defined.

  Definition apd {T : Type}{P : T -> Type} (f : forall x, P x) {x y : T} (p : x = y) : 
    tr _ p (f x) = f y.
  Proof. 
  refine (match p with eq_refl => eq_refl end).
  Defined.

  Lemma tr_concat {T : Type} {x y z : T} (p : x = y) (q : y = z) : tr _ q p = p @ q.
  Proof. 
  move: q.
  refine (match p as p0 in _ = t return forall (q : t = z), tr _ q p0 = p0 @ q with eq_refl => _ end).
  exact (fun q => match q with eq_refl => 1 end).
  Defined.

End Preliminary.

(*Lemma 2.9.6 in the HoTT BooK weakened *)
Axiom L : forall {T : Type}{P Q : T -> Type} {x y : T} (p : x = y) (f : P x -> Q x) (g : P y -> Q y) 
    ,tr (fun x => P x -> Q x) p f = g -> forall x, tr _ p (f x) = g (tr _ p x).

Section Genthm722.

  Variable A B : Type.
  Variable R : A -> B -> Type.
  Variable m : A -> B.
  Variable Rrefl : forall x, R x (m x). (* 2a *)
  Variable imp : forall x y, R x y -> m x = y. (* 2b *)
  Variable MereR : forall x y (r1 r2 : R x y), r1 = r2.

  Definition F {x : A} {y : B}  (p : m x = y) := apd (imp x) p.

  Definition inverses_concat_tr : forall x,
  forall p : m x = m x,
  imp x (m x) (Rrefl x) @ p = imp x (m x) (tr _ p (Rrefl x)).
  Proof. move=> x p.
  rewrite -tr_concat.
  apply L.
  exact: F.
  Defined.

  Definition path_shape : forall x,
  forall p : m x = m x,
  p = (imp x (m x) (Rrefl x))^ @ imp x (m x) (@tr _ _ _ _ p (Rrefl x)).
  Proof.
  move=> x p.
  rewrite -[LHS](concat_1p p).
  rewrite -(concat_Vp (imp x (m x) (Rrefl x))).
  rewrite concat_pp_p.
  apply ap.
  apply inverses_concat_tr.
  Defined.

  Lemma tr_id : forall (x : A) (p : m x = m x), tr (fun y=> R x y) p (Rrefl x) = (Rrefl x).
  Proof. move=> x p; apply MereR. Qed.

  Definition UIP_MA {x y : A} (p q : m x = m y): p = q.
  Proof.
  move: q.
  refine (match p as p0 return forall q, p0 = q with eq_refl => _ end).
  move=> q.
  rewrite (path_shape x 1) /=.
  rewrite (path_shape x q).
  (* rewrite -uniqr. *)
  by rewrite tr_id.
  Defined.

  Section inj.
    Definition injective {A B : Type} (f : A -> B) := forall x y, f x = f y -> x = y.
    Hypothesis m_inj : injective m. 
    
    Lemma ap_inj {C D : Type} (f : C -> D) (inj_f : injective f) : forall x y, injective (@f_equal _ _ f x y).
    Proof.
    move=> x y p1 p2.
    dependent destruction p1.
    dependent destruction p2.
    move=> _ ; exact: eq_refl.
    Defined.
    Print JMeq_refl.

    Definition UIP_A {x y : A} (p q : x = y) : p = q.
    Proof. 
      set mp := @f_equal _ _ m _ _ p.
      set mq := @f_equal _ _ m _ _ q.
      have : mp = mq. by apply UIP_MA.
      by apply: ap_inj.
    Defined.

  End inj.

  Section surj.

    Definition fiber {C D : Type} (f : C -> D) (d : D) := { c & f c = d}.
    Definition isContr (A : Type) := { t & forall t1 : A, t = t1}.
    Definition isProp (A : Type) := forall (x y : A), isContr(x = y).
    Definition surjection {C D : Type} (f : C -> D) := forall y, isProp (fiber f y).
    Hypothesis m_surj : surjection m.

    Lemma UIP_B : forall (x y : B) (p q : x = y), p = q.
    Proof.
    move=> x y.
    have := m_surj x.
    Abort.

  End surj.
  Section surj2.

    Hypothesis comap : B -> A.
    Hypothesis corefl : forall b, R (comap b) b.
    
    Lemma UIP_B : forall (x y : B) (p q : x = y), p = q.
    Proof.
    move=> x y.
    have := (imp _ _ (corefl x)).
    have := (imp _ _ (corefl y)).
    elim.
    elim.
    apply UIP_MA.
    Qed.

  End surj2.

End Genthm722.

Section thm722.

    Variable A : Type.
    Variable R : A -> A -> Type.
    Variable rrefl : forall x, R x x. (* 2a *)
    Variable imp : forall x y, R x y -> x = y.  (* 2b *)
    Variable mereR : forall x y (r1 r2 : R x y), r1 = r2.
    Variable M4 : forall x (r1 r2 : {y & R x y} ), r1 = r2.

    Lemma uip_a (x y : A) (p q : x = y) : p = q.
    Proof. 
    apply (UIP_MA A A R (@id A) rrefl imp). 
    by move=> e ?; apply mereR.
    Qed.

End thm722.


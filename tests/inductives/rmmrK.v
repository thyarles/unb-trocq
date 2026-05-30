Require Import ssreflect.
From Trocq Require Import Trocq.

Require Import HoTTNotations.

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
  
  Lemma left_transpose_eq_concat : forall {T : Type}
        {x y : T} (p : x = y) {z : T} (q : y = z) (r : x = z),
        p @ q = r -> q = p^ @ r.
  Proof.
  move=> T x y p.
  case : _ / p => /= z q r.
  by rewrite !concat_1p. 
  Defined.

(*Lemma 2.9.6 in the HoTT BooK weakened *)
Lemma L : forall {T : Type}{P Q : T -> Type} {x y : T} (p : x = y) (f : P x -> Q x) (g : P y -> Q y) 
    ,tr (fun x => P x -> Q x) p f = g -> forall x, tr _ p (f x) = g (tr _ p x).
Proof.
move=> T P Q x y p.
case: _ / p.
move=> f g /= -> //. 
Defined.

End Preliminary.

Section RmmRK.

  Variable A B : Type.
  Variable R : A -> B -> Type.
  Variable map : A -> B.
  Variable map_in_R : forall x y, map x = y -> R x y. 
  Variable R_in_map : forall x y, R x y -> map x = y.
  Variable mRRmK : forall x y (r : R x y), map_in_R _ _ (R_in_map _ _ r) = r.

  Definition F {x : A} {y : B}  (p : map x = y) := apd (R_in_map x) p.

  Definition inverses_concat_tr : forall x y,
    forall p : map x = y,
    R_in_map x (map x) (map_in_R x (map x) 1) @ p 
    = R_in_map x y (tr _ p (map_in_R x (map x) 1)).
  Proof. 
  move=> x y p.
  rewrite -tr_concat.
  apply L.
  exact: F.
  Defined.

  Definition path_shape {x y} :
  forall p : map x = y,
  p = (R_in_map x (map x) (map_in_R x (map x) 1))^ 
      @ R_in_map x y (tr _ p (map_in_R x (map x) 1)).
  Proof.
  move=> p.
  rewrite -[LHS](concat_1p p).
  rewrite -[X in X @ p](concat_Vp (R_in_map x (map x) (map_in_R x (map x) 1))).
  rewrite concat_pp_p.
  apply ap.
  apply inverses_concat_tr.
  Defined.

  Lemma tr_id : forall (x : A) y (p : map x = y), 
    tr (fun y=> R x y) p (map_in_R _ _ 1) = (map_in_R x y p).
  Proof.
  move=> x y p.
  by case: _ / p .
  Defined.

  Lemma Rm_concat : forall a b b' 
    (e : map a = b)
    (e1 : b = b'),
    R_in_map a b' (map_in_R a b' (e @ e1)) =
    R_in_map a b (map_in_R a b e) @ e1.
  Proof.
  move=> a b1 b2 e e1.
  by case: _ / e1.
  Defined.

  Definition RmmRK : forall a b (e : map a = b), 
   R_in_map _ _ (map_in_R _ _ e) = e.
  Proof.
  move=> a b e.
  rewrite [RHS](path_shape e).
  rewrite tr_id.
  set q := R_in_map a b _.
  set p := R_in_map _ _ _.
  apply (left_transpose_eq_concat p q q).
  rewrite -Rm_concat.
  rewrite concat_1p.
  rewrite mRRmK.
  reflexivity.
  Defined.

End RmmRK.


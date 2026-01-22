From Trocq Require Import mymap mR.
From elpi.apps.derive Require Import derive derive.param2 derive.projK.
Require Import HoTTNotations.
Require Import Hierarchy.
From mathcomp Require Import ssreflect.

Unset Uniform Inductive Parameters.
(* Unset Universe Polymorphism. *)
Unset Universe Minimization ToSet.

Inductive vec (A : Type) : nat -> Type :=
| Ov : vec A O
| Consv : A -> forall n, vec A n -> vec A (S n).

Elpi derive nat.
Elpi derive.param2 vec.

Fixpoint vec_map (A B : Type) (AR : Param10.Rel A B) (n1 n2 : nat) (nR : nat_R n1 n2) {struct nR} : 
  vec A n1 -> vec B n2.
Proof.
case: nR.
- move=> v; exact: (Ov B).
- move=> n1' n2' nR' v.
  refine (Consv B _ _ _).
  + move: v.
    refine (fun v => match v in vec _ (S _) with Consv a n v0 => _ end).
    by apply (map AR).
  + refine (vec_map A B AR n1' n2' nR' _).
    by refine ((match v in vec _ (S t) return ( vec A t) with Consv a n v0 => v0 end)).
Defined.

Definition projConsv1 : 
  forall (A : Type), 
    forall n : nat, vec A (S n) -> A.
refine (fun A n v=> _ ).
by refine (match v in vec _ (S t) return A with 
| Consv a n v0 => a end).
Defined.

Definition projConsv2 : 
  forall (A : Type), 
    A -> forall n : nat, vec A (S n) -> vec A n.
refine (fun A a n v=> _ ).
by refine (match v in vec _ (S t) return vec _ t with 
| Consv a n v0 => v0 end).
Defined.

Definition vec_injections21 :
forall (A : Type) (_1 _2 : A) n (v1 v2 : vec A n) (e : Consv A _1 n v1 = Consv A _2 n v2),
  projConsv1 A n (Consv A _1 n v1) = projConsv1 A n (Consv A _2 n v2).
Proof.
move=> A a1 a2 n v1 v2 eq.
exact: (f_equal _ eq).
Defined.

Definition vec_injections22 :
forall (A : Type) (_1 _2 : A) n (v1 v2 : vec A n)(e : Consv A _1 n v1= Consv A _2 n v2),
  projConsv2 A _1 n (Consv A _1 n v1) = projConsv2 A _1 n (Consv A _2 n v2).
Proof.
move=> A a1 a2 n v1 v2 eq.
exact: (f_equal _ eq).
Defined.

Definition conv (A : Type) (x y : A) (p: x = y) 
    (P : forall x0 : A, x = x0 -> Prop) (P0 : P x eq_refl) :=
  match p as p0 in _ = t return (P t p0)
   with eq_refl => P0 end.

Definition vec_injK21 : 
     forall (A : Type) (_1 _2 : A) (p__1 : _1 = _2) n (_3 _4 : vec A n ) (p__2 : _3 = _4),
(fun (t : A) (p : _1 = t) =>
vec_injections21 A _1 t n _3 _4
(eq_trans (eq_f A (vec A (S n)) (fun R : A => Consv A R n _3) _1 t p)
(eq_trans (eq_f (vec A n) (vec A (S n)) (fun (R : vec A n) => Consv A t n R) _3 _4
p__2) eq_refl)) = p) _2 p__1.
Proof.
move=> A a1 a2 p n v1 v2 p2.
apply (conv A a1 a2 p). 
by apply (conv (vec A n) v1 v2 p2).
Defined. 

Definition vec_injK22 : 
     forall (A : Type) (_1 _2 : A) (p__1 : _1 = _2) n (_3 _4 : vec A n ) (p__2 : _3 = _4),
(fun (t : A) (p : _1 = t) =>
vec_injections22 A _1 t n _3 _4
(eq_trans (eq_f A (vec A (S n)) (fun R : A => Consv A R n _3) _1 t p)
(eq_trans (eq_f (vec A n) (vec A (S n)) (fun (R : vec A n) => Consv A t n R) _3 _4
p__2) eq_refl)) = p__2) _2 p__1.
Proof.
move=> A a1 a2 p n v1 v2 p2.
apply (conv A a1 a2 p). 
by apply (conv (vec A n) v1 v2 p2).
Defined. 

Fixpoint mRvec (A1 A2 : Type) (AR : Param2a0.Rel A1 A2) (n1 n2: nat) (nR : nat_R n1 n2)
        {struct nR} : forall (v1 : vec A1 n1) (v2 : vec A2 n2), vec_map _ _ AR n1 n2 nR v1 = v2 -> vec_R A1 A2 AR n1 n2 nR v1 v2.
case: nR.
- refine (fun v1=> match v1 with Ov => _ end).
  refine (fun v2=> match v2 with Ov => _ end).
  move=> _; exact: Ov_R.
- move=> n1' n2' nR' v1.
  move: mRvec=> /(_ A1 A2 AR _ _ nR')=> mRvec.
  move: nR' mRvec.
  refine (match v1 as vt in vec _ (S t) return 
forall nR' : nat_R t n2',
(forall (v2 : vec A1 t) (v3 : vec A2 n2'),
vec_map A1 A2 AR t n2' nR' v2 = v3 -> vec_R A1 A2 AR t n2' nR' v2 v3) ->
forall v2 : vec A2 (S n2'),
vec_map A1 A2 AR (S t) (S n2') (S_R t n2' nR') vt = v2 ->
vec_R A1 A2 AR (S t) (S n2') (S_R t n2' nR') vt v2
with 
Consv a n v0 => _ end
  ).
  move=> nR' mRvec v2.
  move: nR' mRvec.
  refine (match v2 as vt in vec _ (S t) return 
 forall nR' : nat_R n t,
(forall (v3 : vec A1 n) (v4 : vec A2 t),
vec_map A1 A2 AR n t nR' v3 = v4 -> vec_R A1 A2 AR n t nR' v3 v4) ->
vec_map A1 A2 AR (S n) (S t) (S_R n t nR') (Consv A1 a n v0) = vt ->
vec_R A1 A2 AR (S n) (S t) (S_R n t nR') (Consv A1 a n v0) vt 
with 
Consv a n v0 => _ end
  ).
  move=> nR' mRvec eq.
  apply (Consv_R _ _ _ _ _ (map_in_R AR _ _ (vec_injections21 A2 _ _ _ _ _ eq)) _ _ _).
  by apply (mRvec v3 _ (vec_injections22 A2 _ _ _ _ _ eq)).
Defined.

Fixpoint Rmvec (A1 A2 : Type) (AR : Param2b0.Rel A1 A2) (n1 n2: nat) (nR : nat_R n1 n2)
        : forall (v1 : vec A1 n1) (v2 : vec A2 n2), vec_R A1 A2 AR n1 n2 nR v1 v2 -> vec_map _ _ AR n1 n2 nR v1 = v2.
move=> v1 v2 vR; case: vR.
- exact: eq_refl.
- move=> a1 a2 ar n1' n2' nR' v1' v2' vR' /=.
  move: Rmvec=> /(_ A1 A2 AR _ _ nR')=> Rmvec.
  have@ e1 := f_equal (fun a2'=> Consv A2 a2' n2' (vec_map A1 A2 AR n1' n2' nR' v1')) (R_in_map AR _ _ ar).
  have@ e2 := f_equal (fun v => Consv A2 a2 n2' v) (Rmvec _ _ vR').
  exact: (e1 @ e2).
Defined.

Fixpoint mRRmvec (A1 A2 : Type) (AR : Param40.Rel A1 A2) (n1 n2: nat) (nR : nat_R n1 n2)
        : forall (v1 : vec A1 n1) (v2 : vec A2 n2) (vR: vec_R A1 A2 AR n1 n2 nR v1 v2),
        mRvec A1 A2 AR n1 n2 nR v1 v2 (Rmvec A1 A2 AR n1 n2 nR v1 v2 vR) = vR. 
move=> v1 v2 vR; case: vR.
- exact: eq_refl.
- move=> a1 a2 ar n1' n2' nR' v1' v2' vR' /=.
  move: mRRmvec=> /(_ A1 A2 AR _ _ nR')=> mRRmvec.
  rewrite vec_injK21 vec_injK22. rewrite (R_in_mapK AR). rewrite (mRRmvec v1' v2' vR').
  reflexivity.
Defined.
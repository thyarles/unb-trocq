
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

From Coq Require Import ssreflect.
From elpi.apps.derive Require Import eqb_core_defs derive.std derive.legacy.
Require Import HoTT_additions Hierarchy.
Unset Uniform Inductive Parameters.
Unset Universe Polymorphism.

Definition eqnn := @eq_ind_r_nP.
(* Inductive nums := *)
(*   | ZZZ | NNN : nums -> nums. *)

(* Inductive OhOh := *)
(*   | C : (forall A, A -> A) -> OhOh. *)

(* Elpi derive nums. *)
(* Elpi derive OhOh. *)

(* Check OhOh_induction. *)

(* Set Universe Polymorphism. *)
Unset Universe Minimization ToSet.

Notation Unit := unit.

Inductive UnitR : Unit -> Unit -> Type :=
  | ttR : UnitR tt tt.

Definition m_unit : unit -> unit := idmap.
Definition mR_Unit (u1 u2 : Unit) : m_unit u1 = u2 -> UnitR u1 u2.
Proof.
refine (fun e =>
  match u1 with
  | tt => match u2 with
          | tt => ttR
          end end
).
Defined.

Definition Rm_Unit (u1 u2 : Unit) : UnitR u1 u2 -> m_unit u1 = u2.
Proof.
refine (fun r =>
  match r with
  | ttR => 1
  end
).
Defined.

Definition mRRmK_Unit (u1 u2 : Unit) (r1 : UnitR u1 u2) : mR_Unit u1 u2 (Rm_Unit u1 u2 r1) = r1.
Proof.
by elim: r1.
Qed.

Notation Bool := bool.

Inductive BoolR : Bool -> Bool -> Type :=
  | falseR : BoolR false false
  | trueR : BoolR true true.

Definition map_Bool : Bool -> Bool := id.

Definition exF : forall T, true = false -> T :=
fun T e => 
    match e in _ = t return 
        match t with
        | false => T
        | true => unit
        end
    with eq_refl => tt end.

Definition exF' : forall T, false = true -> T :=
fun T e => 
    match e in _ = t return 
        match t with
        | true => T
        | false => unit
        end
    with eq_refl => tt end.


Definition mR_Bool : forall (b b' : Bool) (e : map_Bool b = b'), BoolR b b' :=
  fun b b' => 
     match b as bb with  
    | true => match b' as bb' with 
              | true => fun e => trueR 
              | false => fun e => exF _ e
              end 
    | false => match b' with 
              | true => fun e => exF' _ e
              | false => fun e => falseR
              end
    end.

Definition Rm_Bool : forall (b b' : Bool)  (bR: BoolR b b'), (map_Bool b = b') :=
fun b b' bR => 
        match bR with 
        | trueR => idpath 
        | falseR => idpath 
        end.

Definition mRRmKBool : forall (b b' : Bool) (bR : BoolR b b'),
    mR_Bool b b' (Rm_Bool b b' bR) = bR.
Proof. 
move=> b b' []//=. 
Qed.

Inductive enum :=
| K1 : unit -> enum
| K2 : Bool -> enum.

Definition m_enum : enum -> enum := idmap. 
Inductive enumR : enum -> enum -> Type :=
  | K1R : forall u1 u2, UnitR u1 u2 -> enumR (K1 u1) (K1 u2)
  | K2R : forall b1 b2, BoolR b1 b2 -> enumR (K2 b1) (K2 b2).

Definition K1_proj1 : forall u : unit, enum -> unit :=
fun u e => match e with K1 u => u | K2 _ => u end. 


Lemma K1_inj (u1 u2 : unit) : K1 u1 = K1 u2 -> u1 = u2.
Proof.
move=> e.
exact (ap (K1_proj1 u1) e).
Defined.

Lemma K1_inj' (u1 u2 : unit) : K1 u1 = K1 u2 -> u1 = u2.
Proof.
by case. 
Defined.

Definition K1_inj'' (u1 u2 : unit) : K1 u1 = K1 u2 -> u1 = u2 :=
let p := fun u e => match e with K1 u => u | K2 _ => u end in 
fun e => ap (p u1) e.


Definition K2_proj1 : forall b : bool, enum -> bool :=
fun b e => match e with K2 b => b | K1 _ => b end. 

Lemma K2_inj (b1 b2 : bool) : K2 b1 = K2 b2 -> b1 = b2.
Proof.
move=> e. exact (ap (K2_proj1 b1) e).
Defined.

Lemma K1_K2_discr (T : Type) (u1 : unit)(b1 : bool) : K1 u1 = K2 b1 -> T.
Proof.
    move=> e.
refine (match e in _ = t return 
            match t with 
            | K1 _ => unit 
            | K2 _ => T end
            
            with eq_refl => tt end
         ).
Defined.

Lemma K2_K1_discr (T : Type)  (b : bool) (u : unit): K2 b = K1 u -> T.
Proof.
move=> e.
refine ( match e in _ = t return 
            match t with
            | K1 _ => T 
            | K2 _ => unit 
            end 
        with eq_refl => tt end ).
Defined.

Definition mR_enum : forall (e1 e2 : enum), m_enum e1 = e2 -> enumR e1 e2.
Proof.
move=> e1 e2.
elim: e1=> [u1|b1]; elim: e2=> [u2|b2].
- move=> /K1_inj e; apply (K1R _ _ (mR_Unit _ _ e)).
- move=> /K1_K2_discr => /(_ False) [].
- move=> /K2_K1_discr => /(_ False) [].
- move=> /K2_inj e; apply (K2R _ _ (mR_Bool _ _ e)).
Defined.

Print mR_enum.

Definition mR_enum' : forall (e1 e2 : enum), m_enum e1 = e2 -> enumR e1 e2.
Proof.
refine (fun e1 e2 => 
  match e1 with 
  | K1 u1 => match e2 with 
            | K1 u2 => fun e => K1R _ _ (mR_Unit _ _ (K1_inj _ _ e))
            | K2 b2 => fun e => K1_K2_discr _ u1 b2 e
            end 
  | K2 b1 => match e2 with 
            | K1 u2 => fun e => K2_K1_discr _ b1 u2 e
            | K2 b2 => fun e => K2R _ _ (mR_Bool _ _ (K2_inj _ _ e))
            end
  end
). 
Defined.

Definition Rm_enum : forall (e1 e2 : enum)  (eR: enumR e1 e2), (m_enum e1 = e2).
Proof.
refine (
fun e1 e2 eR => 
   match eR with 
   | K1R u1 u2 uR => (ap K1 (Rm_Unit _ _ uR)) (* match uR with ttR => idpath end *)
   | K2R b1 b2 bR => (ap K2 (Rm_Bool _ _ bR))
        end).
Defined. 

Fixpoint eq_ind_r_n (T : tlist) : p_type T -> p_type T -> Prop :=
  match T return p_type T -> p_type T -> Prop with
  | tnil       => fun p q => p -> q
  | tcons T Ts => fun p q => forall (x y : T), x = y -> @eq_ind_r_n Ts (p x) (q y)
  end.
 
Lemma eq_ind_r_nP (T : tlist) (p : p_type T) : @eq_ind_r_n T p p.
Proof. elim: T p => //= T Ts hrec f a1 a2 ->; apply hrec. Defined.

Lemma eq_ind_r_nP' : forall (T : tlist) (p : p_type T), @eq_ind_r_n T p p.
Proof.
elim.
- refine (fun p H=> H).
- simpl. move=> T TS IH p x y e.
elim: (ap p e).
apply IH.
Defined.
Print eq_ind_r_nP'.
(* Lemma eq_ind_r_nP'' : forall (T : tlist) (p : p_type T), @eq_ind_r_n T p p.
refine (fix IH => fun T match T with
                     | tnil => _
                     | tcons _ _ => _
                     end).

elim.
- move=> p. exact id.
- move=> T Ts hrec f a1 a2.
  elim. apply hrec.
Defined. *)

Definition eqnn_transp := @eq_ind_r_nP'.

Definition Rm_enum' : forall (e1 e2 : enum)  (eR: enumR e1 e2), (m_enum e1 = e2) :=
fun e1 e2 eR =>
   match eR with
   | K1R u1 u2 uR =>
        eqnn (tcons Unit tnil) (fun u1' => K1 u1 = K1 u1' ) _ _ (Rm_Unit _ _ uR) eq_refl
   | K2R u1 u2 uR =>
        eqnn (tcons Bool tnil) (fun u1' => K2 u1 = K2 u1' ) _ _ (Rm_Bool _ _ uR) eq_refl
        end.

Definition Rm_enum'' : forall (e1 e2 : enum)  (eR: enumR e1 e2), (m_enum e1 = e2) :=
fun e1 e2 eR =>
   match eR with
   | K1R u1 u2 uR =>
        eqnn_transp (tcons Unit tnil) (fun u1' => K1 u1 = K1 u1' ) _ _ (Rm_Unit _ _ uR) eq_refl
   | K2R u1 u2 uR =>
        eqnn_transp (tcons Bool tnil) (fun u1' => K2 u1 = K2 u1' ) _ _ (Rm_Bool _ _ uR) eq_refl
        end.

Lemma inj_projK (u1 u2 : unit) (e : m_unit u1 = u2) :
(K1_inj u1 u2 (ap K1 e)) = e.
Proof.
by rewrite /K1_inj -ap_compose /= ap_idmap. Qed.

Definition mRRmKEnum : forall (e1 e2 : enum) (eR : enumR e1 e2),
    mR_enum _ _ (Rm_enum _ _ eR) = eR.
Proof. 
move=> e1 e2 []//=.
- move=> u1 u2 uR.
  by rewrite /K1_inj -ap_compose /= ap_idmap mRRmK_Unit.
- move=> b1 b2 bR.
  by rewrite /K2_inj -ap_compose /= ap_idmap mRRmKBool.
Defined.

Definition mRRmKEnum' : forall (e1 e2 : enum) (eR : enumR e1 e2),
    mR_enum' _ _ (Rm_enum _ _ eR) = eR.
Proof. 
move=> e1 e2 []//=.
- move=> u1 u2 uR.
  by rewrite /K1_inj -ap_compose /= ap_idmap mRRmK_Unit.
- move=> b1 b2 bR.
  by rewrite /K2_inj -ap_compose /= ap_idmap mRRmKBool.
Defined.
Print mRRmKEnum.

Inductive enum3 :=
| KK1 : unit -> unit -> enum3
| KK2 : bool -> bool -> enum3.

Inductive enum3R : enum3 -> enum3 -> Type :=
| KK1R : forall (u1 u2 : unit), UnitR u1 u2 
         -> forall (u3 u4 : unit), UnitR u3 u4 
         -> enum3R (KK1 u1 u3) (KK1 u2 u4)
| KK2R : forall (b1 b2 : bool), BoolR b1 b2 
  -> forall (b3 b4 : bool), BoolR b3 b4 
  -> enum3R (KK2 b1 b3) (KK2 b2 b4).

(* Elpi derive.map "pp". *)
Elpi derive.map "unit".
Elpi derive.map "bool".
Elpi derive.map "list".
Elpi derive.projK enum.
Print projK11.
Print projK21.
Elpi derive.projK list.
Print projcons1.
Print projcons2.


Elpi derive.projK enum3.
Print projKK11.

Definition KK1_proj1 (u1 : unit) : enum3 -> unit:=
  fun e => match e with KK1 u1 _ => u1 | _ => u1 end.

Definition KK1_proj2 (u1 : unit) : enum3 -> unit:=
  fun e => match e with KK1 _ u1 => u1 | _ => u1 end.

Definition KK2_proj1 (b1 : bool) : enum3 -> bool:=
  fun e => match e with KK2 b1 _ => b1 | _ => b1 end.

Definition KK2_proj2 (b1 : bool) : enum3 -> bool:=
  fun e => match e with KK2 _ b1 => b1 | _ => b1 end.

Definition tr_ap {A : Type} {B : A -> Type} {C : Type} {D : C -> Type}
    (f : A -> C) (g : forall (x : A) , B x -> D (f x))
    {x y : A} (p : x = y) (z : B x) :  
  transport D (ap f p) (g x z) = g y (transport B p z).
Proof.
exact (match p with eq_refl => eq_refl end).
Defined.

Definition KK1_inj1 (u1 u2 u3 u4 : unit) : KK1 u1 u2 = KK1 u3 u4 -> u1 = u3.
Proof.
  (* by refine (fun e => match e with eq_refl => eq_refl end). *)
  move=> e.
  (* sol1  *)
  (* apply (ap (fun x=> KK1 x u4)). *)
  exact: (ap (KK1_proj1 u1) e).

  (* eo sol1 *)
  (* sol2  *)
  (* have@ e' := (ap (KK1_proj2 u2) e) : u2 = u4. *)
  (* have@ e'' := (ap (KK1_proj1 u1) e) : u1 = u3. *)
  (* have@ e''' : KK1 u1 u4 = KK1 u3 u4. *)
  (*   have@ aux_transp1 : KK1 u1 u2 = KK1 u3 u2. *)
  (*     by apply (ap ( ( fun x => (KK1 x u2) ) ) e''). *)
  (*     (* by apply (ap ( ( fun x => (KK1 x u2) ) o (KK1_proj1 u1) ) e). *) *)
  (*   by have@ aux := (transport (fun x=> KK1 u1 x = KK1 u3 x) e' aux_transp1). *)
  (* exact: (ap (KK1_proj1 u1) e'''). *)
  (* Show Proof. *)
  (* eo sol2  *)
Defined.

Definition KK1_inj2 (u1 u2 u3 u4 : unit) : KK1 u1 u2 = KK1 u3 u4 -> u2 = u4.
exact: (fun e => (ap (KK1_proj2 u2) e)).
(* by refine (fun e => match e with eq_refl => eq_refl end). *)
Defined.

Definition KK2_inj1 (u1 u2 u3 u4 : bool) : KK2 u1 u2 = KK2 u3 u4 -> u1 = u3.
exact: (fun e => (ap (KK2_proj1 _) e)).
Defined.

Definition KK2_inj2 (u1 u2 u3 u4 : bool) : KK2 u1 u2 = KK2 u3 u4 -> u2 = u4.
exact: (fun e => (ap (KK2_proj2 u2) e)).
Defined.

(* Definition KK2_inj1 (b1 b2 b3 b4 : bool) : KK2 b1 b2 = KK2 b3 b4 -> b1 = b3. *)
(* Proof. *)
(* by refine (fun e => match e with eq_refl => eq_refl end). *)
(* Defined. *)

(* Definition KK2_inj2 (b1 b2 b3 b4 : bool) : KK2 b1 b2 = KK2 b3 b4 -> b2 = b4. *)
(* by refine (fun e => match e with eq_refl => eq_refl end). *)
(* Defined. *)

Definition KK1_KK2 (T : Type) (u1 u2 : unit) (b1 b2 : bool) : 
  KK1 u1 u2 = KK2 b1 b2 -> T.
Proof. 
refine (fun e => match e in _ = t return 
                    match t with 
                    | KK1 _ _ => unit 
                    | KK2 _ _ => T end 
                    with eq_refl => tt end).
Defined.

Definition KK2_KK1 (T : Type) (b1 b2 : bool) (u1 u2 : unit) : 
  KK2 b1 b2 = KK1 u1 u2 -> T.
Proof. 
refine (fun e => match e in _ = t return 
                    match t with 
                    | KK1 _ _ => T 
                    | KK2 _ _ => unit end 
                    with eq_refl => tt end).
Defined.

Definition mR_enum3 (e1 e2 : enum3) : e1 = e2 -> enum3R e1 e2.
Proof.
refine (
match e1 with 
| KK1 u1 u2 => match e2 with 
               | KK1 u3 u4 => fun e => KK1R _ _ (mR_Unit _ _ (KK1_inj1 u1 u2 u3 u4 e)) _ _ (mR_Unit _ _ (KK1_inj2 u1 u2 u3 u4 e))
               | KK2 b1 b2  => fun e => KK1_KK2 _ _ _ _ _ e
               end 
| KK2 b1 b2 => match e2 with 
               | KK1 u1 u2 => fun e => KK2_KK1 _ _ _ _ _ e 
               | KK2 b3 b4 => fun e => KK2R _ _ (mR_Bool _ _ (KK2_inj1 _ _ _ _ e))
                                            _ _ (mR_Bool _ _ (KK2_inj2 _ _ _ _ e))
                end
end
).
Defined.

Lemma KK1_curry : forall u1 u2, KK1 u1 u2 = (uncurry KK1) (u1,u2).
Proof.
reflexivity.
Defined.

Definition Rm_enum3 (e1 e2 : enum3) : enum3R e1 e2 -> e1 = e2.
Proof.
elim.
- move=> u1 u2 uR1 u3 u4 uR2.
  (* rewrite !KK1_curry. *)
  (* apply ap. *)
  (* apply ap.
  pose F := uncurry KK1. *)
  elim: (Rm_Unit _ _ uR1).
  (* apply ap. *)
  elim: (Rm_Unit _ _ uR2).
  reflexivity.
  (* by apply ap. *)
- move=> b1 b2 bR1 b3 b4 bR2.
  elim: (Rm_Bool _ _ bR1). 
  elim: (Rm_Bool _ _ bR2). 
  by apply ap.
Defined.
Print Rm_enum3.
Print f_equal2.
(* Definition Rm_enum3' (e1 e2 : enum3) : enum3R e1 e2 -> e1 = e2.
Proof.
elim.
- move=> u1 u2 uR1 u3 u4 uR2.
  apply (ap (KK1 u1) (Rm_Unit _ _ uR1)).
  elim: (Rm_Unit _ _ uR1).
  elim: (Rm_Unit _ _ uR2).
  by apply ap.
- move=> b1 b2 bR1 b3 b4 bR2.
  elim: (Rm_Bool _ _ bR1). 
  elim: (Rm_Bool _ _ bR2). 
  by apply ap.
Defined. *)

Definition Rm_enum3' (e1 e2 : enum3) : enum3R e1 e2 -> e1 = e2.
Proof.
elim.
- move=> u1 u2 uR1 u3 u4 uR2.
  by apply (eqnn (tcons Unit (tcons Unit tnil)) (fun u1' u2' => KK1 u1 u3 = KK1 u1' u2') u1 u2 (Rm_Unit u1 u2 uR1) u3 u4 (Rm_Unit u3 u4 uR2) ).
- move=> u1 u2 uR1 u3 u4 uR2.
  by apply (eqnn (tcons Bool (tcons Bool tnil)) (fun u1' u2' => KK2 u1 u3 = KK2 u1' u2') u1 u2 (Rm_Bool u1 u2 uR1) u3 u4 (Rm_Bool u3 u4 uR2) ).
Defined.

Definition Rm_enum3''' (e1 e2 : enum3) : enum3R e1 e2 -> e1 = e2.
Proof.
  elim.
  - move=> u1 u2 uR1 u3 u4 uR2.
    (* have e := ap (fun u => KK1 u u3) (Rm_Unit _ _ uR1). *)
    (* have e' := ap (fun u => KK1 u2 u) (Rm_Unit _ _ uR2). *)
    (* exact: (e @ e'). *)
    exact: (ap (fun u => KK1 u u3) (Rm_Unit _ _ uR1) @ ap (fun u => KK1 u2 u) (Rm_Unit _ _ uR2)).
  - move=> u1 u2 uR1 u3 u4 uR2.
    (* have e := ap (fun u => KK2 u u3) (Rm_Bool _ _ uR1). *)
    (* have e' := ap (fun u => KK2 u2 u) (Rm_Bool _ _ uR2). *)
    (* exact: (e @ e'). *)
    exact: (ap (fun u => KK2 u u3) (Rm_Bool _ _ uR1) @ ap (fun u => KK2 u2 u) (Rm_Bool _ _ uR2)).
Defined.

Definition Rm_enum3'''' (e1 e2 : enum3) : enum3R e1 e2 -> e1 = e2.
Proof.
  elim.
  - move=> u1 u2 uR1 u3 u4 uR2.
    (* have e'' := ap (fun u => KK1 u1 u) (Rm_Unit _ _ uR2). *)
    (* have e''' := ap (fun u => KK1 u u4) (Rm_Unit _ _ uR1). *)
    (* exact: (e'' @ e'''). *)
    exact: ( (ap (fun u => KK1 u1 u) (Rm_Unit _ _ uR2)) @ (ap (fun u => KK1 u u4) (Rm_Unit _ _ uR1))).
  - move=> u1 u2 uR1 u3 u4 uR2.
    (* have e := ap (fun u => KK2 u u3) (Rm_Bool _ _ uR1). *)
    (* have e' := ap (fun u => KK2 u2 u) (Rm_Bool _ _ uR2). *)
    (* exact: (e @ e'). *)
    exact: ( (ap (fun u => KK2 u1 u) (Rm_Bool _ _ uR2)) @ (ap (fun u => KK2 u u4) (Rm_Bool _ _ uR1))).
Defined.

Definition Rm_enum3'' (e1 e2 : enum3) : enum3R e1 e2 -> e1 = e2 := 
fun eR => 
match eR with 
| KK1R u1 u2 uR1 u3 u4 uR2 => 
    (eqnn (tcons Unit (tcons Unit tnil)) 
          (fun u1' u2' => KK1 u1 u3 = KK1 u1' u2') 
          u1 u2 (Rm_Unit u1 u2 uR1) u3 u4 (Rm_Unit u3 u4 uR2) 
          eq_refl)
| KK2R u1 u2 uR1 u3 u4 uR2 => 
    (eqnn (tcons Bool (tcons Bool tnil)) 
          (fun u1' u2' => KK2 u1 u3 = KK2 u1' u2') 
          u1 u2 (Rm_Bool u1 u2 uR1) u3 u4 (Rm_Bool u3 u4 uR2) 
          eq_refl)
end.
Print f_equal.
Search f_equal f_equal2.

Definition tr_id {A : Type} {B : A -> Type} {a : A}
  (f : forall (x : A), a = x -> B x)
  (x : A) (p : a = x) : f x p = transport B p (f a eq_refl).
Proof.
  exact: (match p with eq_refl => eq_refl end).
Defined.

Definition preserves_tr {I : Type} {A : I -> Type} {B : I -> Type} (f : forall (i : I),  A i -> B i)
  {i j : I} (p : i = j) (x : A i) :
  f j (transport A p x) = transport B p (f i x).
Proof.
  exact: (match p with eq_refl => eq_refl end).
Defined.

Definition compute_preserves_tr {I : Type} {A : I -> Type} {B : I -> Type}
  (f : forall (i : I), A i -> B i)
  {i j : I} (p : i = j) (x : A i) :
  preserves_tr _ p x =
    (tr_ap id f p x)^ @ ap (fun q => transport B q (f i x)) (ap_idmap p).
Proof.
  exact: (match p with eq_refl => eq_refl end).
Defined.

Definition substitution_law_tr {X : Type} {A : Type} (B : A -> Type) (f : X -> A)
  {x y : X} (p : x = y) {x' : B (f x)} :
  transport B (ap f p) x' = transport (B o f) p x'.
Proof.
  apply (tr_ap f (fun _ => idmap) p x').
Defined.

Definition tr_Id_left {A : Type} {a b c : A} (q : b = c) (p : b = a) :
  transport (fun x => x = a) q p = q^ @ p.
Proof.
  refine ((match q with eq_refl => _ end)).
  by rewrite transport1 concat_1p.
Defined.

Definition tr_Id_right {A : Type} {a b c : A} (q : b = c) (p : a = b) :
  transport (fun x => a = x) q p = p @ q.
Proof.
  refine ((match q with eq_refl => _ end)).
  by rewrite transport1 concat_p1.
Defined.

Definition KK1_proj1K : forall u1 u2 (p1 : u1 = u2) u3 u4 (p2 : u3 = u4),
  (ap (KK1_proj1 u1)
     (ap (fun u : Unit => KK1 u u3) p1 @
        ap (fun u : Unit => KK1 u2 u) p2)) = p1.
Proof.
  refine (fun u1 u2 p1 => match p1 as p0 in _ = t
                            return
                            forall u3 u4 p2, (ap (KK1_proj1 u1)
                               (ap (fun u : Unit => KK1 u u3) p0 @
                                  ap (fun u : Unit => KK1 t u) p2)) = p0
                      with eq_refl => _ end

         ).
  refine (fun u3 u4 p2 => match p2 as p0 in _ = t
                            return
                            (ap (KK1_proj1 u1)
                               (ap (fun u : Unit => KK1 u u3) 1 @
                                  ap (fun u : Unit => KK1 u1 u) p0)) = 1
                      with eq_refl => eq_refl end
         ).
Defined.

Definition KK1_proj2K : forall u1 u2 (p1 : u1 = u2) u3 u4 (p2 : u3 = u4),
  (ap (KK1_proj2 u3)
     (ap (fun u : Unit => KK1 u u3) p1 @
        ap (fun u : Unit => KK1 u2 u) p2)) = p2.
Proof.
  refine (fun u1 u2 p1 => match p1 as p0 in _ = t
                            return
                            forall u3 u4 p2, (ap (KK1_proj2 u3)
                               (ap (fun u : Unit => KK1 u u3) p0 @
                                  ap (fun u : Unit => KK1 t u) p2)) = p2
                       with eq_refl => _ end

         ).
  refine (fun u3 u4 p2 => match p2 as p0 in _ = t
                             return
                             (ap (KK1_proj2 u3)
                               (ap (fun u : Unit => KK1 u u3) 1 @
                                  ap (fun u : Unit => KK1 u1 u) p0)) = p0
                      with eq_refl => eq_refl end
         ).
Defined.

Definition KK2_proj1K : forall b1 b2 (p1 : b1 = b2),
    forall b3 b4 (p2 : b3 = b4),

  (ap (KK2_proj1 b4)
          (ap (fun u : Bool => KK2 u b3) p1 @
             ap (fun u : Bool => KK2 b2 u) p2)) = p1.
Proof.
  refine (
      fun b1 b2 p1 =>
        match p1 as p0 in _ = t
              return
              forall b3 b4 p2, (ap (KK2_proj1 b4)
                 (ap (fun u : Bool => KK2 u b3) p0 @
                    ap (fun u : Bool => KK2 t u) p2)) = p0
        with eq_refl => _ end
    ).
  refine (

      fun b3 b4 p2 =>
        match p2 as p0 in _ = t
              return
               (ap (KK2_proj1 t)
                 (ap (fun u : Bool => KK2 u b3) 1 @
                    ap (fun u : Bool => KK2 b1 u) p0)) = 1
        with eq_refl => eq_refl end
    ).
Defined.

Definition KK2_proj2K : forall b1 b2 (p1 : b1 = b2),
  forall b3 b4 (p2 : b3 = b4),
    (* (ap (KK2_proj2 b4) *)
    KK2_inj2 b1 b3 b2 b4 (
       (ap (fun u : Bool => KK2 u b3) p1 @
          ap (fun u : Bool => KK2 b2 u) p2)) = p2.
Proof.
  refine (
      fun b1 b2 p1 =>
        match p1 as p0 in _ = t
              return
              forall b3 b4 p2,
                KK2_inj2 b1 b3 t b4
                            ((ap (fun u : Bool => KK2 u b3) p0) @ (ap (fun u : Bool => KK2 t u) p2)) = p2
        with eq_refl => _ end
    ).
  refine (
      fun b3 b4 p2 =>
        match p2 as p0 in _ = t
              return
              KK2_inj2 b1 b3 b1 t
                 ((ap (fun u : Bool => KK2 u b3) 1 @
                    ap (fun u : Bool => KK2 b1 u) p0)) = p0
        with eq_refl => eq_refl end
    ).
Defined.

Lemma mRRmK_enum3' (e1 e2 : enum3) (eR : enum3R e1 e2) : mR_enum3 _ _ (Rm_enum3''' _ _ eR) = eR.
Proof.
  elim: eR=> /=.
  - move=> u1 u2 uR1 u3 u4 uR2 /=.
    by rewrite /KK1_inj1 KK1_proj1K /KK1_inj2 KK1_proj2K !mRRmK_Unit.
  - move=> b1 b2 bR1 b3 b4 bR2 /=.
    by rewrite /KK2_inj1 KK2_proj1K KK2_proj2K !mRRmKBool.
Defined.

Inductive pp :=
| Z
| S : pp -> pp.

Inductive ppR : pp -> pp -> Type :=
| ZR : ppR Z Z
| SR : forall pp1 pp2, ppR pp1 pp2 -> ppR (S pp1) (S pp2).

Definition map_pp : pp -> pp := id.

Fixpoint map_pp' (p : pp) : pp :=
  match p with
  | Z => Z
  | S p' => S (map_pp' p')
  end.

Definition S_proj (dflt : pp) (p1 : pp) : pp :=
match p1 with
| Z => dflt
| S p1' => p1'
end.

Definition S_inj (p1 p2 : pp) : (S p1) = S p2 -> p1 = p2.
by move=> /(ap (S_proj p1)).
Defined.

Definition S_inj' (p1 p2 : pp) : map_pp (S p1) = S p2 -> map_pp p1 = p2.
by case.
Defined.

Definition map_S_e (p1 p2 : pp) : p1 = p2 -> (S p1) = (S p2).
by apply (ap S).
Defined.

Definition map_S_e' (p1 p2 : pp) : map_pp p1 = p2 -> map_pp (S p1) = (S p2).
by elim.
Defined.

Definition inj_projK_pp (p1 p2 : pp) (e : p1 = p2): S_inj p1 p2 (map_S_e p1 p2 e) = e.
Proof.
by rewrite /S_inj/map_S_e -ap_compose ap_idmap. 
Defined.

Definition inj_projK_pp' (p1 p2 : pp) (e : p1 = p2): S_inj p1 p2 (ap S e) = e.
Proof.
by refine (
    match e as p0 in _ = t
                           return S_inj p1 t (ap S p0) = p0
                                                           with eq_refl => eq_refl end
  ).
Defined.

Definition ex_falso_Z_pp (T : Type) (p1 : pp) : map_pp Z = S p1 -> T.
refine (
fun e => match e in _ = t return 
         match t with 
         | Z => Unit
         | S _ => T end 
         with eq_refl => tt end

).
Defined.

Definition ex_falso_pp_ZZ (T : Type) (p1 : pp) : map_pp (S p1) = Z -> T.
refine (
fun e => match e in _ = t return 
         match t with 
         | Z => T
         | S _ => Unit end 
         with eq_refl => tt end

).
Defined. 

Definition mR_pp : forall p1 p2, (map_pp p1) = p2 -> ppR p1 p2.
elim=> [|p1' IHn]. 
- case=> [|p2'].
  + move=> e; exact: ZR.
  + move=> /ex_falso_Z_pp contr; apply contr.
- case=> [|p2'].
  + move=> /ex_falso_pp_ZZ contr; apply contr.
  + move=> /S_inj e; exact: SR _ _ (IHn _ e).
Defined.

Definition mR_pp' : forall p1 p2, (map_pp' p1) = p2 -> ppR p1 p2.
elim=> [|p1' IHn].
- case=> [|p2'].
  + move=> e; exact: ZR.
  + move=> /ex_falso_Z_pp contr; apply contr.
- case=> [|p2'].
  + move=> /ex_falso_pp_ZZ contr; apply contr.
  + move=> /S_inj e; exact: SR _ _ (IHn _ e).
Defined.

Print ppR_ind.
Definition Rm_pp : forall p1 p2, ppR p1 p2 -> map_pp p1 = p2.
move=> p1 p2 eR.
elim : eR => [| p1' p2' hR rec]. 
- exact: idpath.
- by apply map_S_e.
Defined.

Definition Rm_pp'' : forall p1 p2, ppR p1 p2 -> map_pp' p1 = p2.
  move=> p1 p2 eR.
  elim : eR => [| p1' p2' hR rec].
  - exact: idpath.
  - by apply (ap S rec).
Defined.

Definition Rm_pp' : forall p1 p2, ppR p1 p2 -> map_pp p1 = p2.
move=> p1 p2.
fix IH 1.
elim.
- exact: idpath.
- by move=> p1' p2' ppR' rec; apply: map_S_e.  
Defined.

Definition mRRmK_pp : forall p1 p2 (pR : ppR p1 p2), mR_pp _ _ (Rm_pp _ _ pR) = pR.
Proof.
move=> p1 p2; elim.
- reflexivity.
- move=> p1' p2' eR' rec.
  move=> /=. apply ap. by rewrite inj_projK_pp rec.
Defined.

(* with map <> id *)
Definition mRRmK_pp': forall p1 p2 (pR : ppR p1 p2), mR_pp' _ _ (Rm_pp'' _ _ pR) = pR.
Proof.
  move=> p1 p2; elim.
  - reflexivity.
  - move=> p1' p2' eR' rec.
    rewrite /=.
  by rewrite inj_projK_pp' rec.
Defined.

Module i.
  Inductive issue (A B C : Type) :=
  | K1 : unit -> enum -> pp -> issue A B C
  | K2 : A -> B -> C -> issue A B C
  (* | K3 : A -> pp -> issue A *)
  | K4 : issue A B C -> issue A B C -> issue A B C -> issue A B C.

Elpi derive.map "issue".
Elpi derive.projK issue.
Print issue_map.
Print projK11.
Inductive issueR
  (A A' : Type) (AR : A -> A' -> Type)
  (B B' : Type) (BR : B -> B' -> Type)
  (C C' : Type) (CR : C -> C' -> Type)
  : issue A B C -> issue A' B' C' -> Type :=
| K1R :
  forall u1 u2 (uR : UnitR u1 u2),
  forall e1 e2 (eR : enumR e1 e2),
  forall p1 p2 (pR : ppR p1 p2),
    issueR A A' AR B B' BR C C' CR (K1 A B C u1 e1 p1) (K1 A' B' C' u2 e2 p2)
| K2R :
  forall a1 a2 (aR : AR a1 a2),
  forall b1 b2 (bR : BR b1 b2),
  forall c1 c2 (cR : CR c1 c2),
    issueR A A' AR B B' BR C C' CR (K2 A B C a1 b1 c1) (K2 A' B' C' a2 b2 c2)
| K4R :
  forall i1 i2 (iR1 : issueR A A' AR B B' BR C C' CR i1 i2),
  forall i3 i4 (iR2 : issueR A A' AR B B' BR C C' CR i3 i4),
  forall i5 i6 (iR3 : issueR A A' AR B B' BR C C' CR i5 i6),
    issueR A A' AR B B' BR C C' CR (K4 A B C i1 i3 i5) (K4 A' B' C' i2 i4 i6).

(* Definition issue_map *)
(*   (A A' : Type) (AR : Param10.Rel A A') *)
(*   (B B' : Type) (BR : Param10.Rel B B') *)
(*   (C C' : Type) (CR : Param10.Rel C C') *)
(*   : issue A B C -> issue A' B' C' := *)
(*   let fix im (ia : issue A B C) {struct ia} : issue A' B' C' := *)
(*     match ia with *)
(*     | K1 _ _ _ u e p => K1 A' B' C' u e p *)
(*     | K2 _ _ _ a b c => K2 A' B' C' (map AR a) (map BR b) (map CR c) *)
(*     (* | K3 _ a pp => K3 A' (map AR a) pp *) *)
(*     | K4 _ _ _ ia1 ia2 ia3 => K4 A' B' C' (im ia1) (im ia2) (im ia3) end in *)
(*   fun ia => im ia. *)

Fixpoint issue_map_fix
  (A A' : Type) (AR : Param10.Rel A A')
  (B B' : Type) (BR : Param10.Rel B B')
  (C C' : Type) (CR : Param10.Rel C C')
  (ia : issue A B C) : issue A' B' C' :=
    match ia with
    | K1 _ _ _ u e p => K1 A' B' C' u e p
    | K2 _ _ _ a b c => K2 A' B' C' (map AR a) (map BR b) (map CR c)
    | K4 _ _ _ ia1 ia2 ia3 => K4 A' B' C'
                               (issue_map_fix A A' AR B B' BR C C' CR ia1)
                               (issue_map_fix A A' AR B B' BR C C' CR ia2)
                               (issue_map_fix A A' AR B B' BR C C' CR ia3) end.

(* Definition issue_map_fix2 : *)
(*   forall (A A' : Type) (AR : Param10.Rel A A') *)
(*   (B B' : Type) (BR : Param10.Rel B B') *)
(*   (C C' : Type) (CR : Param10.Rel C C') *)
(*   (ia : issue A B C), issue A' B' C' := *)
(*     let fix F A A' AR B B' BR C C' CR ia {struct ia} := *)
(*       match ia with *)
(*     | K1 _ _ _ u e p => K1 A' B' C' u e p *)
(*     | K2 _ _ _ a b c => K2 A' B' C' (map AR a) (map BR b) (map CR c) *)
(*     | K4 _ _ _ ia1 ia2 ia3 => K4 A' B' C' *)
(*                                (F A A' AR B B' BR C C' CR ia1) *)
(*                                (F A A' AR B B' BR C C' CR ia2) *)
(*                                (F A A' AR B B' BR C C' CR ia3) end in *)
(*     fun A A' AR B B' BR C C' CR ia => F A A' AR B B' BR C C' CR ia. *)
(* Definition issue_mapE *)
(*   (A A' : Type) (AR : Param10.Rel A A') *)
(*   (B B' : Type) (BR : Param10.Rel B B') *)
(*   (C C' : Type) (CR : Param10.Rel C C') *)
(*   ia : *)
(*   issue_map A A' AR *)
(*             B B' BR *)
(*             C C' CR *)
(*             ia = ((fix im (ia0 : issue A B C) : issue A' B' C' := *)
(*               match ia0 with *)
(*               | K1 _ _ _ u e p => K1 A' B' C' u e p *)
(*               | K2 _ _ _ a b c => K2 A' B' C' (map AR a) (map BR b) (map CR c) *)
(*               | K4 _ _ _ ia7 ia8 ia9 => K4 A' B' C' (im ia7) (im ia8) (im ia9) *)
(*               end) ia). *)
(* Proof. by []. Qed. *)

Definition issue_k1_proj1 : forall (A B C : Type) (u : unit), issue A B C -> unit :=
fun A B C u ia =>
  match ia with
  | K1 _ _ _ u _ _ => u
  | _ => u end.

Definition issue_k1_proj2 : forall (A B C: Type) (e : enum), issue A B C -> enum :=
fun A B C e ia =>
  match ia with
  | K1 _ _ _ _ e _ => e
  | _ => e end.

Definition issue_k1_proj3 : forall (A B C: Type) (p : pp), issue A B C -> pp :=
fun A B C p ia =>
  match ia with
  | K1 _ _ _ _ _ p => p
  | _ => p end.

Definition issue_k2_proj1 : forall (A B C : Type) (a : A), issue A B C -> A :=
fun A B C a ia =>
  match ia with
  | K2 _ _ _ a _ _ => a
  | _ => a end.

Definition issue_k2_proj2 : forall (A B C : Type) (b : B), issue A B C -> B :=
fun A B C b ia =>
  match ia with
  | K2 _ _ _ _ b _ => b
  | _ => b end.

Definition issue_k2_proj3 : forall (A B C : Type) (c : C), issue A B C -> C :=
fun A B C c ia =>
  match ia with
  | K2 _ _ _ _ _ c => c
  | _ => c end.

Definition issue_k4_proj1 : forall (A B C : Type) (ia : issue A B C), issue A B C -> issue A B C :=
fun A B C ia' ia =>
  match ia with
  | K4 _ _ _ ia' _ _ => ia'
  | _ => ia' end.

Definition issue_k4_proj2 : forall (A B C : Type) (ia : issue A B C), issue A B C -> issue A B C :=
fun A B C ia' ia =>
  match ia with
  | K4 _ _ _ _ ia' _ => ia'
  | _ => ia' end.

Definition issue_k4_proj3 : forall (A B C : Type) (ia : issue A B C), issue A B C -> issue A B C :=
fun A B C ia' ia =>
  match ia with
  | K4 _ _ _ _ _ ia' => ia'
  | _ => ia' end.

Definition issue_k1_inj1 : forall (A B C : Type) (u1 u2 : unit) (e1 e2 : enum) (p1 p2 : pp), K1 A B C u1 e1 p1 = K1 A B C u2 e2 p2 -> u1 = u2.
  move=> A B C u1 u2 e1 e2 p1 p2 E.
  injection E.
  Show Proof.
  move=> P1 P2 P3; exact: P3.
  Show Proof.
  Defined.
  (* fun A B C u1 u2 e1 e2 p1 p2 E => ap (issue_k1_proj1 A B C u1) E. *)

Definition issue_k1_inj2 : forall (A B C : Type) (u1 u2 : unit) (e1 e2 : enum) (p1 p2 : pp), K1 A B C u1 e1 p1 = K1 A B C u2 e2 p2 -> e1 = e2 :=
  fun A B C u1 u2 e1 e2 p1 p2 E => ap (issue_k1_proj2 A B C e1) E.

Definition issue_k1_inj3 : forall (A B C : Type) (u1 u2 : unit) (e1 e2 : enum) (p1 p2 : pp), K1 A B C u1 e1 p1 = K1 A B C u2 e2 p2 -> p1 = p2 :=
  fun A B C u1 u2 e1 e2 p1 p2 E => ap (issue_k1_proj3 A B C p1) E.

Definition issue_k2_inj1 : forall (A B C : Type) (a1 a2 : A) (b1 b2 : B) (c1 c2 : C), K2 A B C a1 b1 c1= K2 A B C a2 b2 c2 -> a1 = a2 :=
  fun A B C a1 a2 b1 b2 c1 c2 E => ap (issue_k2_proj1 A B C a1) E.

Definition issue_k2_inj2 : forall (A B C : Type) (a1 a2 : A) (b1 b2 : B) (c1 c2 : C), K2 A B C a1 b1 c1= K2 A B C a2 b2 c2 -> b1 = b2 :=
  fun A B C a1 a2 b1 b2 c1 c2 E => ap (issue_k2_proj2 A B C b1) E.

Definition issue_k2_inj3 : forall (A B C : Type) (a1 a2 : A) (b1 b2 : B) (c1 c2 : C), K2 A B C a1 b1 c1= K2 A B C a2 b2 c2 -> c1 = c2 :=
  fun A B C a1 a2 b1 b2 c1 c2 E => ap (issue_k2_proj3 A B C c1) E.

Definition issue_k4_inj1 : forall (A B C : Type) (ia1 ia2 : issue A B C) (ia3 ia4 : issue A B C) (ia5 ia6 : issue A B C), K4 A B C ia1 ia3 ia5 = K4 A B C ia2 ia4 ia6 -> ia1 = ia2 :=
  fun A B C ia1 ia2 ia3 ia4 ia5 ia6 E => ap (issue_k4_proj1 A B C ia1) E.

Definition issue_k4_inj2 : forall (A B C : Type) (ia1 ia2 : issue A B C) (ia3 ia4 : issue A B C) (ia5 ia6 : issue A B C), K4 A B C ia1 ia3 ia5 = K4 A B C ia2 ia4 ia6 -> ia3 = ia4 :=
  fun A B C ia1 ia2 ia3 ia4 ia5 ia6 E => ap (issue_k4_proj2 A B C ia3) E.

Definition issue_k4_inj3 : forall (A B C : Type) (ia1 ia2 : issue A B C) (ia3 ia4 : issue A B C) (ia5 ia6 : issue A B C), K4 A B C ia1 ia3 ia5 = K4 A B C ia2 ia4 ia6 -> ia5 = ia6 :=
  fun A B C ia1 ia2 ia3 ia4 ia5 ia6 E => ap (issue_k4_proj3 A B C ia5) E.

Definition issue_ex_falso_k1_k2 : forall (A B C A' : Type) u1 e1 p1 a2 b2 c2,
    K1 A B C u1 e1 p1 = K2 A B C a2 b2 c2 -> A' :=
  fun A B C A' u1 e1 p1 a2 b2 c2 e =>
    match e in _ = t return
          match t with
          | K2 _ _ _ _ _ _ => A'
          | _ => Unit end
    with eq_refl => tt end.

Definition issue_ex_falso_k1_k4 : forall (A B C A' : Type) u1 e1 p1 ia2 ia4 ia6 , K1 A B C u1 e1 p1 = K4 A B C ia2 ia4 ia6 -> A' :=
  fun A B C A' u1 e1 p1 ia2 ia4 ia6 e =>
    match e in _ = t return
          match t with
          | K4 _ _ _ _ _ _ => A'
          | _ => Unit end
    with eq_refl => tt end.

Definition issue_ex_falso_k2_k1 : forall (A B C A' : Type) a1 b1 c1 u2 e2 p2, K2 A B C a1 b1 c1 = K1 A B C u2 e2 p2 -> A' :=
  fun A B C A' a1 b1 c1 u1 e1 p1 e =>
    match e in _ = t return
          match t with
          | K1 _ _ _ _ _ _ => A'
          | _ => Unit end
    with eq_refl => tt end.

Definition issue_ex_falso_k2_k4 : forall (A B C A' : Type) a1 b1 c1 ia2 ia4 ia6 , K2 A B C a1 b1 c1 = K4 A B C ia2 ia4 ia6 -> A' :=
  fun A B C A' a1 b1 c1 ia2 ia4 ia6 e =>
    match e in _ = t return
          match t with
          | K4 _ _ _ _ _ _ => A'
          | _ => Unit end
    with eq_refl => tt end.

Definition issue_ex_falso_k4_k1 : forall (A B C A' : Type) ia1 ia3 ia5 u2 e2 p2 , K4 A B C ia1 ia3 ia5 = K1 A B C u2 e2 p2 -> A' :=
  fun A B C A' ia1 ia3 ia5 u1 e1 p1 e =>
    match e in _ = t return
          match t with
          | K1 _ _ _ _ _ _ => A'
          | _ => Unit end
    with eq_refl => tt end.

Definition issue_ex_falso_k4_k2 : forall (A B C A' : Type) ia1 ia3 ia5 a2 b2 c2 , K4 A B C ia1 ia3 ia5 = K2 A B C a2 b2 c2 -> A' :=
  fun A B C A' ia1 ia3 ia5 a2 b2 c2 e =>
    match e in _ = t return
          match t with
          | K2 _ _ _ _ _ _ => A'
          | _ => Unit end
    with eq_refl => tt end.

Fixpoint issue_mR
  (A A' : Type) (AR : Param2a0.Rel A A')
  (B B' : Type) (BR : Param2a0.Rel B B')
  (C C' : Type) (CR : Param2a0.Rel C C')

  ia {struct ia} : forall ia', issue_map_fix A A' AR B B' BR C C' CR ia = ia' -> issueR A A' AR B B' BR C C' CR ia ia'.
Proof.
  (* fix F 1. *)
  case: ia => [u1 e1 p1 | a1 b1 c1 | ia1 ia3 ia5 ]; case=> [u2 e2 p2 | a2 b2 c2 | ia2 ia4 ia6] e.
  (* Set Printing All. *)
  (* rewrite /= in e. *)
  + by apply (K1R _ _ _ _ _ _ _ _ _
                _ _ (mR_Unit _ _ (issue_k1_inj1 _ _ _ _ _ _ _ _ _ e))
                _ _ (mR_enum _ _ (issue_k1_inj2 _ _ _ _ _ _ _ _ _ e))
                _ _ (mR_pp _ _ (issue_k1_inj3 _ _ _ _ _ _ _ _ _ e))).
  + by apply (issue_ex_falso_k1_k2 A' B' C' _ u1 e1 p1 a2 b2 c2).
  + by apply (issue_ex_falso_k1_k4 A' B' C' _ u1 e1 p1 ia2 ia4 ia6).

  + by apply (issue_ex_falso_k2_k1 A' B' C' _ (map AR a1) (map BR b1) (map CR c1) u2 e2 p2).
  +
    (* simpl [issue_map]in e. *)
    by apply (K2R _ _ _ _ _ _ _ _ _

                _ _ (map_in_R AR _ _ (issue_k2_inj1 _ _ _ _ _ _ _ _ _ e))
                _ _ (map_in_R BR _ _ (issue_k2_inj2 _ _ _ _ _ _ _ _ _ e))
                _ _ (map_in_R CR _ _ (issue_k2_inj3 _ _ _ _ _ _ _ _ _ e))).
  + by apply (issue_ex_falso_k2_k4 A' B' C' _(map AR a1) (map BR b1) (map CR c1) ia2 ia4 ia6).

  + by apply (issue_ex_falso_k4_k1 A' B' C' _
                (issue_map_fix A A' AR B B' BR C C' CR ia1)
                (issue_map_fix A A' AR B B' BR C C' CR ia3)
                (issue_map_fix A A' AR B B' BR C C' CR ia5) u2 e2 p2).
  + by apply (issue_ex_falso_k4_k2 A' B' C' _
                (issue_map_fix A A' AR B B' BR C C' CR ia1)
                (issue_map_fix A A' AR B B' BR C C' CR ia3)
                (issue_map_fix A A' AR B B' BR C C' CR ia5) a2 b2 c2).
  + by apply (K4R _ _ _ _ _ _ _ _ _
             _ _ (issue_mR _ _ AR _ _ BR _ _ CR ia1 ia2 (issue_k4_inj1 _ _ _ _ _ _ _ _ _ e))
             _ _ (issue_mR _ _ AR _ _ BR _ _ CR ia3 ia4 (issue_k4_inj2 _ _ _ _ _ _ _ _ _ e))
             _ _ (issue_mR _ _ AR _ _ BR _ _ CR ia5 ia6 (issue_k4_inj3 _ _ _ _ _ _ _ _ _ e))).
Defined.

Fixpoint issue_Rm
  (A A' : Type) (AR : Param2b0.Rel A A')
  (B B' : Type) (BR : Param2b0.Rel B B')
  (C C' : Type) (CR : Param2b0.Rel C C')
   ia ia' (iaR : issueR A A' AR B B' BR C C' CR ia ia') {struct iaR}: issue_map_fix A A' AR B B' BR C C' CR ia = ia'.
Proof.
  (* move: iaR. *)
  (* Set Printing All. *)
  (* rewrite /=. *)
  (* move=> iaR; *)
  (* elim: iaR. *)
  (* move: ia. *)
  (* refine (fun ia ia' => _). *)
  elim: iaR=> [u1 u2 uR e1 e2 eR p1 p2 pR | a1 a2 aR b1 b2 bR c1 c2 cR | ia1 ia2 iaR1 iaRm1 ia3 ia4 iaR2 iaRm2 ia5 ia6 iaR3 iaRm3 ].
  +
    rewrite /=.
    (* have E' := (ap (fun x => K1 A' B' C' x e1 p1) (Rm_Unit u1 u2 uR)). *)
    (* have E'' := (ap (fun x => K1 A' B' C' u2 x p1) (Rm_enum e1 e2 eR)). *)
    (* have E''' := (ap (fun x => K1 A' B' C' u2 e2 x) (Rm_pp p1 p2 pR)). *)
    (* exact: (E' @ E'' @ E'''). *)
    exact: ((ap (fun x => K1 A' B' C' x e1 p1) (Rm_Unit u1 u2 uR))@
     (ap (fun x => K1 A' B' C' u2 x p1) (Rm_enum e1 e2 eR))@
     (ap (fun x => K1 A' B' C' u2 e2 x) (Rm_pp p1 p2 pR))).
  +
    (* rewrite /=. *)
    (* have E' := (ap (fun x => K2 A' B' C' x (map BR b1) (map CR c1)) (R_in_map AR a1 a2 aR)). *)
    (* have E'' := (ap (fun x => K2 A' B' C' a2 x (map CR c1)) (R_in_map BR b1 b2 bR)). *)
    (* have E''' := (ap (fun x => K2 A' B' C' a2 b2 x) (R_in_map CR c1 c2 cR)). *)
    (* exact: (E' @ E'' @ E'''). *)
    exact ((ap (fun x => K2 A' B' C' x (map BR b1) (map CR c1)) (R_in_map AR a1 a2 aR)) @
     (ap (fun x => K2 A' B' C' a2 x (map CR c1)) (R_in_map BR b1 b2 bR)) @
     (ap (fun x => K2 A' B' C' a2 b2 x) (R_in_map CR c1 c2 cR))).

    (* rewrite /=. *)
    (* have /= E' := (ap (fun x => K4 A' B' C' x (issue_map A A' AR B B' BR C C' CR ia3) (issue_map A A' AR B B' BR C C' CR ia5)) (F _ _ iaR1)). *)
    (* have /= E'' := (ap (fun x => K4 A' B' C' ia2 x (issue_map A A' AR B B' BR C C' CR ia5)) (F _ _ iaR2)). *)
    (* have /= E''' := (ap (fun x => K4 A' B' C' ia2 ia4 x) (F _ _ iaR3)). *)
  + exact ((ap (fun x => K4 A' B' C' x (issue_map_fix A A' AR B B' BR C C' CR ia3) (issue_map_fix A A' AR B B' BR C C' CR ia5)) (issue_Rm A A' AR B B' BR C C' CR _ _ iaR1)) @
             (ap (fun x => K4 A' B' C' ia2 x (issue_map_fix A A' AR B B' BR C C' CR ia5)) (issue_Rm A A' AR B B' BR C C' CR _ _ iaR2)) @
             (ap (fun x => K4 A' B' C' ia2 ia4 x) (issue_Rm A A' AR B B' BR C C' CR _ _ iaR3))).
 Defined.

(* Lemma HH A' B' C' u1 u2 e1 e2 p1 p2 E E' : *)
(*   (issue_k1_inj1 A' B' C' u1 u2 e1 e2 p1 p2 *)
(*      ((ap (fun x : Unit => K1 A' B' C' x e1 p1) E @ *)
(*          E'))) = E. *)
(* Proof. *)
(*   move: u1 u2 E E'. *)
(*   refine (fun u1 u2 E => match E as p0 in _ = t return *)
(*                forall E', issue_k1_inj1 A' B' C' u1 t e1 e2 p1 p2 (ap (fun x : Unit => K1 A' B' C' x e1 p1) p0 @ E') = p0 *)
(*                       with eq_refl => _ end *)
(*          ). *)
(*   refine( fun E' => match E' as p0 in _ = t return *)
(*                        issue_k1_inj1 A' B' C' u1 u1 e1 e1 p1 p1 (ap (fun x : Unit => K1 A' B' C' x e1 p1) 1 @ p0) = 1 *)
(*           with eq_refl => _ end *)
(*         ). *)
(*   rewrite /issue_k1_inj1. *)
(*   (* rewrite /issue_k1_proj1. *) *)
(*   rewrite ap_pp. *)
(*   (* rewrite -ap_compose /= ap_idmap. *) *)
(*   (* (* move: E; elim: u1. elim: u2. *) *) *)

Definition issue_k1_inj1K : forall A' B' C' u1 u2 (p1 : u1 = u2) e1 e2 (p2 : e1 = e2) pp1 pp2 (p3 : pp1 = pp2),
    issue_k1_inj1 A' B' C' u1 u2 e1 e2 pp1 pp2
      ((ap (fun x : Unit => K1 A' B' C' x e1 pp1) p1 @
          ap (fun x : enum => K1 A' B' C' u2 x pp1) p2) @
         ap (fun x : pp => K1 A' B' C' u2 e2 x) p3) = p1 .
Proof.
  move=> A' B' C'.
  refine (fun u1 u2 p1 => match p1 as p0 in _ = t return
                             forall (e1 e2 : enum) (p2 : e1 = e2) (pp1 pp2 : pp) (p3 : pp1 = pp2),
                               issue_k1_inj1 A' B' C' u1 t e1 e2 pp1 pp2
                                 ((ap (fun x : Unit => K1 A' B' C' x e1 pp1) p0 @ ap (fun x : enum => K1 A' B' C' t x pp1) p2) @
                                    ap (fun x : pp => K1 A' B' C' t e2 x) p3) = p0
                       with eq_refl => _ end
         ).
  refine (fun e1 e2 p2 => match p2 as p0 in _ = t return
                             forall (pp1 pp2 : pp) (p3 : pp1 = pp2),
                               issue_k1_inj1 A' B' C' u1 u1 e1 t pp1 pp2
                                 ((ap (fun x : Unit => K1 A' B' C' x e1 pp1) 1
                                      @ ap (fun x : enum => K1 A' B' C' u1 x pp1) p0) @
                                    ap (fun x : pp => K1 A' B' C' u1 t x) p3) = 1
                       with eq_refl => _ end
         ).
  refine (fun pp1 pp2 p3 => match p3 as p0 in _ = t return
                               issue_k1_inj1 A' B' C' u1 u1 e1 e1 pp1 t
                                 ((ap (fun x : Unit => K1 A' B' C' x e1 pp1) 1
                                      @ ap (fun x : enum => K1 A' B' C' u1 x pp1) 1) @
                                    ap (fun x : pp => K1 A' B' C' u1 e1 x) p0) = 1
                       with eq_refl => eq_refl end
       ).
Defined.

Definition issue_k1_inj2K : forall A' B' C' u1 u2 (p1 : u1 = u2) e1 e2 (p2 : e1 = e2) pp1 pp2 (p3 : pp1 = pp2),
       (issue_k1_inj2 A' B' C' u1 u2 e1 e2 pp1 pp2
          ((ap (fun x : Unit => K1 A' B' C' x e1 pp1) p1 @
            ap (fun x : enum => K1 A' B' C' u2 x pp1) p2) @
           ap (fun x : pp => K1 A' B' C' u2 e2 x) p3)) = p2.
Proof.
move=> A' B' C'.
refine (fun u1 u2 p1 => match p1 as p0 in _ = t
       return
  forall (e1 e2 : enum) (p2 : e1 = e2)
    (pp1 pp2 : pp) (p3 : pp1 = pp2),
  issue_k1_inj2 A' B' C' u1 t e1 e2 pp1 pp2
    ((ap (fun x : Unit => K1 A' B' C' x e1 pp1) p0 @ ap (fun x : enum => K1 A' B' C' t x pp1) p2) @
     ap (fun x : pp => K1 A' B' C' t e2 x) p3) = p2
                                                with eq_refl => _ end
       ).
refine (fun e1 e2 p2 => match p2 as p0 in _ = t
       return
  forall (pp1 pp2 : pp) (p3 : pp1 = pp2),
  issue_k1_inj2 A' B' C' u1 u1 e1 t pp1 pp2
    ((ap (fun x : Unit => K1 A' B' C' x e1 pp1) 1 @ ap (fun x : enum => K1 A' B' C' u1 x pp1) p0) @
     ap (fun x : pp => K1 A' B' C' u1 t x) p3) = p0
                                                with eq_refl => _ end
       ).
refine (fun pp1 pp2 p3 => match p3 as p0 in _ = t
       return
         issue_k1_inj2 A' B' C' u1 u1 e1 e1 pp1 t
           ((ap (fun x : Unit => K1 A' B' C' x e1 pp1) 1 @ ap (fun x : enum => K1 A' B' C' u1 x pp1) 1) @
              ap (fun x : pp => K1 A' B' C' u1 e1 x) p0) = 1
                                                with eq_refl => eq_refl end
       ).
Defined.

Definition issue_k1_inj3K : forall A' B' C' u1 u2 (p1 : u1 = u2) e1 e2 (p2 : e1 = e2) pp1 pp2 (p3 : pp1 = pp2),
   (issue_k1_inj3 A' B' C' u1 u2 e1 e2 pp1 pp2
          ((ap (fun x : Unit => K1 A' B' C' x e1 pp1) p1 @
            ap (fun x : enum => K1 A' B' C' u2 x pp1) p2) @
             ap (fun x : pp => K1 A' B' C' u2 e2 x) p3)) = p3.
Proof.
  move=> A' B' C'.
  refine (
      fun u1 u2 p1 => match p1 as p0 in _ = t return
                         forall e1 e2 p2 pp1 pp2 p3,
  (issue_k1_inj3 A' B' C' u1 t e1 e2 pp1 pp2
          ((ap (fun x : Unit => K1 A' B' C' x e1 pp1) p0 @
            ap (fun x : enum => K1 A' B' C' t x pp1) p2) @
           ap (fun x : pp => K1 A' B' C' t e2 x) p3)) = p3
                   with eq_refl => _ end ).
  refine (
      fun e1 e2 p2 => match p2 as p0 in _ = t return
                         forall pp1 pp2 p3,
  (issue_k1_inj3 A' B' C' u1 u1 e1 t pp1 pp2
          ((ap (fun x : Unit => K1 A' B' C' x e1 pp1) 1 @
            ap (fun x : enum => K1 A' B' C' u1 x pp1) p0) @
           ap (fun x : pp => K1 A' B' C' u1 t x) p3)) = p3
                   with eq_refl => _ end ).
  refine (
      fun pp1 pp2 p3 => match p3 as p0 in _ = t return
  (issue_k1_inj3 A' B' C' u1 u1 e1 e1 pp1 t
          ((ap (fun x : Unit => K1 A' B' C' x e1 pp1) 1 @
            ap (fun x : enum => K1 A' B' C' u1 x pp1) 1) @
           ap (fun x : pp => K1 A' B' C' u1 e1 x) p0)) = p0
  with eq_refl => eq_refl end ).
  Defined.

Definition issue_k2_inj1K :
  forall A' B' C'
    a1 a2 (p1 : a1 = a2) b1 b2 (p2 : b1 = b2) c1 c2 (p3 : c1 = c2),
    (issue_k2_inj1 A' B' C' a1 a2 b1 b2 c1 c2
       ((ap (fun x : A' => K2 A' B' C' x b1 c1) p1 @
           ap (fun x : B' => K2 A' B' C' a2 x c1) p2) @
          ap (fun x : C' => K2 A' B' C' a2 b2 x) p3)) = p1 .
Proof.
move=> A' B' C'.
refine (fun a1 a2 p1 => match p1 as p0 in _ = t return
forall (b1 b2 : B') (p2 : b1 = b2) (c1 c2 : C') (p3 : c1 = c2),
  issue_k2_inj1 A' B' C' a1 t b1 b2 c1 c2
    ((ap (fun x : A' => K2 A' B' C' x b1 c1) p0 @ ap (fun x : B' => K2 A' B' C' t x c1) p2) @
       ap (fun x : C' => K2 A' B' C' t b2 x) p3) = p0
                     with eq_refl => _ end).
refine (fun b1 b2 p2 => match p2 as p0 in _ = t return
forall (c1 c2 : C') (p3 : c1 = c2),
  issue_k2_inj1 A' B' C' a1 a1 b1 t c1 c2
    ((ap (fun x : A' => K2 A' B' C' x b1 c1) 1 @ ap (fun x : B' => K2 A' B' C' a1 x c1) p0) @
       ap (fun x : C' => K2 A' B' C' a1 t x) p3) = 1
                     with eq_refl => _ end).
refine (fun c1 c2 p3 => match p3 as p0 in _ = t return
  issue_k2_inj1 A' B' C' a1 a1 b1 b1 c1 t
    ((ap (fun x : A' => K2 A' B' C' x b1 c1) 1 @ ap (fun x : B' => K2 A' B' C' a1 x c1) 1) @
       ap (fun x : C' => K2 A' B' C' a1 b1 x) p0) = 1
                                                   with eq_refl => eq_refl end).
Defined.


Definition issue_k2_inj2K :
  forall A' B' C'
    a1 a2 (p1 : a1 = a2) b1 b2 (p2 : b1 = b2) c1 c2 (p3 : c1 = c2),
    (issue_k2_inj2 A' B' C' (a1) a2 (b1) b2 (c1) c2
       ((ap (fun x : A' => K2 A' B' C' x (b1) (c1)) p1 @
           ap (fun x : B' => K2 A' B' C' a2 x (c1)) p2) @
          ap (fun x : C' => K2 A' B' C' a2 b2 x) p3)) = p2.
  move=> A' B' C'.
  refine (
      fun a1 a2 (p1 : a1 = a2)=> match p1 as p0 in _ = t return
                                           forall b1 b2 (p2 : b1 = b2) c1 c2 (p3 : c1 = c2),
(issue_k2_inj2 A' B' C' (a1) t (b1) b2 (c1) c2
         ((ap (fun x : A' => K2 A' B' C' x (b1) (c1)) p0 @
           ap (fun x : B' => K2 A' B' C' t x (c1)) p2) @
          ap (fun x : C' => K2 A' B' C' t b2 x) p3)) = p2
                                                      with eq_refl => _ end
    ).
  refine (
      fun b1 b2 (p2 : b1 = b2)=> match p2 as p0 in _ = t return
                                           forall c1 c2 (p3 : c1 = c2),
(issue_k2_inj2 A' B' C' (a1) (a1) (b1) t (c1) c2
         ((ap (fun x : A' => K2 A' B' C' x (b1) (c1)) 1 @
           ap (fun x : B' => K2 A' B' C' (a1) x (c1)) p0) @
          ap (fun x : C' => K2 A' B' C' (a1) t x) p3)) = p0
                                                      with eq_refl => _ end
    ).
  refine (
      fun c1 c2 (p3 : c1 = c2)=> match p3 as p0 in _ = t return
(issue_k2_inj2 A' B' C' (a1) (a1) (b1) (b1) (c1) t
         ((ap (fun x : A' => K2 A' B' C' x (b1) (c1)) 1 @
           ap (fun x : B' => K2 A' B' C' (a1) x (c1)) 1) @
          ap (fun x : C' => K2 A' B' C' (a1) (b1) x) p0)) = 1
                                                      with eq_refl => eq_refl end
  ).
Defined.

Definition issue_k2_inj3K :
  forall A' B' C' 
    a1 a2 (p1 : a1 = a2) b1 b2 (p2 : b1 = b2) c1 c2 (p3 : c1 = c2),
    (issue_k2_inj3 A' B' C' (a1) a2 (b1) b2 (c1) c2
       ((ap (fun x : A' => K2 A' B' C' x (b1) (c1)) p1 @
           ap (fun x : B' => K2 A' B' C' a2 x (c1)) p2) @
          ap (fun x : C' => K2 A' B' C' a2 b2 x) p3)) = p3.
  move=> A' B' C'.
  refine (
      fun a1 a2 (p1 : a1 = a2)=> match p1 as p0 in _ = t return
                                           forall b1 b2 (p2 : b1 = b2) c1 c2 (p3 : c1 = c2),
(issue_k2_inj3 A' B' C' (a1) t (b1) b2 (c1) c2
         ((ap (fun x : A' => K2 A' B' C' x (b1) (c1)) p0 @
           ap (fun x : B' => K2 A' B' C' t x (c1)) p2) @
          ap (fun x : C' => K2 A' B' C' t b2 x) p3)) = p3
                                                      with eq_refl => _ end
    ).
  refine (
      fun b1 b2 (p2 : b1 = b2)=> match p2 as p0 in _ = t return
                                           forall c1 c2 (p3 : c1 = c2),
(issue_k2_inj3 A' B' C' (a1) (a1) (b1) t (c1) c2
         ((ap (fun x : A' => K2 A' B' C' x (b1) (c1)) 1 @
           ap (fun x : B' => K2 A' B' C' (a1) x (c1)) p0) @
          ap (fun x : C' => K2 A' B' C' (a1) t x) p3)) = p3
                                                      with eq_refl => _ end
    ).
  refine (
      fun c1 c2 (p3 : c1 = c2)=> match p3 as p0 in _ = t return
(issue_k2_inj3 A' B' C' (a1) (a1) (b1) (b1) (c1) t
         ((ap (fun x : A' => K2 A' B' C' x (b1) (c1)) 1 @
           ap (fun x : B' => K2 A' B' C' (a1) x (c1)) 1) @
          ap (fun x : C' => K2 A' B' C' (a1) (b1) x) p0)) = p0
                                                      with eq_refl => eq_refl end
  ).
  Defined.

Definition issue_k4_inj1K :
  forall A' B' C',
  forall ia1 ia2 (p1 :  ia1 = ia2) ia3 ia4 (p2 :  ia3 = ia4) ia5 ia6 (p3 :  ia5 = ia6),
    (issue_k4_inj1 A' B' C' ( ia1) ia2 ( ia3) ia4 ( ia5) ia6
      ((ap
          (fun x : issue A' B' C' =>
              K4 A' B' C' x (ia3) (ia5))
          p1 @
          ap (fun x : issue A' B' C' => K4 A' B' C' ia2 x (ia5))
          p2) @
         ap (fun x : issue A' B' C' => K4 A' B' C' ia2 ia4 x) p3)) = p1.
Proof.
  move=> A' B' C'.
  refine (fun ia1 ia2 p1 => match p1 as p0 in _ = t return
                               forall ia3 ia4 (p2 :  ia3 = ia4) ia5 ia6 (p3 :  ia5 = ia6),
                               (issue_k4_inj1 A' B' C' ( ia1) t ( ia3) ia4 ( ia5) ia6
      ((ap
          (fun x : issue A' B' C' =>
              K4 A' B' C' x (ia3) (ia5))
          p0 @
          ap (fun x : issue A' B' C' => K4 A' B' C' t x (ia5))
          p2) @
          ap (fun x : issue A' B' C' => K4 A' B' C' t ia4 x) p3)) = p0
                               with eq_refl => _ end
         ).
  refine (fun ia3 ia4 p2 => match p2 as p0 in _ = t return
                               forall ia5 ia6 (p3 :  ia5 = ia6),
                               (issue_k4_inj1 A' B' C' ( ia1) ( ia1) ( ia3) t ( ia5) ia6
      ((ap
          (fun x : issue A' B' C' =>
              K4 A' B' C' x (ia3) (ia5))
          1 @
          ap (fun x : issue A' B' C' => K4 A' B' C' ( ia1) x (ia5))
          p0) @
          ap (fun x : issue A' B' C' => K4 A' B' C' ( ia1) t x) p3)) = 1
                               with eq_refl => _ end
         ).
  refine (fun ia5 ia6 p3 => match p3 as p0 in _ = t return
                               (issue_k4_inj1 A' B' C' ( ia1) ( ia1) ( ia3) ( ia3) ( ia5) t
      ((ap
          (fun x : issue A' B' C' =>
              K4 A' B' C' x (ia3) (ia5))
          1 @
          ap (fun x : issue A' B' C' => K4 A' B' C' (ia1) x (ia5))
          1) @
          ap (fun x : issue A' B' C' => K4 A' B' C' ( ia1) ( ia3) x) p0)) = 1
                               with eq_refl => eq_refl end
       ).
Defined.

Definition issue_k4_inj2K : forall A' B' C',
                              forall ia1 ia2 (p1 : ia1 = ia2) ia3 ia4 (p2 : ia3 = ia4) ia5 ia6 (p3 : ia5 = ia6),
    (issue_k4_inj2 A' B' C' (ia1) ia2 (ia3) ia4 (ia5) ia6
      ((ap
          (fun x : issue A' B' C' =>
              K4 A' B' C' x (ia3) (ia5))
          p1 @
          ap (fun x : issue A' B' C' => K4 A' B' C' ia2 x (ia5))
          p2) @
         ap (fun x : issue A' B' C' => K4 A' B' C' ia2 ia4 x) p3)) = p2.
Proof.
  move=> A' B' C'.
  refine (fun ia1 ia2 p1 => match p1 as p0 in _ = t return
                               forall ia3 ia4 (p2 : ia3 = ia4) ia5 ia6 (p3 : ia5 = ia6),
                               (issue_k4_inj2 A' B' C' (ia1) t (ia3) ia4 (ia5) ia6
      ((ap
          (fun x : issue A' B' C' =>
              K4 A' B' C' x (ia3) (ia5))
          p0 @
          ap (fun x : issue A' B' C' => K4 A' B' C' t x (ia5))
          p2) @
          ap (fun x : issue A' B' C' => K4 A' B' C' t ia4 x) p3)) = p2
                               with eq_refl => _ end
         ).
  refine (fun ia3 ia4 p2 => match p2 as p0 in _ = t return
                               forall ia5 ia6 (p3 : ia5 = ia6),
                               (issue_k4_inj2 A' B' C' (ia1) (ia1) (ia3) t (ia5) ia6
      ((ap
          (fun x : issue A' B' C' =>
              K4 A' B' C' x (ia3) (ia5))
          1 @
          ap (fun x : issue A' B' C' => K4 A' B' C' (ia1) x (ia5))
          p0) @
          ap (fun x : issue A' B' C' => K4 A' B' C' (ia1) t x) p3)) = p0
                               with eq_refl => _ end
         ).
  refine (fun ia5 ia6 p3 => match p3 as p0 in _ = t return
                               (issue_k4_inj2 A' B' C' (ia1) (ia1) (ia3) (ia3) (ia5) t
      ((ap
          (fun x : issue A' B' C' =>
              K4 A' B' C' x (ia3) (ia5))
          1 @
          ap (fun x : issue A' B' C' => K4 A' B' C' (ia1) x (ia5))
          1) @
          ap (fun x : issue A' B' C' => K4 A' B' C' (ia1) (ia3) x) p0)) = 1
                               with eq_refl => eq_refl end
       ).
Defined.

Definition issue_k4_inj3K : forall A' B' C',
  forall ia1 ia2 (p1 : ia1 = ia2) ia3 ia4 (p2 : ia3 = ia4) ia5 ia6 (p3 : ia5 = ia6),
    (issue_k4_inj3 A' B' C' (ia1) ia2 (ia3) ia4 (ia5) ia6
      ((ap
          (fun x : issue A' B' C' =>
              K4 A' B' C' x (ia3) (ia5))
          p1 @
          ap (fun x : issue A' B' C' => K4 A' B' C' ia2 x (ia5))
          p2) @
         ap (fun x : issue A' B' C' => K4 A' B' C' ia2 ia4 x) p3)) = p3.
Proof.
  move=> A' B' C'.
  refine (fun ia1 ia2 p1 => match p1 as p0 in _ = t return
                               forall ia3 ia4 (p2 : ia3 = ia4) ia5 ia6 (p3 : ia5 = ia6),
                               (issue_k4_inj3 A' B' C' (ia1) t (ia3) ia4 (ia5) ia6
      ((ap
          (fun x : issue A' B' C' =>
              K4 A' B' C' x (ia3) (ia5))
          p0 @
          ap (fun x : issue A' B' C' => K4 A' B' C' t x (ia5))
          p2) @
          ap (fun x : issue A' B' C' => K4 A' B' C' t ia4 x) p3)) = p3
                               with eq_refl => _ end
         ).
  refine (fun ia3 ia4 p2 => match p2 as p0 in _ = t return
                               forall ia5 ia6 (p3 : ia5 = ia6),
                               (issue_k4_inj3 A' B' C' (ia1) (ia1) (ia3) t (ia5) ia6
      ((ap
          (fun x : issue A' B' C' =>
              K4 A' B' C' x (ia3) (ia5))
          1 @
          ap (fun x : issue A' B' C' => K4 A' B' C' (ia1) x (ia5))
          p0) @
          ap (fun x : issue A' B' C' => K4 A' B' C' (ia1) t x) p3)) = p3
                               with eq_refl => _ end
         ).
  refine (fun ia5 ia6 p3 => match p3 as p0 in _ = t return
                               (issue_k4_inj3 A' B' C' (ia1) (ia1) (ia3) (ia3) (ia5) t
      ((ap
          (fun x : issue A' B' C' =>
              K4 A' B' C' x (ia3) (ia5))
          1 @
          ap (fun x : issue A' B' C' => K4 A' B' C' (ia1) x (ia5))
          1) @
          ap (fun x : issue A' B' C' => K4 A' B' C' (ia1) (ia3) x) p0)) = p0
                               with eq_refl => eq_refl end
       ).
  Defined.

Definition mRRmKIssue
  (A A' : Type) (AR : Param40.Rel A A')
  (B B' : Type) (BR : Param40.Rel B B')
  (C C' : Type) (CR : Param40.Rel C C')
  : forall ia ia' (iaR : issueR A A' AR B B' BR C C' CR ia ia'),
    issue_mR A A' AR B B' BR C C' CR _ _ (issue_Rm A A' AR B B' BR C C' CR _ _ iaR) = iaR.
Proof.
  move=> ia ia'.
  elim=> [u1 u2 uR e1 e2 eR p1 p2 pR /= | a1 a2 aR b1 b2 bR c1 c2 cR /= | ia1 ia2 iaR1 IH1 ia3 ia4 iaR2 IH2 ia5 ia6 iaR3 IH3 /=].
  + rewrite issue_k1_inj1K issue_k1_inj2K issue_k1_inj3K.
    by rewrite mRRmK_Unit mRRmKEnum mRRmK_pp.
  + rewrite issue_k2_inj1K issue_k2_inj2K issue_k2_inj3K.
    by rewrite !R_in_mapK.
  + rewrite issue_k4_inj1K issue_k4_inj2K issue_k4_inj3K.
    by rewrite IH1 IH2 IH3.
  Qed.
Inductive enum3R : enum3 -> enum3 -> Type :=
| KK1R : forall (u1 u2 : unit), UnitR u1 u2
         -> forall (u3 u4 : unit), UnitR u3 u4
         -> enum3R (KK1 u1 u3) (KK1 u2 u4)
| KK2R : forall (b1 b2 : bool), BoolR b1 b2
  -> forall (b3 b4 : bool), BoolR b3 b4
  -> enum3R (KK2 b1 b3) (KK2 b2 b4).

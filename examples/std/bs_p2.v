From Stdlib Require Import ssreflect.
Local Open Scope nat_scope.

Set Universe Polymorphism.

Inductive PList (A : Type) : Type :=
    | PNil  : PList A
    | PCons : A -> PList A -> PList A.
Arguments PNil  {A}.     (* Infer A rather than requiring it to be supplied
                            explicitly. Without it we would have to write
                            [@PNil nat] or [@PCons nat 1 l]. *)
Arguments PCons {A} _ _. (* When writing [PCons h t], Rocq deduces A from
                            the type of h; the two underscores _ indicate
                            that the element and tail remain explicit. *)
Notation "x :p: l" := (PCons x l) (at level 60, right associativity).
Notation "{{}}"    := PNil.

Fixpoint plength {A : Type} (l : PList A) : nat :=
    match l with
    | @PNil _     => O
    | @PCons _ _ t  => S (plength t)
    end.

Fixpoint papp {A : Type} (l1 l2 : PList A) : PList A :=
    match l1 with
    | @PNil _       => l2
    | @PCons _ h t  => @PCons _ h (papp t l2)
    end.

Example plength_ex : plength (1 :p: 2 :p: 3 :p: {{}}) = 3.
Proof. simpl. reflexivity. Qed.

Example papp_ex : papp (true :p: {{}}) (false :p: false :p: {{}}) 
                        = (true :p: false :p: false :p: {{}}).
Proof. simpl. reflexivity. Qed.

Theorem plength_papp :
    forall {A : Type} (l1 l2 : PList A),
    plength (papp l1 l2) = plength l1 + plength l2.
Proof.
    intros A l1 l2.
    induction l1 as [| h t IH].
    - (* Base case: l1 = NNil. *)
      simpl. reflexivity.
    - (* Inductive step: l1 = NCons h t. *)
      simpl. rewrite IH. reflexivity.
Qed.

(** EXPL B — Comparing the proofs: differences and similarities

    nlength_napp                             plength_papp
    ─────────────────────                    ─────────────────────────
    intros l1 l2.                            intros A l1 l2.
    induction l1 as ...                      induction l1 as ...
    - simpl. reflexivity.                    - simpl. reflexivity.
    - simpl. rewrite IH.                     - simpl. rewrite IH.
      reflexivity.                             reflexivity.

    The only structural difference is "intros A".
    
    Why? The property depends only on HOW the list is built (no elements /
    one element prepended), not on the TYPE of the elements. The type appears
    only in the definition, not in the proof.

    - Practical consequence: "plength_papp" is strictly more general than
      "nlength_napp". Instantiating A := nat gives exactly the same statement.

    - Problem: "NatList ≠ PList nat", they are distinct types, so we cannot
      apply "plength_papp" directly to a "NatList". We need a "bridge" between
      the two types.      
*)
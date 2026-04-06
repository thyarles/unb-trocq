From Stdlib Require Import ssreflect.
Require Import Trocq_examples.bs_p1.
Require Import Trocq_examples.bs_p2.
Local Open Scope nat_scope.

Set Universe Polymorphism.

(*  Show how to "transfer" nlength_napp to PList nat by hand, explicitly
    building the conversion functions and the compatibility lemmas.
    I think this is what Trocq automates.

    The plan:

        1. Define plist_to_natlist : PList nat → NatList
        2. Define natlist_to_plist : NatList → PList nat
        3. Prove they are inverses (isomorphism)
        4. Prove they preserve length and append
        5. Use these bridges to derive plength_papp_via_natlist from nlength_napp
        6. Notes
*)

(*  ── 1 & 2: Conversion functions ──────────────────────────────────-── *)

Fixpoint plist_to_natlist (l : PList nat) : NatList :=
    match l with
    | @PNil _      => NNil
    | @PCons _ h t => NCons h (plist_to_natlist t)
    end.

Fixpoint natlist_to_plist (l : NatList) : PList nat :=
    match l with
    | NNil      => @PNil nat
    | NCons h t => @PCons nat h (natlist_to_plist t)
    end.

(* Show the conversion bridge at work: both sides pass through NatList. *)
Goal nlength (plist_to_natlist (1 :p: 2 :p: 3 :p: {{}})) = 3. reflexivity.
Goal plist_to_natlist (papp (1 :p: {{}}) (2 :p: {{}})) = 1 :n: 2 :n: [[]]. reflexivity.
Goal plist_to_natlist (1 :p: 2 :p: {{}}) = (1 :n: 2 :n: [[]]). reflexivity.
Goal natlist_to_plist (1 :n: 2 :n: [[]]) = (1 :p: 2 :p: {{}}). reflexivity.

(*  ── 3: Isomorphism ────────────────────────────────────────────────── *)

(** Round trip (to NatList and back): natlist_to_plist ∘ plist_to_natlist = id *)
Lemma plist_natlist_iso : forall (l : PList nat),
    natlist_to_plist (plist_to_natlist l) = l.
Proof.
    induction l as [| h t IH]; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
Qed.

(** Round trip (to PList and back): plist_to_natlist ∘ natlist_to_plist = id *)
Lemma natlist_plist_iso : forall (l : NatList),
    plist_to_natlist (natlist_to_plist l) = l.
Proof.
    induction l as [| h t IH]; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
Qed.

(*  ── 4: Compatibility with length and app ──────────────────────────── *)

(* The conversion preserves the length. *)
Lemma plength_eq_nlength : forall (l : PList nat),
    nlength (plist_to_natlist l) = plength l.
Proof.
    induction l as [| h t IH].
    - simpl. reflexivity.
    - simpl. rewrite IH. reflexivity.
Qed.

(** The conversion distributes over concatenation. *)
Lemma plist_to_natlist_app : forall (l1 l2 : PList nat),
    plist_to_natlist (papp l1 l2) =
    napp (plist_to_natlist l1) (plist_to_natlist l2).
Proof.
    intros l1 l2.
    induction l1 as [| h t IH]; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
Qed.

(*  ── 5: Manual transfer ────────────────────────────────────────────── *)

Theorem plength_papp_via_natlist : forall (l1 l2 : PList nat),
    plength (papp l1 l2) = plength l1 + plength l2.
Proof.
    (*** Step 0: Introduces the variables. *)
    intros l1 l2.
    (*** Step 1: rewrite the left-hand side using plength_eq_nlength. *)
    rewrite <- (plength_eq_nlength (papp l1 l2)).
    (*** Step 2: distribute the conversion over papp. *)
    rewrite plist_to_natlist_app.
    (*** Step 3: apply the monomorphic theorem *)
    rewrite nlength_napp.
    (*** Step 4: convert the remaining nlength back to plength. *)
    rewrite plength_eq_nlength.
    rewrite plength_eq_nlength.
    reflexivity.
Qed.

Goal plength (papp (1 :p: 2 :p: {{}}) (3 :p: {{}})) =
     plength (1 :p: 2 :p: {{}}) + plength (3 :p: {{}}).
     (* The proof actually uses the transferred theorem as its justification:
        the specific lists are witnesses to the universal statement ∀ l1 l2,
        plength (papp l1 l2) = plength l1 + plength l2. *)
    apply plength_papp_via_natlist.

Goal plength (papp ({{}} : PList nat) (1 :p: 2 :p: {{}})) =
     plength ({{}} : PList nat) + plength (1 :p: 2 :p: {{}}).
     apply plength_papp_via_natlist.

Goal plength (papp (1 :p: 2 :p: {{}}) ({{}} : PList nat)) =
     plength (1 :p: 2 :p: {{}}) + plength ({{}} : PList nat).
     apply plength_papp_via_natlist.

(*  ── 7: Notes ───────────────────────────────────────────────────────── *)

(** EXPL D — Notes about manual transfer *)

    (*  To perform the transfer "by hand" we used:
        + 2 conversion functions
        + 2 isomorphism proofs
        + 2 compatibility lemmas (length and app)
        + 1 "glue" proof (plength_papp_via_natlist)
        -----------------------------------------
        = 7 items in total to transfer 1 theorem.

        Hypothetically, with Trocq:
        - We register the relation ONCE:
            + Trocq Use R_NatList_PList
            + Trocq Use R_NNil_PNil
            + Trocq Use R_NCons_PCons
        - Then, for each new theorem:
            = trocq. apply nlength_napp.   ← Done!

        Trocq automatically builds the compatibility lemmas and the
        glue proof, using the registered structure. *)
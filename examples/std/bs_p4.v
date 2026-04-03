From Stdlib Require Import ssreflect.
Require Import Trocq_examples.bs_p1.
Require Import Trocq_examples.bs_p2.
Require Import Trocq_examples.bs_p3.
Local Open Scope nat_scope.

Set Universe Polymorphism.

(*  Show how to "transfer" length_papp to NatList by hand, explicitly
    building the conversion functions and the compatibility lemmas.
    I think this is what Trocq automates.

    The plan:

        1. Define natlist_to_plist : NatList → PList nat
        2. Define plist_to_natlist : PList nat → NatList
        3. Prove they are inverses (isomorphism)
        4. Prove they preserve length and append
        5. Use these bridges to derive nlength_napp from plength_papp 
        6. Notes
*)

(*  ── 1 & 2: Conversion functions ──────────────────────────────────-── *)

Fixpoint natlist_to_plist (l : NatList) : PList nat :=
    match l with
    | NNil      => @PNil nat
    | NCons h t => @PCons nat h (natlist_to_plist t)
    end.

Fixpoint plist_to_natlist (l : PList nat) : NatList :=
    match l with
    | @PNil _      => NNil
    | @PCons _ h t => NCons h (plist_to_natlist t)
    end.

(* Show the conversion bridge at work: both sides pass through PList nat. *)
Compute plength (natlist_to_plist (1 :n: 2 :n: 3 :n: [[]])).
Compute natlist_to_plist (napp (1 :n: 2 :n: [[]]) (3 :n: [[]])).
Compute natlist_to_plist (1 :n: 2 :n: 3 :n: [[]]) = (1 :p: 2 :p: 3 :p: {{}}).
Compute plist_to_natlist (1 :p: 2 :p: 3 :p: {{}}) = (1 :n: 2 :n: 3 :n: [[]]).

(*  ── 3: Isomorphism ────────────────────────────────────────────────── *)

    (** Round trip (to PList and back): plist_to_natlist ∘ natlist_to_plist = id *)
    Lemma natlist_plist_iso :
        forall (l : NatList),
        plist_to_natlist (natlist_to_plist l) = l.
    Proof.
        induction l as [| h t IH].
        - simpl. reflexivity.
        - simpl. rewrite IH. reflexivity.
    Defined.

    (** Round trip (to NatList and back): natlist_to_plist ∘ plist_to_natlist = id *)
    Lemma plist_natlist_iso :
        forall (l : PList nat),
        natlist_to_plist (plist_to_natlist l) = l.
    Proof.
        induction l as [| h t IH].
        - simpl. reflexivity.
        - simpl. rewrite IH. reflexivity.
    Defined.

(*  ── 4: Compatibility with length and app ──────────────────────────── *)

    (* The conversion preserves the length. *)
    Lemma nlength_eq_plength :
        forall (l : NatList),
        plength (natlist_to_plist l) = nlength l.
    Proof.
        induction l as [| h t IH].
        - simpl. reflexivity.
        - simpl. rewrite IH. reflexivity.
    Defined.

    (** The conversion distributes over concatenation. *)
    Lemma natlist_to_plist_app :
        forall (l1 l2 : NatList),
        natlist_to_plist (napp l1 l2) =
        papp (natlist_to_plist l1) (natlist_to_plist l2).
    Proof.
        intros l1 l2.
        induction l1 as [| h t IH].
        - simpl. reflexivity.
        - simpl. rewrite IH. reflexivity.
    Defined.

(*  ── 5: Manual transfer ────────────────────────────────────────────── *)

    Theorem nlength_napp_via_plist :
        forall (l1 l2 : NatList),
        nlength (napp l1 l2) = nlength l1 + nlength l2.
    Proof.
        (*** Step 0: Introduces the variables. *)
        intros l1 l2.
        (*** Step 1: rewrite the left-hand side using nlength_eq_plength. *)
        rewrite <- (nlength_eq_plength (napp l1 l2)).
        (*** Step 2: distribute the conversion over napp. *)
        rewrite natlist_to_plist_app.
        (*** Step 3: apply the polymorphic theorem *)
        rewrite plength_papp.
        (*** Step 4: convert the remaining plength back to nlength. *)
        rewrite nlength_eq_plength.
        rewrite nlength_eq_plength.
        reflexivity.
    Defined.

    Example test_transfer_normal :
        nlength (napp (1 :n: 2 :n: [[]]) (3 :n: [[]])) =
        nlength (1 :n: 2 :n: [[]]) + nlength (3 :n: [[]]).
    Proof. 
        (* The proof actually uses the transferred theorem as its justification:
           the specific lists are witnesses to the universal statement ∀ l1 l2,
           nlength (napp l1 l2) = nlength l1 + nlength l2. *)
        apply nlength_napp_via_plist.
    Qed.

    Example test_transfer_empty_l :
        nlength (napp [[]] (1 :n: 2 :n: [[]])) =
        nlength [[]] + nlength (1 :n: 2 :n: [[]]).
    Proof. apply nlength_napp_via_plist. Qed.

    Example test_transfer_empty_r :
        nlength (napp (1 :n: 2 :n: [[]]) [[]]) =
        nlength (1 :n: 2 :n: [[]]) + nlength [[]].
    Proof. apply nlength_napp_via_plist. Qed. 

(*  ── 7: Notes ───────────────────────────────────────────────────────── *)

(** EXPL D — Notes about manual transfer *)

    (*  To perform the transfer "by hand" we used:
        + 2 conversion functions
        + 2 isomorphism proofs
        + 2 compatibility lemmas (length and app)
        + 1 "glue" proof (nlength_napp_via_plist)
        -----------------------------------------
        = 7 items in total to transfer 1 theorem.

        Hypothetically, with Trocq:
        - We register the relation ONCE:
            + Trocq Use R_NatList_PList
            + Trocq Use R_NNil_PNil
            + Trocq Use R_NCons_PCons
        - Then, for each new theorem:
            = trocq. exact plength_papp.   ← Done!

        Trocq automatically builds the compatibility lemmas and the
        glue proof, using the registered structure. *)
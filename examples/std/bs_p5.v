From Stdlib Require Import ssreflect.
Local Open Scope nat_scope.
From Trocq Require Import Trocq.
From Trocq Require Import Param_nat.

Set Universe Polymorphism.

(*  ── NatList definitions (source – theorem to transfer) ────────────── *)

Require Import Trocq_examples.bs_p1.

(*  ── PList nat definitions (target – type to prove) ────────────────── *)

Require Import Trocq_examples.bs_p2.

(* Monomorphic aliases for PList nat avoids Trocq confusing the implicit
   sort argument with a list variable. *)
Definition NPNatList   : Type                                := PList nat.
Definition npPNil      : NPNatList                           := @PNil nat.
Definition npPCons     : nat -> NPNatList -> NPNatList       := @PCons nat.
Definition npnlength   : NPNatList -> nat                    := @plength nat.
Definition npnapp      : NPNatList -> NPNatList -> NPNatList := @papp nat.

(*  ── Conversion functions ──────────────────────────────────────────── *)

Fixpoint plist_to_natlist (l : NPNatList) : NatList :=
    match l with
    | @PNil _      => NNil
    | @PCons _ h t => NCons h (plist_to_natlist t)
    end.

Fixpoint natlist_to_plist (l : NatList) : NPNatList :=
    match l with
    | NNil      => npPNil
    | NCons h t => npPCons h (natlist_to_plist t)
    end.

(*  ── Bridge lemmas  ────────────────────────────────────────────────── *)

Lemma npnlength_eq_nlength :
    forall (l : NPNatList),
    npnlength l = nlength (plist_to_natlist l).
Proof.
    unfold npnlength.
    induction l; simpl.
    - reflexivity.
    - rewrite IHl. reflexivity.
Defined.

Lemma plist_to_natlist_app :
    forall (l1 l2 : NPNatList),
    plist_to_natlist (npnapp l1 l2) =
    napp (plist_to_natlist l1) (plist_to_natlist l2).
Proof.
    unfold npnapp.
    intros l1 l2.
    induction l1; simpl.
    - reflexivity.
    - rewrite IHl1. reflexivity.
Defined.

(*  ── Mutual inverses ───────────────────────────────────────────────── *)

Lemma plist_natlist_iso :
    forall (l : NPNatList),
    natlist_to_plist (plist_to_natlist l) = l.
Proof.
    induction l; simpl.
    - unfold npPNil. reflexivity.
    - rewrite IHl. unfold npPCons. reflexivity.
Defined.

Lemma natlist_plist_iso :
    forall (l : NatList),
    plist_to_natlist (natlist_to_plist l) = l.
Proof.
    induction l; simpl.
    - reflexivity.
    - rewrite IHl. reflexivity.
Defined.

(*  ── Relation between the types ────────────────────────────────────── *)

Definition R_NatList : Param44.Rel NPNatList NatList.
Proof.
    apply Iso.toParam; unshelve econstructor.
    - apply plist_to_natlist.   (* map   : NPNatList → NatList    *)
    - apply natlist_to_plist.   (* comap : NatList   → NPNatList  *)
    - apply plist_natlist_iso.  (* mapK  : comap ∘ map = id       *)
    - apply natlist_plist_iso.  (* comapK: map ∘ comap = id       *)
Defined.

(*  ── Relation between the functions ────────────────────────────────── *)

Definition R_npnlength
    (l : NPNatList)
    (l': NatList)
    (lR: rel R_NatList l l'): natR (npnlength l) (nlength l') :=
    map_in_R_nat
        (eq_trans (npnlength_eq_nlength l) (ap nlength lR)).

Definition R_npnapp
    (l1 : NPNatList) (l1' : NatList) (l1R : rel R_NatList l1 l1')
    (l2 : NPNatList) (l2' : NatList) (l2R : rel R_NatList l2 l2') :
    rel R_NatList (npnapp l1 l2) (napp l1' l2') :=
    eq_trans
        (plist_to_natlist_app l1 l2)
        (eq_trans
            (ap (fun x => napp x (plist_to_natlist l2)) l1R)
            (ap (napp l1') l2R)).

(*  ── Register in Trocq's database ──────────────────────────────────── *)

Trocq Use R_NatList.        (* relation between the types *)
Trocq Use R_npnlength.      (* relation between the functions *)
Trocq Use R_npnapp.         (* relation between the functions *)

Trocq Use Param44_nat.      (* from Trocq *)
Trocq Use Param_add.        (* from Trocq *)

(*  ── The theorem via Trocq ─────────────────────────────────────────── *)
Theorem npnlength_npnapp_trocq : forall (l1 l2 : NPNatList),
    npnlength (npnapp l1 l2) = npnlength l1 + npnlength l2.
Proof.
    trocq.
    apply nlength_napp.
Qed.

Print Assumptions npnlength_npnapp_trocq.

(** EXPL D — Notes about Trocq *)

(* Trocq works with a database of "parametric relations".

    To use the trocq tactic we need:

    (a) The relation between the TYPES
        NatList ~ PList nat
    (b) The relation between the CONSTRUCTORS
        NNil ~ PNil  and  NCons ~ PCons
    (c) The relation between the FUNCTIONS
        nlength ~ plength  and  napp ~ papp
    (d) Register everything with Trocq Use
    (e) The main theorem via trocq
*)
                                                                            
(*  ── Step (a): Relation between the types ──────────────────────────── *)

    (* Trocq uses "parametric relations" instead of simple bijections. The
    strongest class is Param44 (full isomorphism, with proofs in both
    directions and coherence).

    We reuse the functions and proofs from PART 5. We just pack them into
    an Iso.type and convert with Iso.toParam.

    Iso.type A B = { map : A → B; comap : B → A;
                        mapK : comap ∘ map = id; comapK : map ∘ comap = id }

    (turns the isomorphism into the strongest possible parametric relation)
    Iso.toParam f : Param44.Rel A B 

    We use apply "Iso.toParam; unshelve econstructor" to build the isomorphism
    and the relation in a single step (standard Trocq project pattern). *)

    (* Two problems arise when using universe-polymorphic functions like
        [papp], [plength], [PNil], [PCons] directly with Trocq:

        1. [PList : Type → Type] as the sort causes a universe error.

        2. Trocq confuses the implicit [{A : Type}] argument with the
            translated list variable, generating [papp l1'] where l1' is
            passed as the type A instead of as the first list argument.

        Fix: define monomorphic aliases specialised to [nat] so that
        Trocq sees functions whose types contain no implicit sort argument.
    *)

    (* Note: "rel R_NatList l l'" is definitionally equal to "natlist_to_plist l = l'".
                Every relational proof reduces to an equality over the conversion function,
                which greatly simplifies the reasoning. *)

(*  ── Step (b): Relation between the constructors ───────────────────── *)

    (* For each constructor we prove that it "respects" the relation R_NatList.
        Even if the constructors do not appear directly in the theorem we want to
        prove, registering them lets Trocq reason about the TYPE NatList in general
        (e.g. in induction instances). *)

    (* [NNil ~ nPNil]: natlist_to_plist NNil = nPNil (true by definition). *)

    (* [NCons ~ PCons]: given h ~ h' (diagonal relation on nat, [natR h h'])
        and l ~ l' (list relation), we have [NCons h l ~ PCons h' l'].

        "Why [natR h h'] rather than just [h = h']"? Trocq uses natR
        (from Param_nat) as the official relation for nat.
        It is equivalent to = but is what the database recognises.

        [R_in_map_nat hR : h = h'] extracts the equality from the natR relation. *)

(*  ── Step (c): Relation between the functions ──────────────────────── *)

    (* For each function appearing in the target theorem we supply a term
        of type: ∀ related inputs -> related outputs. 
        
        This is the parametric counterpart of "function preserves the relation". 

        [nlength ~ plength]:
        Given l ~ l' (i.e., natlist_to_plist l = l'), prove
        [natR (nlength l) (plength l')].

        Why natR and not =?
        Trocq expects the registered relation for nat, which is natR
        (equivalent to = via map_in_R_nat and R_in_map_nat).

        Chain of equalities used:
        nlength l
            = plength (natlist_to_plist l)   (by nlength_eq_plength)^
            = plength l'                     (ap plength lR) *)

    (* [napp ~ papp]:
        Given l1 ~ l1' and l2 ~ l2', prove
        [rel R_NatList (napp l1 l2) (papp l1' l2')].

        Chain used:
            natlist_to_plist (napp l1 l2)
            = papp (natlist_to_plist l1) (natlist_to_plist l2)  [natlist_to_plist_app]
            = papp l1'                   (natlist_to_plist l2)  [ap ... l1R]
            = papp l1'                   l2'                    [ap ... l2R] *)

(*  ── Step (d): Register in Trocq's database ────────────────────────── *)

    (* Suggested order:
    
    type → constructors → helper functions → domain functions → equality.

    Trocq automatically generates weaker versions (smaller classes) of
    each registered relation — so it suffices to register the strongest
    one (Param44). *)

(*  ── Step (e): The theorem via Trocq ───────────────────────────────── *)

    (* The proof now has TWO lines:
    
    1. trocq: transforms the goal from NatList to PList nat
    2. exact plength_papp: closes it with the already-proved theorem

    Trocq internally performs all the work we did by hand in PART 4
    (building the bridge, invoking nlength_eq_plength,
    natlist_to_plist_app, etc.) fully automatically. *)

    (* Print Assumptions nlength_napp_trocq shows the axioms assumed by the proof.
        Univalence is not needed here because the relation between NatList and
        PList nat is an isomorphism, not merely a type equivalence. *)

(*  ── Step (f): Take notes ───────────────────────────────── *)

    (* Registration (done ONCE for the pair NatList/PList nat):
        R_NatList   — target type
        R_NNil      — base constructor
        R_NCons     — recursive constructor
        R_nlength   — length function
        R_napp      — append function
        Param44_nat, Param_add, Param01_paths — arithmetic/=

        Cost: ~8 registrations + ~5 definitions.

        Gain: for ANY new theorem about NatList using nlength and napp,
        the proof is: trocq. exact <theorem_for_PList>.

        Comparison with the manual approach (PART 4):
        - Manual: 7 intermediate lemmas + 1 glue proof → repeated for EACH new theorem
        - Trocq : one-time registration + 2 lines per new theorem *)
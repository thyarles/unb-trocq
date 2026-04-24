From Stdlib Require Import ssreflect.
Local Open Scope nat_scope.
From Trocq Require Import Trocq.
From Trocq Require Import Param_nat.

Set Universe Polymorphism.

(*  ── NatList definitions (source – theorem to transfer) ────────────────── *)

Require Import Trocq_examples.bs_p1.

(*  ── PList nat definitions (target – type to prove) ────────────────────── *)

Require Import Trocq_examples.bs_p2.

(* Monomorphic aliases for PList nat avoids Trocq confusing the implicit
   sort argument with a list variable. *)
Definition _PList   : Type                       := PList nat.
Definition _PNil    : _PList                     := @PNil nat.
Definition _PCons   : nat -> _PList -> _PList    := @PCons nat.
Definition _plength : _PList -> nat              := @plength nat.
Definition _papp    : _PList -> _PList -> _PList := @papp nat.

(*  ── Relation between the constructors ─────────────────────────────────── *)

Fixpoint plist_2_nlist (l : _PList) : NatList :=
    match l with
    | @PNil _      => NNil
    | @PCons _ h t => NCons h (plist_2_nlist t)
    end.

Fixpoint nlist_2_plist (l : NatList) : _PList :=
    match l with
    | NNil      => _PNil
    | NCons h t => _PCons h (nlist_2_plist t)
    end.

(*  ── Bridge lemmas  ────────────────────────────────────────────────────── *)

Lemma _plength_eq_nlength :
    forall (l : _PList),
        _plength l = nlength (plist_2_nlist l).
Proof.
    unfold _plength.
    induction l; simpl.
    - reflexivity.
    - rewrite IHl. reflexivity.
Defined.

Lemma plist_2_nlist_app :
    forall (l1 l2 : _PList), plist_2_nlist (_papp l1 l2) =
        napp (plist_2_nlist l1) (plist_2_nlist l2).
Proof.
    unfold _papp.
    intros l1 l2.
    induction l1; simpl.
    - reflexivity.
    - rewrite IHl1. reflexivity.
Defined.

(*  ── Mutual inverses ───────────────────────────────────────────────────── *)

Lemma plist_nlist_iso :
    forall (l : _PList),
        nlist_2_plist (plist_2_nlist l) = l.
Proof.
    induction l; simpl.
    - unfold _PNil. reflexivity.
    - rewrite IHl. unfold _PCons. reflexivity.
Defined.

Lemma nlist_plist_iso :
    forall (l : NatList),
        plist_2_nlist (nlist_2_plist l) = l.
Proof.
    induction l; simpl.
    - reflexivity.
    - rewrite IHl. reflexivity.
Defined.

(*  ── Relation between the types ────────────────────────────────────────── *)

Definition R_NatList : Param44.Rel _PList NatList.
Proof.
    apply Iso.toParam; unshelve econstructor.
    - apply plist_2_nlist.    (* map   : _PList  → NatList *)
    - apply nlist_2_plist.    (* comap : NatList → _PList  *)
    - apply plist_nlist_iso.  (* mapK  : comap ∘ map = id  *)
    - apply nlist_plist_iso.  (* comapK: map ∘ comap = id  *)
Defined.

(*  ── Relation between the functions ────────────────────────────────────── *)

(** Notes:
    [rel R l l']  => l and l' are related; unfolds to [map R l = l']
                     (i.e., the isomorphism's forward map applied to l equals l')
    natR n m      => Trocq's parametric relation for nat, essentially n = m
    eq_trans p q  => Chains a = b and b = c into a = c
    ap f p        => Lifts equality a = b through a function (f a = f b)
    map_in_R_nat  => Converts a plain = on nat into a natR witness
*)

(* Definition R__plength
    (** In plain English:
        If a _PList (l) and a NatList (l') are related,
        then their lengths are related nats. *)
    (l : _PList) (l' : NatList) (lR : rel R_NatList l l') :
    (* rel R_NatList l l' === plist_2_nlist l = l' *)
    natR (_plength l) (nlength l') :=
    map_in_R_nat
        (eq_trans (_plength_eq_nlength l) (ap nlength lR)). *)

Lemma R__plength
    (l : _PList) (l' : NatList) (lR : rel R_NatList l l') :
    natR (_plength l) (nlength l').
Proof.
    change (plist_2_nlist l = l') in lR.
    (* normalize lR's type *)
    apply map_in_R_nat.
    (* reduce to: _plength l = nlength l' *)
    rewrite _plength_eq_nlength.
    (* goal: nlength (plist_2_nlist l) = nlength l' *)
    rewrite lR.
    (* goal: nlength l' = nlength l' *)        
    reflexivity.
Defined.

(* Definition R__papp
    (** In plain English:
        If (l1 ~ l1') and (l2 ~ l2') are two pairs of related lists,
        then their appended lists are also related. *)
    (l1 : _PList) (l1' : NatList) (l1R : rel R_NatList l1 l1')
    (* l1R : plist_2_nlist l1 = l1' *)
    (l2 : _PList) (l2' : NatList) (l2R : rel R_NatList l2 l2') :
    (* l2R : plist_2_nlist l2 = l2' *)
    rel R_NatList (_papp l1 l2) (napp l1' l2') :=
    (* goal: plist_2_nlist (_papp l1 l2) = napp l1' l2' *)
    eq_trans
        (plist_2_nlist_app l1 l2)
        (* step 1: plist_2_nlist (_papp l1 l2)
                 = napp (plist_2_nlist l1) (plist_2_nlist l2)      *)
        (eq_trans
            (ap (fun x => napp x (plist_2_nlist l2)) l1R)
            (* step 2: napp (plist_2_nlist l1) (plist_2_nlist l2)
                     = napp l1'                   (plist_2_nlist l2)  *)
            (ap (napp l1') l2R)).
            (* step 3: napp l1' (plist_2_nlist l2)
                     = napp l1' l2'                                      *) *)

Lemma R__papp
    (l1 : _PList) (l1' : NatList) (l1R : rel R_NatList l1 l1')
    (l2 : _PList) (l2' : NatList) (l2R : rel R_NatList l2 l2') :
    rel R_NatList (_papp l1 l2) (napp l1' l2').
Proof.
    change (plist_2_nlist l1 = l1') in l1R. 
    (* normalize hypotheses *)
    change (plist_2_nlist l2 = l2') in l2R.
    (* normalize hypotheses *)
    change (plist_2_nlist (_papp l1 l2) = napp l1' l2').
    (* normalize goal *)
    rewrite plist_2_nlist_app.
    (* unfold the append conversion *)
    rewrite l1R.
    (* substitute plist_2_nlist l1 → l1' *)
    rewrite l2R.
    (* substitute plist_2_nlist l2 → l2' *)
    reflexivity.
Defined.

(*  ── Register in Trocq's database ──────────────────────────────────────── *)

Trocq Use R_NatList.    (* relation between the types *)
Trocq Use R__plength.   (* relation between the functions *)
Trocq Use R__papp.      (* relation between the functions *)

Trocq Use Param44_nat.  (* from Trocq *)
Trocq Use Param_add.    (* from Trocq *)

(*  ── The theorem via Trocq ─────────────────────────────────────────────── *)
Theorem _plength_papp : forall (l1 l2 : _PList),
    _plength (_papp l1 l2) = _plength l1 + _plength l2.
Proof.
    trocq.
    apply nlength_napp.
Qed.

Print Assumptions _plength_papp.

Theorem _plength_papp_comm : forall (l1 l2 : _PList),
    _plength (_papp l1 l2) = _plength l2 + _plength l1.
Proof.
    trocq.
    apply napp_length_comm.
Qed.

Print Assumptions _plength_papp_comm.

Theorem _papp_assoc : forall (l1 l2 l3 : _PList),
    _papp (_papp l1 l2) l3 = _papp l1 (_papp l2 l3).
Proof.
    trocq.
    apply napp_assoc.
Qed.

Print Assumptions _papp_assoc.

(** EXPL D — Notes about Trocq *)

(* Trocq works with a database of "parametric relations".

    To use the trocq tactic we need:

    (a) The relation between the CONSTRUCTORS
        NNil ~ PNil  and  NCons ~ PCons
    (b) The relation between the TYPES
        NatList ~ PList nat
    (c) The relation between the FUNCTIONS
        nlength ~ plength  and  napp ~ papp
    (d) Register everything with Trocq Use
    (e) The main theorem via trocq
*)
                                                                            
(*  ── Step (b): Relation between the types ──────────────────────────────── *)

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

    (* Note: "rel R_NatList l l'" is definitionally equal to "nlist_2_plist l = l'".
                Every relational proof reduces to an equality over the conversion function,
                which greatly simplifies the reasoning. *)

(*  ── Step (a): Relation between the constructors ───────────────────────── *)

    (* For each constructor we prove that it "respects" the relation R_NatList.
        Even if the constructors do not appear directly in the theorem we want to
        prove, registering them lets Trocq reason about the TYPE NatList in general
        (e.g. in induction instances). *)

    (* [NNil ~ nPNil]: nlist_2_plist NNil = nPNil (true by definition). *)

    (* [NCons ~ PCons]: given h ~ h' (diagonal relation on nat, [natR h h'])
        and l ~ l' (list relation), we have [NCons h l ~ PCons h' l'].

        "Why [natR h h'] rather than just [h = h']"? Trocq uses natR
        (from Param_nat) as the official relation for nat.
        It is equivalent to = but is what the database recognises.

        [R_in_map_nat hR : h = h'] extracts the equality from the natR relation. *)

(*  ── Step (c): Relation between the functions ──────────────────────────── *)

    (* For each function appearing in the target theorem we supply a term
        of type: ∀ related inputs -> related outputs. 
        
        This is the parametric counterpart of "function preserves the relation". 

        [nlength ~ plength]:
        Given l ~ l' (i.e., nlist_2_plist l = l'), prove
        [natR (nlength l) (plength l')].

        Why natR and not =?
        Trocq expects the registered relation for nat, which is natR
        (equivalent to = via map_in_R_nat and R_in_map_nat).

        Chain of equalities used:
        nlength l
            = plength (nlist_2_plist l)   (by nlength_eq_plength)^
            = plength l'                     (ap plength lR) *)

    (* [napp ~ papp]:
        Given l1 ~ l1' and l2 ~ l2', prove
        [rel R_NatList (napp l1 l2) (papp l1' l2')].

        Chain used:
            nlist_2_plist (napp l1 l2)
            = papp (nlist_2_plist l1) (nlist_2_plist l2)  [nlist_2_plist_app]
            = papp l1'                   (nlist_2_plist l2)  [ap ... l1R]
            = papp l1'                   l2'                    [ap ... l2R] *)

(*  ── Step (d): Register in Trocq's database ────────────────────────────── *)

    (* Suggested order:
    
    type → constructors → helper functions → domain functions → equality.

    Trocq automatically generates weaker versions (smaller classes) of
    each registered relation — so it suffices to register the strongest
    one (Param44). *)

(*  ── Step (e): The theorem via Trocq ───────────────────────────────────── *)

    (* The proof now has TWO lines:
    
    1. trocq: transforms the goal from NatList to PList nat
    2. exact plength_papp: closes it with the already-proved theorem

    Trocq internally performs all the work we did by hand in PART 4
    (building the bridge, invoking nlength_eq_plength,
    nlist_2_plist_app, etc.) fully automatically. *)

    (* Print Assumptions nlength_napp_trocq shows the axioms assumed by the proof.
        Univalence is not needed here because the relation between NatList and
        PList nat is an isomorphism, not merely a type equivalence. *)

(*  ── Step (f): Take notes ──────────────────────────────────────────────── *)

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
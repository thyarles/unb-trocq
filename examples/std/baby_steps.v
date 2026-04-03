(*****************************************************************************)
(*                  Tutorial: Lists, Parametricity, and Trocq                *)
(*                            — Step by Step —                               *)
(*                                                                           *)
(*  Goal: understand how type parametricity enables proof reuse, and how     *)
(*  Trocq can automate that reuse.                                           *)
(*                                                                           *)
(*  Overview:                                                                *)
(*    Expl A — Core concept: what is parametricity?                          *)
(*    Part 1 — Natural-number lists (monomorphic): length, append, theorem   *)
(*    Part 2 — Polymorphic lists: length, append, theorem                    *)
(*             Expl B — Comparing the proofs (tactic style)                  *)
(*    Part 3 — Proof objects: proofs as lambda terms                         *)
(*             Expl C — Comparing the proofs (lambda terms)                  *)
(*    Part 4 — Manual transfer                                               *)
(*             Expl D - Notes about manual transfer                          *)
(*    Part 5 — Using Trocq                                                   *)
(*    Part 6 — Applying Trocq to other types                                 *)
(*****************************************************************************)

From Coq Require Import ssreflect.
Local Open Scope nat_scope. (* 0, 1, 2, 3 are interpreted as natural numbers *)

(** Rocq does not allow a type to have itself as its type.  Instead, it uses a
    hidden universe hierarchy: Type@{0} has type Type@{1}, which has type
    Type@{2}, and so on. The next command tells to treat universe levels as 
    local variables, enabling more generic code. *)
Set Universe Polymorphism.

(** EXPL A — Core concept: what is parametricity?
    ---------------------------------------------------------------------------
    Imagine you need lists of naturals, lists of booleans, lists of strings...
    Without parametricity you would have to define a separate type for each one
    and rewrite all functions (length, append...) and all proofs from scratch.

    With parametric polymorphism you define the operations once for a generic
    type A, and every instance (nat, bool, string...) automatically inherits the
    proved properties.

    The fundamental idea:

      "Properties that depend only on the STRUCTURE of a list (and not on the
      TYPE of its elements) are automatically valid for any instance." 
*)

(** PART 1 — Natural-number lists (monomorphic): length, append, theorem *)
    Require Import Trocq_examples.bs_p1.

(** PART 2 — Polymorphic (parametric) lists *)
    Require Import Trocq_examples.bs_p2.

(** PART 3 — Proof objects: proofs as lambda terms *)
    Require Import Trocq_examples.bs_p3.
    
(** PART 4 — Manual transfer *)
    Require Import Trocq_examples.bs_p4.

(** PART 5 — Using Trocq *)

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

    From Trocq Require Import Trocq.
    From Trocq Require Import Param_nat. (* natR, Param44_nat, Param_add,
                                            map_in_R_nat, R_in_map_nat  *)
                                                                                
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
        Definition NPList   : Type                       := PList nat.
        Definition nPNil    : NPList                     := @PNil nat.
        Definition nPCons   : nat -> NPList -> NPList    := @PCons nat.
        Definition nplength : NPList -> nat              := @plength nat.
        Definition npapp    : NPList -> NPList -> NPList := @papp nat.
        Definition R_NatList: Param44.Rel NatList NPList.
        Proof.
          apply Iso.toParam; unshelve econstructor.
          - exact natlist_to_plist.    (* map   : NatList → PList nat *)
          - exact plist_to_natlist.    (* comap : PList nat → NatList *)
          - exact natlist_plist_iso.   (* mapK  : comap ∘ map = id *)
          - exact plist_natlist_iso.   (* comapK: map ∘ comap = id *)
        Defined.

        (* Note: "rel R_NatList l l'" is definitionally equal to "natlist_to_plist l = l'".
                 Every relational proof reduces to an equality over the conversion function,
                 which greatly simplifies the reasoning below. *)

    (*  ── Step (b): Relation between the constructors ───────────────────── *)

        (* For each constructor we prove that it "respects" the relation R_NatList.
           Even if the constructors do not appear directly in the theorem we want to
           prove, registering them lets Trocq reason about the TYPE NatList in general
           (e.g. in induction instances). *)

        (* [NNil ~ nPNil]: natlist_to_plist NNil = nPNil (true by definition). *)
        Definition R_NNil : rel R_NatList NNil nPNil := eq_refl.

        (* [NCons ~ PCons]: given h ~ h' (diagonal relation on nat, [natR h h'])
           and l ~ l' (list relation), we have [NCons h l ~ PCons h' l'].

           "Why [natR h h'] rather than just [h = h']"? Trocq uses natR
           (from Param_nat) as the official relation for nat.
           It is equivalent to = but is what the database recognises.

          [R_in_map_nat hR : h = h'] extracts the equality from the natR relation. *)
        Definition R_NCons
          (h h' : nat) (hR : natR h h')
          (l : NatList) (l' : NPList) (lR : rel R_NatList l l') :
          rel R_NatList (NCons h l) (nPCons h' l') :=
          (* natlist_to_plist (NCons h l) ≡ nPCons h (natlist_to_plist l) (by def.) *)
          (* ap (nPCons h) lR           : nPCons h (nat2p l) = nPCons h  l'         *)
          (* ap (nPCons · l') h_eq      : nPCons h l'        = nPCons h' l'         *)
          eq_trans (ap (nPCons h) lR) (ap (fun x => nPCons x l') (R_in_map_nat hR)).

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
        Definition R_nlength
          (l : NatList) (l' : NPList) (lR : rel R_NatList l l') :
          natR (nlength l) (nplength l') :=
          (* map_in_R_nat converts (n = n') → natR n n'                       *)
          (* nplength = @plength nat, so the goal is: nlength l = nplength l' *)
          map_in_R_nat (eq_trans (eq_sym (nlength_eq_plength l)) (ap nplength lR)).

        (* [napp ~ papp]:
           Given l1 ~ l1' and l2 ~ l2', prove
           [rel R_NatList (napp l1 l2) (papp l1' l2')].

           Chain used:
              natlist_to_plist (napp l1 l2)
                = papp (natlist_to_plist l1) (natlist_to_plist l2)  [natlist_to_plist_app]
                = papp l1'                   (natlist_to_plist l2)  [ap ... l1R]
                = papp l1'                   l2'                    [ap ... l2R] *)
        Definition R_napp
            (l1 : NatList) (l1' : NPList) (l1R : rel R_NatList l1 l1')
            (l2 : NatList) (l2' : NPList) (l2R : rel R_NatList l2 l2') :
            rel R_NatList (napp l1 l2) (npapp l1' l2') :=
          eq_trans
            (natlist_to_plist_app l1 l2)
            (eq_trans
              (ap (fun x => npapp x (natlist_to_plist l2)) l1R)
              (ap (npapp l1') l2R)).

    (*  ── Step (d): Register in Trocq's database ────────────────────────── *)

        (* Suggested order:
        
        type → constructors → helper functions → domain functions → equality.

        Trocq automatically generates weaker versions (smaller classes) of
        each registered relation — so it suffices to register the strongest
        one (Param44). *)

        (* Main type and the diagonal relation on nat (return type of nlength). *)
        Trocq Use R_NatList.
        Trocq Use Param44_nat.

        (* Constructors of NatList. R_NNil and R_NCons are needed for
           Trocq to recognise the TYPE NatList as fully specified. *)
        Trocq Use R_NNil.
        Trocq Use R_NCons.

        (* Functions on lists and addition of nat. *)
        Trocq Use R_nlength.
        Trocq Use R_napp.
        Trocq Use Param_add.

        (* Equality: Param01_paths transforms a = b : A into a' = b' : A'
          when A ~ A' and a ~ a', b ~ b'. It is needed because the goal
          contains an equality = between nat values. *)
        Trocq Use Param01_paths.

    (*  ── Step (e): The theorem via Trocq ───────────────────────────────── *)

        (* The proof now has TWO lines:
        
        1. trocq: transforms the goal from NatList to PList nat
        2. exact plength_papp: closes it with the already-proved theorem

        Trocq internally performs all the work we did by hand in PART 4
        (building the bridge, invoking nlength_eq_plength,
        natlist_to_plist_app, etc.) fully automatically. *)

        Theorem nlength_napp_trocq : forall (l1 l2 : NatList), 
          nlength (napp l1 l2) = nlength l1 + nlength l2.
        Proof.
          (* The trocq tactic automatically translates the NatList goal into 
             the PList nat goal using the relations provided *)
          trocq. 
          (* Goal: ∀(l1 l2: PList nat), plength(papp l1 l2) = plength l1 + plength l2 *)            
          apply plength_papp.
        Qed.        

        (* Print Assumptions nlength_napp_trocq shows the axioms assumed by the proof.
           Univalence is not needed here because the relation between NatList and
           PList nat is an isomorphism, not merely a type equivalence. *)
        Print Assumptions nlength_napp_trocq.

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

(** PART 6 — Applying Trocq to other types *)

    (* The same five-step pattern from Part 5 applies to any monomorphic type
       that is isomorphic to a PList specialisation. Here we do it for
       BolList ~ PList bool. *)

    (*  ── Base definitions ──────────────────────────────────────────────── *)

    Inductive BolList : Type :=
        | BNil  : BolList
        | BCons : bool -> BolList -> BolList.
    Notation "x :b: l" := (BCons x l) (at level 60, right associativity).
    Notation "[bb]"    := BNil.

    Fixpoint blength (l : BolList) : nat :=
        match l with
        | BNil       => O
        | BCons _ t  => S (blength t)
        end.

    Fixpoint bapp (l1 l2 : BolList) : BolList :=
        match l1 with
        | BNil       => l2
        | BCons h t  => BCons h (bapp t l2)
        end.

    (* Monomorphic aliases for PList bool — same reason as NPList in Part 5:
       avoids Trocq confusing the implicit sort argument with a list variable. *)
    Definition NBPList   : Type                          := PList bool.
    Definition nbPNil    : NBPList                       := @PNil bool.
    Definition nbPCons   : bool -> NBPList -> NBPList    := @PCons bool.
    Definition nbplength : NBPList -> nat                := @plength bool.
    Definition nbpapp    : NBPList -> NBPList -> NBPList := @papp bool.

    (*  ── Conversion functions ──────────────────────────────────────────── *)

    Fixpoint bollist_to_plist (l : BolList) : NBPList :=
      match l with
      | BNil      => @PNil bool
      | BCons h t => @PCons bool h (bollist_to_plist t)
      end.

    Fixpoint plist_to_bollist (l : NBPList) : BolList :=
      match l with
      | @PNil _      => BNil
      | @PCons _ h t => BCons h (plist_to_bollist t)
      end.

    (*  ── Bridge lemmas (analogues of nlength_eq_plength and
          natlist_to_plist_app from Part 4) ────────────────────────────── *)

    Lemma blength_eq_nbplength :
        forall (l : BolList),
        nbplength (bollist_to_plist l) = blength l.
    Proof.
        unfold nbplength.
        induction l; simpl.
        - reflexivity.
        - rewrite IHl. reflexivity.
    Defined.

    Lemma bollist_to_plist_app :
        forall (l1 l2 : BolList),
        bollist_to_plist (bapp l1 l2) =
        nbpapp (bollist_to_plist l1) (bollist_to_plist l2).
    Proof.
        unfold nbpapp.
        intros l1 l2.
        induction l1; simpl.
        - reflexivity.
        - rewrite IHl1. reflexivity.
    Defined.

    (*  ── Mutual inverses ───────────────────────────────────────────────── *)

    Lemma bollist_plist_iso :
        forall (l : BolList),
        plist_to_bollist (bollist_to_plist l) = l.
    Proof.
        induction l; simpl.
        - reflexivity.
        - rewrite IHl. reflexivity.
    Defined.

    Lemma plist_bollist_iso :
        forall (l : NBPList),
        bollist_to_plist (plist_to_bollist l) = l.
    Proof.
        induction l; simpl.
        - reflexivity.
        - rewrite IHl. reflexivity.
    Defined.

    (*  ── Step (a): Relation between the types ──────────────────────────── *)

    Definition R_BolList : Param44.Rel BolList NBPList.
    Proof.
        apply Iso.toParam; unshelve econstructor.
        - exact bollist_to_plist.   (* map   : BolList → NBPList *)
        - exact plist_to_bollist.   (* comap : NBPList → BolList *)
        - exact bollist_plist_iso.  (* mapK  : comap ∘ map = id  *)
        - exact plist_bollist_iso.  (* comapK: map ∘ comap = id  *)
    Defined.

    (* rel R_BolList l l' is definitionally equal to bollist_to_plist l = l'. *)

    (*  ── Step (b): Relation between the constructors ───────────────────── *)

    Definition R_BNil : rel R_BolList BNil nbPNil := eq_refl.

    (* [BCons ~ nbPCons]: given h ~ h' (BoolR h h') and l ~ l', conclude
       BCons h l ~ nbPCons h' l'.  Mirrors R_NCons from Part 5. *)
    Definition R_BCons
        (h h' : bool) (hR : BoolR h h')
        (l : BolList) (l' : NBPList) (lR : rel R_BolList l l') :
        rel R_BolList (BCons h l) (nbPCons h' l') :=
        eq_trans (ap (nbPCons h) lR) (ap (fun x => nbPCons x l') (R_in_map_Bool hR)).

    (*  ── Step (c): Relation between the functions ──────────────────────── *)

    (* [blength ~ nbplength]:
       Chain: blength l
                = nbplength (bollist_to_plist l)   (eq_sym blength_eq_nbplength)
                = nbplength l'                     (ap nbplength lR)           *)
    Definition R_blength
        (l : BolList) (l' : NBPList) (lR : rel R_BolList l l') :
        natR (blength l) (nbplength l') :=
        map_in_R_nat
            (eq_trans (eq_sym (blength_eq_nbplength l)) (ap nbplength lR)).

    (* [bapp ~ nbpapp]:
       Chain: bollist_to_plist (bapp l1 l2)
                = nbpapp (bollist_to_plist l1) (bollist_to_plist l2)  (bollist_to_plist_app)
                = nbpapp l1'                   (bollist_to_plist l2)  (ap … l1R)
                = nbpapp l1'                   l2'                    (ap … l2R) *)
    Definition R_bapp
        (l1 : BolList) (l1' : NBPList) (l1R : rel R_BolList l1 l1')
        (l2 : BolList) (l2' : NBPList) (l2R : rel R_BolList l2 l2') :
        rel R_BolList (bapp l1 l2) (nbpapp l1' l2') :=
        eq_trans
            (bollist_to_plist_app l1 l2)
            (eq_trans
                (ap (fun x => nbpapp x (bollist_to_plist l2)) l1R)
                (ap (nbpapp l1') l2R)).

    (*  ── Step (d): Register in Trocq's database ────────────────────────── *)

    Trocq Use R_BolList.
    Trocq Use Param44_Bool.   (* diagonal relation for the bool elements *)
    Trocq Use R_BNil.
    Trocq Use R_BCons.
    Trocq Use R_blength.
    Trocq Use R_bapp.
    (* Param_add and Param01_paths were already registered in Part 5
       and remain in Trocq's global database. *)

    (*  ── Step (e): The theorem via Trocq ───────────────────────────────── *)

    Theorem blength_bapp_trocq : forall (l1 l2 : BolList),
        blength (bapp l1 l2) = blength l1 + blength l2.
    Proof.
        trocq.
        apply plength_papp.
    Qed.
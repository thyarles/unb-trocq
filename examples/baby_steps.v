(*****************************************************************************)
(*                  Tutorial: Lists, Parametricity, and Trocq                *)
(*                            — Step by Step —                               *)
(*                                                                           *)
(*  Goal: understand how type parametricity enables proof reuse, and how     *)
(*  Trocq can automate that reuse.                                           *)
(*                                                                           *)
(*  Overview:                                                                *)
(*    Part 0 — Core concept: what is parametricity?                          *)
(*    Part 1 — Natural-number lists (monomorphic): length, append, theorem   *)
(*    Part 2 — Polymorphic lists: length, append, theorem                    *)
(*    Part 3 — Comparing the proofs (tactic style)                           *)
(*    Part 4 — Proof objects: proofs as lambda terms                         *)
(*    Part 5 — Manual transfer                                               *)
(*    Part 6 — Using Trocq                                                   *)
(*****************************************************************************)

(** TODO: better understand the role of the HoTT library. *)
From HoTT Require Import HoTT.
From Coq Require Import ssreflect.
Local Open Scope nat_scope. (* Opens the nat scope so that literals such as
                               0, 1, 2, 3 are interpreted as natural numbers
                               by default. Provided by the ssreflect import. *)

(** Rocq does not allow a type to have itself as its type.  Instead, it uses a
    hidden universe hierarchy: Type@{0} has type Type@{1}, which has type
    Type@{2}, and so on.

    The command [Set Universe Polymorphism] changes this behaviour and tells
    Rocq to treat universe levels as local variables, enabling more generic
    code. *)
Set Universe Polymorphism.

(** PART 0 — Core concept: what is parametricity?
    ---------------------------------------------------------------------------
    Imagine you need lists of naturals, lists of booleans, lists of strings...
    Without parametricity you would have to define a separate type for each one
    and rewrite ALL functions (length, append, reverse...) and ALL proofs from
    scratch.

    With parametric polymorphism you define the operations ONCE for a generic
    type A, and every instance (nat, bool, string...) automatically inherits the
    proved properties.

    The fundamental idea:

      "Properties that depend only on the STRUCTURE of a list (and not on the
      TYPE of its elements) are automatically valid for any instance." *)

(** PART 1 — Natural-number lists (monomorphic): length, append, theorem
    ---------------------------------------------------------------------------
    We define a list type for [nat], as if we did not yet know about
    polymorphism.  This is the "starting point" without generalisation:
    (a) a type
    (b) implementations, and
    (c) a theorem. *)

    (* (a)  Type: a list of naturals is either empty (NNil) or a nat
            followed by another list ([NCons h t]). *)
    Inductive NatList : Type :=
      | NNil  : NatList
      | NCons : nat -> NatList -> NatList.
    Notation "x :n: l" := (NCons x l) (at level 60, right associativity).
    Notation "[[]]"    := NNil.

    (* (b)  Implementation: counts the number of elements. *)
    Fixpoint nlength (l : NatList) : nat :=
      match l with
      | NNil       => O
      | NCons _ t  => S (nlength t)
      end.

    (* (b)  Implementation: appends elements of l1 before l2. *)
    Fixpoint napp (l1 l2 : NatList) : NatList :=
      match l1 with
      | NNil       => l2
      | NCons h t  => NCons h (napp t l2)
      end.

    (* Some examples. *)
    Example nlength_ex1 : nlength [[]] = O.
    Proof. simpl. reflexivity. Qed.

    Example nlength_ex2 : nlength (S O :n: S (S O) :n: S (S (S O)) :n: [[]]) = S (S (S O)).
    Proof. simpl. reflexivity. Qed.

    Example nlength_ex3 : nlength (1 :n: 2 :n: 3 :n: [[]]) = 3.
    Proof. simpl. reflexivity. Qed.

    Example napp_ex : napp (1 :n: 2 :n: [[]]) (3 :n: 4 :n: [[]]) = (1 :n: 2 :n: 3 :n: 4 :n: [[]]).
    Proof. simpl. reflexivity. Qed.

    (* (c)  Theorem:  "The length of the concatenation equals the sum of the lengths." *)
    Theorem nlength_napp :
      forall (l1 l2 : NatList),
        nlength (napp l1 l2) = nlength l1 + nlength l2.
    Proof.
      intros l1 l2.
      induction l1 as [| h t IH].   (* Induction on l1, l2 stays fixed. *)
      - (* Base case: l1 = NNil. *) 
        simpl. reflexivity.         (* Both sides reduce to [nlength l2] by computation. *)
      - (* Inductive step: l1 = NCons h t. *)
        simpl.                      (* Goal: S (nlength (napp t l2)) = S (nlength t + nlength l2) *)
        rewrite IH.                 (* Replaces the left-hand side of IH in the goal. *)
        reflexivity.
    Qed.

(** PART 2 — Polymorphic (parametric) lists
    ---------------------------------------------------------------------------
    Generalization: instead of fixing the element type as nat, we turn the type
    into a PARAMETER "A : Type".

    Notice that the definition and functions are structurally identical to those
    in PART 1.  The only difference is the parameter A. *)

    (* (a)  Type: The polymorphic type parameter A is the type of the elements. *)
    Inductive PList (A : Type) : Type :=
      | PNil  : PList A
      | PCons : A -> PList A -> PList A.
    Arguments PNil  {A}.     (* Tells Rocq to infer A rather than requiring it
                                to be supplied explicitly. Without it we would
                                have to write [@PNil nat] or [@PCons nat 1 l]. *)
    Arguments PCons {A} _ _. (* When writing [PCons h t], Rocq deduces A from
                                the type of h; the two underscores _ indicate
                                that the element and tail remain explicit. *)
    Notation "x :p: l" := (PCons x l) (at level 60, right associativity).
    Notation "{{}}"    := PNil.

    (* (b)  Implementation: identical in structure to [nlength];
            [A] is implicit. *)
    Fixpoint plength {A : Type} (l : PList A) : nat :=
      match l with
      | PNil       => O
      | PCons _ t  => S (plength t)
      end.

    (* (b)  Implementation: appends elements Type A of l1 before l2. *)
    Fixpoint papp {A : Type} (l1 l2 : PList A) : PList A :=
      match l1 with
      | PNil       => l2
      | PCons h t  => PCons h (papp t l2)
      end.
    
    (* Some examples. *)
    Example plength_ex : plength (1 :p: 2 :p: 3 :p: {{}}) = 3.
    Proof. simpl. reflexivity. Qed.

    Example papp_ex : papp (true :p: {{}}) (false :p: false :p: {{}}) 
                         = (true :p: false :p: false :p: {{}}).
    Proof. simpl. reflexivity. Qed.

    (* (c)  Theorem:  "The length of the concatenation equals the sum of the lengths." *)
    Theorem plength_papp :
      forall {A : Type} (l1 l2 : PList A),
        plength (papp l1 l2) = plength l1 + plength l2.
    Proof.
      intros A l1 l2.                     (* A is just one extra intro; the rest is identical! *)
      induction l1 as [| h t IH].
      - simpl. reflexivity.
      - simpl. rewrite IH. reflexivity.
    Qed.

(** PART 3 — Comparing the proofs: differences and similarities
    ---------------------------------------------------------------------------
    Comparing the two proofs side by side:

        nlength_napp                             plength_papp
        ─────────────────────                    ─────────────────────────
        intros l1 l2.                            intros A l1 l2.
        induction l1 as ...                      induction l1 as ...
        - simpl. reflexivity.                    - simpl. reflexivity.
        - simpl. rewrite IH.                     - simpl. rewrite IH.
          reflexivity.                             reflexivity.

    The only structural difference is "intros A".
    
    Why?  The property depends only on HOW the list is built (no elements /
    one element prepended), not on the TYPE of the elements. The type appears
    only in the definition, not in the proof.

    TODO: As suggested by the Advisor, if we ommit the parameters on intros, 
    it will have excactly the same structure.

    - Practical consequence: "plength_papp" is strictly more general than
      "nlength_napp". Instantiating A := nat gives exactly the same statement.

    - Problem: "NatList ≠ PList nat", they are distinct types, so we cannot
      apply "plength_papp" directly to a "NatList". We need a "bridge" between
      the two types. *)

(** PART 4 — Proof objects: proofs as lambda terms
    ---------------------------------------------------------------------------
    In Rocq, PROOFS ARE TERMS of dependent types. Every tactic is just a
    shorthand for building such a term interactively. We will write the same
    proofs directly as functions, using the RECURSOR of each inductive type
    instead of the induction tactic. *)

    (*  ── Monomorphic version as a proof object ────────────────────────

        For NatList, Rocq automatically generates:

        NatList_rect: 
          ∀ (P : NatList → Type),
            P NNil →
            (∀ (h : nat) (t : NatList), P t → P (NCons h t)) →
            ∀ (l : NatList), P l

        P is the motive of the induction — the property we want to prove.
        The second argument is the proof of the base case.
        The third is the proof of the inductive step (receives IH as an argument).

        - idpath is the witness of a = a in HoTT, like eq_refl in standard Rocq.

        - Here it proves the base case because both sides of the equality reduce
          definitionally to [nlength l2].

          [ap S IH] uses the path combinator: ap : (A → B) → a = b → f a = f b

          to "lift" the constructor S over the induction hypothesis IH:
            IH      : nlength (napp t l2) = nlength t + nlength l2
            ap S IH : S (nlength (napp t l2)) = S (nlength t + nlength l2)
          which is exactly the goal in the inductive step after unfolding. *)

        Definition nlength_napp_PO :
          forall (l1 l2 : NatList),
            nlength (napp l1 l2) = nlength l1 + nlength l2 :=
          fun l1 l2 =>
            (* TODO: Print NatList_rect and NatList_ind; analyse the difference. *)
            NatList_rect
              (* motive P *)
              (fun l1 => nlength (napp l1 l2) = nlength l1 + nlength l2)
              (* base case: P NNil = (nlength l2 = nlength l2) *)
              idpath
              (* inductive step: given h, t, IH : P t, produce P (NCons h t) *)
              (fun _h _t IH => ap S IH)
              (* main argument *)
              l1.

    (*  ── Polymorphic version as a proof object ─────────────────────────

        For PList, Rocq generates:

            PList_rect :
              ∀ (A : Type) (P : PList A → Type),
                P PNil →
                (∀ (a : A) (l : PList A), P l → P (PCons a l)) →
                ∀ (l : PList A), P l

        We need to pass A explicitly as the first argument. *)

        Definition plength_papp_PO :
          forall {A : Type} (l1 l2 : PList A),
            plength (papp l1 l2) = plength l1 + plength l2 :=
          fun A l1 l2 =>
            PList_rect A
              (* motive P *)
              (fun l1 => plength (papp l1 l2) = plength l1 + plength l2)
              (* base case *)
              idpath
              (* inductive step *)
              (fun _h _t IH => ap S IH)
              (* main argument *)
              l1.

    (*  ── Comparing the two proof terms as proof objects ─────────────────────────

           nlength_napp_PO                        plength_papp_PO                     
           ──────────────────────                 ──────────────────────              
           fun l1 l2 =>                           fun A l1 l2 =>                      
             NatList_rect                           PList_rect A                      
               (fun l1 => ...)                      (fun l1 => ...)                   
               idpath                               idpath                            
               (fun _ _ IH =>                       (fun _ _ IH =>                    
                 ap S IH)                             ap S IH)                        
               l1.                                  l1.                               
                                                                          
        Difference: NatList_rect vs PList_rect A.
                                                                      
        This is not a coincidence. Both inductive types have the SAME STRUCTURE:
        no base constructors, one recursive constructor with an "extra" field
        (nat vs A) that plays no role in the proof.
                                                                      
        TODO: Could A be replaced by _ (wildcard) in PList_rect?  

        Note: nlength_napp_PO and nlength_napp produce computationally equal
              results, but Rocq cannot compare their internal terms via
              reflexivity because tactic proofs are opaque (closed with Qed).
              To verify the equivalence it suffices to evaluate both proofs
              on a concrete example — the result is the same: *)

        Check nlength_napp_PO (1 :n: [[]]) ([[]]) = nlength_napp (1 :n: [[]]) ([[]]).

(** PART 5 — Manual transfer
    ---------------------------------------------------------------------------
    Goal of this part:
      Show how to "transfer" length_papp to NatList by hand, explicitly
      building the conversion functions and the compatibility lemmas.
      I think this is what Trocq automates.

    The plan:
      1. Define natlist_to_plist : NatList → PList nat
      2. Define plist_to_natlist : PList nat → NatList
      3. Prove they are inverses (isomorphism)
      4. Prove they preserve length and append
      5. Use these bridges to derive nlength_napp from plength_papp 
      6. Take notes *)

    (*  ── 1 & 2: Conversion functions ──────────────────────────────────-── *)

        Fixpoint natlist_to_plist (l : NatList) : PList nat :=
          match l with
          | NNil      => PNil
          | NCons h t => PCons h (natlist_to_plist t)
          end.
        (* Compute natlist_to_plist (1 :n: 2 :n: 3 :n: [[]]) = (1 :p: 2 :p: 3 :p: {{}}). *)

        Fixpoint plist_to_natlist (l : PList nat) : NatList :=
          match l with
          | PNil      => NNil
          | PCons h t => NCons h (plist_to_natlist t)
          end.
        (* Compute plist_to_natlist (1 :p: 2 :p: 3 :p: {{}}) = (1 :n: 2 :n: 3 :n: [[]]). *)

        (* Show the conversion bridge at work: both sides pass through PList nat. *)
        Compute plength (natlist_to_plist (1 :n: 2 :n: 3 :n: [[]])).
        (* => 3  ← same as nlength (1 :n: 2 :n: 3 :n: [[]])  [nlength_eq_plength] *)
        Compute natlist_to_plist (napp (1 :n: 2 :n: [[]]) (3 :n: [[]])).
        (* => 1 :p: 2 :p: 3 :p: {{}}  [natlist_to_plist distributes over napp] *)

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

        (* Strategy for proving nlength_napp using plength_papp:

        nlength (napp l1 l2)
          = plength (natlist_to_plist (napp l1 l2))       [nlength_eq_plength]
          = plength (papp (natlist_to_plist l1)           [natlist_to_plist_app]
                        (natlist_to_plist l2))
          = plength (natlist_to_plist l1)                 [plength_papp]
            + plength (natlist_to_plist l2)
          = nlength l1 + plength (natlist_to_plist l2)    [nlength_eq_plength]
          = nlength l1 + nlength l2                       [nlength_eq_plength]   *)
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

        (* Some examples *)
        Example test_transfer_normal :
          nlength (napp (1 :n: 2 :n: [[]]) (3 :n: [[]])) =
          nlength (1 :n: 2 :n: [[]]) + nlength (3 :n: [[]]).
        Proof. 
          (* The proof actually uses the transferred theorem as its justification — the specific lists are witnesses to the universal statement ∀ l1 l2, nlength (napp l1 l2) = nlength l1 + nlength l2.*)
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

    (*  ── 6: Take notes ─────────────────────────────────────────────────── *)

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

(** PART 6 — Using Trocq
    ---------------------------------------------------------------------------
    Let's try to implement what was sketched in PART 5.

    Trocq works with a database of "parametric relations".

    To use the trocq tactic we need:

    (a) The relation between the TYPES          NatList ~ PList nat
    (b) The relation between the CONSTRUCTORS   NNil ~ PNil  and  NCons ~ PCons
    (c) The relation between the FUNCTIONS      nlength ~ plength  and  napp ~ papp
    (d) Register everything with Trocq Use and then use the tactic trocq  
    (e) The main theorem via Trocq
    (f) Take notes *)

    (* Trocq-specific imports (it somehow breaks the "+" operator) *)
    Check (fun n m : nat => n + m).  (* before Trocq: nat -> nat -> nat *)
    From Trocq Require Import Trocq.
    (*Check (fun n m : nat => n + m).*)  (* after Trocq: breaks or changes *)
    From Trocq Require Import Param_nat. (* natR, Param44_nat, Param_add,
                                            map_in_R_nat, R_in_map_nat  *)
    (* As the import of Trocq breaks the "+" operator, we need to create ours
    Local Notation "n + m" := (Nat.add n m). *)
    Fixpoint add' (n m : nat) : nat :=
      match n with
      | O => m
      | S n' => S (add' n' m)
      end.
    Notation "n :+: m" := (add' n m) (at level 60, right associativity).
                                                                                
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
        and the relation in a single step (standard Trocq project pattern).

        TODO: Review this definition. *)
        Definition R_NatList : Param44.Rel NatList (PList nat).
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

        (* [NNil ~ PNil]: natlist_to_plist NNil = PNil (true by definition). *)
        Definition R_NNil : rel R_NatList NNil PNil := idpath.

        (* [NCons ~ PCons]: given h ~ h' (diagonal relation on nat, [natR h h'])
           and l ~ l' (list relation), we have [NCons h l ~ PCons h' l'].

           "Why [natR h h'] rather than just [h = h']"? Trocq uses natR
           (from Param_nat) as the official relation for nat.
           It is equivalent to = but is what the database recognises.

          [R_in_map_nat hR : h = h'] extracts the equality from the natR relation. *)
        Definition R_NCons
          (h h' : nat) (hR : natR h h')
          (l : NatList) (l' : PList nat) (lR : rel R_NatList l l') :
          rel R_NatList (NCons h l) (PCons h' l') :=
          (* natlist_to_plist (NCons h l) ≡ PCons h (natlist_to_plist l) (by def.) *)
          (* ap (PCons h) lR         : PCons h (nat2p l) = PCons h  l'            *)
          (* ap (PCons · l') h_eq   : PCons h l'         = PCons h' l'            *)
          ap (PCons h) lR @ ap (fun x => PCons x l') (R_in_map_nat hR).

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
          (l : NatList) (l' : PList nat) (lR : rel R_NatList l l') :
          natR (nlength l) (plength l') :=
          (* map_in_R_nat converts (n = n') → natR n n'                *)
          (* map_nat = id by definition, so the goal of map_in_R_nat   *)
          (* is simply: nlength l = plength l'                         *)
          map_in_R_nat ((nlength_eq_plength l)^ @ ap plength lR).

        (* [napp ~ papp]:
           Given l1 ~ l1' and l2 ~ l2', prove
           [rel R_NatList (napp l1 l2) (papp l1' l2')].

           Chain used:
              natlist_to_plist (napp l1 l2)
                = papp (natlist_to_plist l1) (natlist_to_plist l2)  [natlist_to_plist_app]
                = papp l1'                   (natlist_to_plist l2)  [ap ... l1R]
                = papp l1'                   l2'                    [ap ... l2R] *)
        Definition R_napp
            (l1 : NatList) (l1' : PList nat) (l1R : rel R_NatList l1 l1')
            (l2 : NatList) (l2' : PList nat) (l2R : rel R_NatList l2 l2') :
            rel R_NatList (napp l1 l2) (papp l1' l2') :=
          natlist_to_plist_app l1 l2
          @ ap (fun x => papp x (natlist_to_plist l2)) l1R
          @ ap (papp l1') l2R.

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

        (*  TODO:
            Relation added to fix the map error from Trocq, as the add' isn't a Rocq
            core relation.
        *)
        Definition R_add' :
          forall (n1 n1' : nat) (n1R : natR n1 n1') (n2 n2' : nat) (n2R : natR n2 n2'),
            natR (add' n1 n2) (add' n1' n2').
        Proof.
          intros n1 n1' n1R n2 n2' n2R.
          induction n1R as [| n1 n1' n1R IHn1R].
          - (* OR case: add' O n2 = n2 by definition *)
            simpl. exact n2R.
          - (* SR case: add' (S n1) n2 = S (add' n1 n2) by definition *)
            simpl. apply SR. exact IHn1R.
        Defined.
        Trocq Use R_add'.

    (*  ── Step (e): The theorem via Trocq ───────────────────────────────── *)

        (* The proof now has TWO lines:
        
        1. trocq: transforms the goal from NatList to PList nat
        2. exact plength_papp: closes it with the already-proved theorem

        Trocq internally performs all the work we did by hand in PART 5
        (building the bridge, invoking nlength_eq_plength,
        natlist_to_plist_app, etc.) fully automatically.

        TODO: Starting from a proof of a concrete theory, obtain the general
              theory as easily as possible. Trocq should be used in proving
              the general theorem, not here. Redo from this point onward. *)

        (* Theorem nlength_napp_trocq :
          forall (l1 l2 : NatList),
            nlength (napp l1 l2) = nlength l1 :+: nlength l2.
        Proof.
          trocq.
          (** [trocq] transforms the goal:
                NatList → PList nat
                napp    → papp
                nlength → plength
              Resulting goal:
                ∀ l1' l2' : PList nat,
                  plength (papp l1' l2') = plength l1' + plength l2'
              Which is exactly [plength_papp]! *)
          (* exact plength_papp. *)
        Abort. *)

        (*  TODO:
            The error reveals a conceptual mismatch. trocq is being called on a goal that is already in the target language (PList, plength, papp). Trocq tries to translate plength away — but only R_nlength is registered, which maps nlength (source) → plength (target). There is no registered relation that goes out of plength, so it can't find it at the requested class. 
            
            The correct use is the other direction: start with a NatList goal (using nlength and napp), then trocq transforms it into a PList goal that you close with plength_papp. That's exactly the commented-out theorem above it:
        *)

        Theorem nlength_napp_trocq :
          forall (l1 l2 : NatList),
            nlength (napp l1 l2) = nlength l1 :+: nlength l2.
        Proof.
          trocq.         (* transforms: NatList→PList nat, napp→papp, nlength→plength *)
          exact plength_papp.
        Qed.

        (*  TODO:
            The plength_papp' theorem has the goal backwards for what Trocq was set up to do. trocq is a source → target rewriter, and here PList/plength is the target — you can't re-translate the target into itself with the current registrations.
        *)

        Theorem plength_papp' :
          forall {A : Type} (l1 l2 : PList A),
            plength (papp l1 l2) =  plength l1 :+: plength l2.
        Proof.
          trocq.
        Abort. 
 
        (* Print Assumptions plength_papp' shows the axioms assumed by the proof.
           Univalence is not needed here because the relation between NatList and
           PList nat is an isomorphism, not merely a type equivalence. *)
        Print Assumptions plength_papp'.

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

          Comparison with the manual approach (PART 5):
          - Manual: 7 intermediate lemmas + 1 glue proof → repeated for EACH new theorem                    │
          - Trocq : one-time registration + 2 lines per new theorem *)

(** END OF THE EVALUATION *)

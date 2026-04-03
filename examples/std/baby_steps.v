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
        Definition R_NNil : rel R_NatList NNil PNil := eq_refl.

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
          eq_trans (ap (PCons h) lR) (ap (fun x => PCons x l') (R_in_map_nat hR)).

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
          map_in_R_nat (eq_trans (eq_sym (nlength_eq_plength l)) (ap plength lR)).

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
          eq_trans
            (natlist_to_plist_app l1 l2)
            (eq_trans
              (ap (fun x => papp x (natlist_to_plist l2)) l1R)
              (ap (papp l1') l2R)).

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

        Theorem nlength_napp_trocq :
          forall (l1 l2 : NatList),
            nlength (napp l1 l2) = nlength l1 + nlength l2.
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
        Abort.

        (*  TODO:
            The error reveals a conceptual mismatch. trocq is being called on a goal that is already in the target language (PList, plength, papp). Trocq tries to translate plength away — but only R_nlength is registered, which maps nlength (source) → plength (target). There is no registered relation that goes out of plength, so it can't find it at the requested class. 
            
            The correct use is the other direction: start with a NatList goal (using nlength and napp), then trocq transforms it into a PList goal that you close with plength_papp. That's exactly the commented-out theorem above it:
        *)

        (* Theorem nlength_napp_trocq :
          forall (l1 l2 : NatList),
            nlength (napp l1 l2) = nlength l1 + nlength l2.
        Proof.
          trocq.         (* transforms: NatList→PList nat, napp→papp, nlength→plength *)
          exact plength_papp.
        Qed. *)

        (*  TODO:
            The plength_papp' theorem has the goal backwards for what Trocq was set up to do. trocq is a source → target rewriter, and here PList/plength is the target — you can't re-translate the target into itself with the current registrations.
        *)

        Theorem plength_papp' :
          forall {A : Type} (l1 l2 : PList A),
            plength (papp l1 l2) =  plength l1 + plength l2.
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

(** TODO: Specifically, within the context of the Calculus of Inductive Constructions, we evaluate the trade-offs between representing proof scripts versus proof objects and identify the transformation primitives necessary for generalization. Finally, we discuss how these transformations impact underlying proof assistant mechanisms, including type checking, unification, and resolution.
          https://waisiv.cin.ufpe.br/jnamaral.github.io/WAISIV/program/speakers/index.html

          Ajudar na apresentação:
          1. Motivação (hoje faz na mão)
          2. Intuição (trocq é uma "máquina de transferências" que automatiza o processo de generalização)
          3. Mostra como funciona (exemplo simples)
          4. Pegar do Canvas (Arthur) e fazer no Google Drive


          XYZ: Ideia do Selo -> Rastrear o experimento e rastrear os dados
               Pega um estudo empírico e certifica o estudo (olhar Festival de Artefatos)
               Professora Fernanda entende os desafios de automatizar esses processos
               Oportunidade de pesquisa: criar um modelo para certificar um estudo empírico

               Eneas deu um passo importante. Aluno do Ayala provou quatro ou cinco teoremas, mas não entrou
               no artigo. Não só mostrar a rastreabilidade, mas ter um modelo que contemple diferentes tipos de
               artefatos e diferentes tipo de evidências (alguém pode atestar ou o resultado de uma função
               computando algo). DSL: pode usar Llama o trabalho do Eneas. Nos modelos, o importante é rastrear
               os dados. A evidência pode ser heterogência, mas podemos documentar as que não sejam empíricas.

               O que se espera: modelo formal para especificar experimentos. O modelo tem que ter rastreabilidade
               dos resultados, tem que contemplar tratamentos de programas e não programas e, neste caso, deveria
               ter alguma forma de validar a evidência. Pode ser adaptado ou estendido para estudos de IA.

               Ver as apresentações do professor para ver quem está interessado.
*)
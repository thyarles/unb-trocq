From Coq Require Import ssreflect.
From HoTT Require Import HoTT.
From Trocq Require Import Trocq.
From Trocq_examples Require Import N.

(** Set Universe Polymorphism

    Coq does not allow Type to be of type Type. Instead, it uses a hidden, infinite hierarchy of
    universes: Type@{0} has type Type@{1}, which has type Type@{2}, and so on.

    The command "Set Universe Polymorphism" changes this behavior. It tells Coq to treat universes
    as local, bound variables rather than fixed global constraints. This allows us to write more 
    general code that can work across different universe levels without having to specify them 
    explicitly.
*)
Set Universe Polymorphism.

(** STEP 1: RELATING THE TYPES

    We transport the induction principle on natural numbers from two equivalent representations
    of "N": the unary one "nat" and the binary one "N". 
  
    - First, we define the relation.
      "Iso.toParamSym" takes the standard isomorphism between binary and unary numbers and lifts 
      it into Trocq's hierarchy of relations. 
    
    - Instead of a rigid univalent equivalence, Trocq decomposes this into its 36-element.
*)
Definition RN : (N <=> nat)%P := Iso.toParamSym N.of_nat_iso.

(** Trocq Use

    We use the `Trocq Use` command to register this type translation. Under the hood, this adds
    the relation to a COQ-ELPI meta-level database (the "knowledge base"), so the `trocq` tactic
    can automatically find it later when translating the goal.
*)
Trocq Use RN.

(** STEP 2: RELATING THE CONSTANTS

    This equivalence proof coerces to a relation of type `N -> nat -> Type`.
    
    We must manually provide the base cases: proving that the zero and successor constants of 
    these types are perfectly related through our isomorphism. 
*)
Definition RN0 : RN 0%N 0%nat.
  (** The binary zero (0%N) and the unary zero (0%nat) are structurally related. *)
  Proof. done. Defined.

Definition RNS m n : RN m n -> RN (N.succ m) (S n). 
  (** The binary successor (N.succ) and the unary successor (S) are structurally related. *)
  Proof. by case. Defined.

(** Trocq Use

    We register these constant relations in the Trocq knowledge base just like the types.

    This prevents us from having to manually prove how operations map to each other 
    every time we translate a goal.
*)
Trocq Use RN0.
Trocq Use RNS.

(** STEP 3: THE PROOF TRANSFER

    We state the standard, natural mathematical induction principle, but we 
    state it for "N" (the binary representation).
    
    Binary numbers natively have an unnatural induction principle (based on bit shifts)
    making manual proofs very hard.
*)
Lemma N_Srec : forall (P : N -> Type), P 0%N ->
  (forall n, P n -> P (N.succ n)) -> forall n, P n.
  (** The "trocq" tactic is called. It does the following:
      1. Traverses the initial goal G ("N_Srec").
      2. Replaces "N" with "nat" to create the associated goal G' (unary induction).
      3. Builds a constraint graph of parametricity classes and infers the minimal possible 
         classes needed to prove G' -> G at the specific entry level (0,1).
      4. It applies this implication proof, leaving us with only G' to prove.
  *)
  Proof. 
    trocq. 
    (** The goal has now been "magically" rewritten to use "nat". 
        We can simply provide the exact induction principle from the standard library.
    *)
    exact nat_rect. 
  Defined.

(** STEP 4: INSPECTING THE RESULTS
    
    Inspecting the proof term reveals how Trocq's Parametricity Class Inference works. 
*)
Print N_Srec.
Print Assumptions N_Srec.

(** Testing the new induction principle on binary numbers.

    Indeed this computes efficiently because it is built on partial isomorphisms
    and doesn't get stuck on uncomputable axioms.

  - "Eval compute in" fully calculates the expression and outputs the final answer.
  - "N_Srec" is the unary induction principle that Trocq just translated to work on
    the binary representation N. It acts like a traditional for loop or fold.
  - "(fun _ => N)" is the "return type" of the loop. Just return a binary number (N).
  - "(0%N)" is the base case. If the input is 0, the loop returns 0.
  - "N.add" is the "step" function. At each step of the induction, it takes the current
    index and the accumulated total, and adds them together.
  - "1~0~1~1~0~1%positive" is the input number n in binary format (= 45).
  - By running this, you are using the transferred unary loop to calculate the sum of all
    integers from 0 to 44, efficiently returning "(1~1~1~1~0~1~1~1~1~0)%positive" (= 990).
    
  You get the ease of a unary proof, with the execution speed of a binary computation.    
*)
Eval compute in N_Srec (fun _ => N) (0%N) N.add 1~0~1~1~0~1%positive.

(** 1. The Small Number Example (Summing 0 to 5)

    To get the sum of numbers from 0 to 5, the induction loop needs to iterate 6 times
    (for the indices 0, 1, 2, 3, 4, 5). Therefore, the input number to the function is 5.

    Binary numbers ("positive") are constructed bit-by-bit using "~0" and "~1" appended to "1". 
    * The decimal number "6" is "110" in binary, which is written as "1~1~0%positive".
    * The expected sum of 0 to 5 is "0 + 1 + 2 + 3 + 4 + 5 = 15".
    * The decimal number "15" is "1111" in binary, which is written as "1~1~1~1%positive".
*)
Eval compute in N_Srec (fun _ => N) (0%N) N.add 1~1~0%positive.

(** 2. How this is solved WITHOUT Trocq (just standard Coq)

    Binary numbers ("N") natively lack a natural step-by-step induction principle.
    They are built using a binary tree structure (bit shifts), meaning you cannot naturally
    loop over them one-by-one ("n", then "n+1") without doing extra work.
    
    Unary numbers ("nat") have the natural "nat_rect" induction principle, but they are
    exponentially slower to compute.

    Without Trocq, relying on the easy-to-prove Peano (`nat`) representation forces the computer
    to do incredibly inefficient, slow math. 
  
    To sum the numbers from 0 to 5 in pure Peano arithmetic, we use the standard "nat_rect"
    loop and standard unary addition. 
*)
Eval compute in 
  Datatypes.nat_rect                         (* Standard loop *)
    (fun _ => Datatypes.nat)                 (* Standard return type *)
    Datatypes.O                              (* Base case: standard 0 *)
    (fun (n : Datatypes.nat) (acc : Datatypes.nat) =>  
       Nat.add n acc)                        (* Standard unary addition *)
    (Datatypes.S                             (* The number 6, in Peano *)
     (Datatypes.S(Datatypes.S(Datatypes.S(Datatypes.S(Datatypes.S Datatypes.O)))))
    ). 

(** Points to note
    
    * The Unary Performance Problem
      In the pure "nat" approach above, the number 45 is not just a digit; it is stored
      in memory as 45 nested successors: `S (S (S ... O))`. When you ask Coq to add `a + b`
      in unary, it has to recursively peel off every single `S` from `a` and stick it onto
      `b` one-by-one. 
    * Summing from 0 to 5 in Peano is fast enough. But calculating the sum from 0 to 10,000.
      In pure Peano ("nat"), this requires millions of recursive pattern-matching steps.
      Coq will freeze, take minutes to compute, or simply crash with a stack overflow.
    * The binary representation ("N") compresses numbers exponentially into bits ("1~0~1...").
      Binary addition is nearly instantaneous because it works on bits, just like a real CPU.
      But binary numbers lack the natural mathematical induction principle you just used above
      ("nat_rect"), making proofs about them a nightmare. 
    * Without Trocq, you have to choose between **easy proofs but uncomputably slow code
      (using "nat"), or **fast code but impossibly difficult proofs (using "N"). 
    * With Trocq's axiom-free parametricity translation, you get both. You write your proofs
      using the easy Peano induction principle, and Trocq automatically transfers it so your
      program executes using the lightning-fast binary addition, without locking up the
      computation engine.
*)
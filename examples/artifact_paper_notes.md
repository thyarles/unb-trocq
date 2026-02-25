# Trocq

## What is Trocq?

A proof transfer framework for the Rocq.

In formal mathematics:

- Users often face the problem of having multiple representations for the same mathematical object (lists vs. vectors, or different types of integers).

- Trocq allows to automatically transfer proofs and computations from one representation to another without always requiring the heavy "univalence axiom".

## A simple example

### Two representations of natural numbers

1.  **Unary (Peano) Representation (`nat` or $\mathbb{N}$):**
    
    - This is the standard definition where a number is either `0` or the successor of another number `S n`.
    - It provides a very natural induction principle, which makes it easy to write mathematical proofs.    
    - However, it is exponentially slow and unnatural for actual computations.

2.  **Binary Representation (`N` or `bin_nat`):**

    - This alternative represents numbers using binary digits (e.g., encoding numbers with constructors that represent bit shifts).
    
    - It is highly efficient for computation but possesses a complex, unnatural induction principle that makes doing manual proofs very difficult.

## How Trocq solves the simple example

We want the best of both worlds: **do proofs in the unary system**, but **run computations in the binary system**, `without duplicating the proofs`.

### >> Step 1: Relating the representations

We first provide Trocq with conversion functions between the two types, $$\uparrow_N: \mathbb{N} \to N\text{ and }\downarrow_N: N \to \mathbb{N}.$$

We also prove basic relations showing they are inverses of each other, and that they correctly map $0_\mathbb{N}$ to $0_N$ and the unary successor $S_\mathbb{N}$ to the binary successor $S_N$.

### >> Step 2: Transferring computations and proofs

Because we defined how the base elements relate, Trocq uses a `parametricity translation` to automatically bridge more complex functions, like addition ($+_\mathbb{N} \sim +_N$). 

### >> Step 3 The goal substitution

If we have a goal $G$ in the binary representation, Trocq automatically reduces it to a hypothesis $H$ (or $G'$) in the unary representation.

It does this by systematically finding an implication arrow ($H \to G$) at a specific parametricity entry level denoted as $(0,1)$.

This allows you to automatically justify that a complex computation like a sum over binary numbers equals the transferred sum over unary numbers: $$\sum_{i=0_N}^{17_N} i = \uparrow_N \sum_{i=0_\mathbb{N}}^{17_\mathbb{N}} i$$ 


## Type constraints

`Traditional univalent parametricity` (the predecessor to Trocq) rigidly forces we to prove a full, perfectly symmetrical "equivalence" between types, which `requires adding the univalence axiom to the system`.

Trocq breaks this rigid requirement by decomposing equivalence into a `36-element` of relations. 

* These 36 levels are represented by pairs of numbers, ranging from a raw relation at `(0,0)` all the way to a full univalent equivalence at `(4,4)`.

* When Trocq traverses the user's goal to translate it, it creates a `constraint graph` with variables for the required parametricity classes. 

* Instead of forcing everything to the maximum `(4,4)` level, Trocq performs `parametricity class inference` (it calculates the `minimal` possible class needed to make the translation work).

* If the required type constraints infer that your translation level stays below a specific threshold (let's say $\alpha \ngeq (2_b, 0)$ and $\alpha \ngeq (0, 2_b)$), Trocq can perform the proof transfer using only `partial isomorphisms` without triggering the `univalence axiom` at all. 

This makes Trocq highly modular; it asks for the absolute minimum amount of proof constraints required to map your types together.

# Show cases

## The Fermat's Last Theorem Modulo 9

Imagine you need to prove a step of Fermat's Last Theorem for $n=3$:

*If 3 does not divide $a$, $b$, and $c$, then $a^3 + b^3 \neq c^3$*. 

*   Usually, mathematicians prove this by looking at the numbers modulo 9.
*   In standard Coq, this is very tedious because you are working with the infinite type of integers (`Z`).
*   With Trocq, you can define a transfer from infinite integers to the finite type of integers modulo 9 ($Z/9Z$). 
*   Because Trocq automatically translates the goal, you change an infinite proof into a simple equality over $9^3$ (729) finite cases.
* You can then just use a compute tactic to brute-force check all 729 cases, completing the proof instantly without manual reasoning.

## Computing polynomial degrees
In libraries like `Mathlib`, polynomials are often defined in a non-computable way for mathematical purity. If you have a specific, concrete polynomial and want Coq to compute its degree (e.g., proving the degree is exactly 7), the standard representation will get stuck.

With Trocq, you can transfer the goal to a slightly different, computable representation of polynomials, run the computation to get 7, and transfer the result back. 


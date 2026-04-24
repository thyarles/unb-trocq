From Stdlib Require Import ssreflect.
Require Import Trocq_examples.bs_p1.
Require Import Trocq_examples.bs_p2.
Local Open Scope nat_scope.

Set Universe Polymorphism.

(*  In Rocq, PROOFS ARE TERMS of dependent types. Every tactic is just a
    shorthand for building such a term interactively. We will write the same
    proofs directly as functions, using the RECURSOR of each inductive type
    instead of the induction tactic.  *)

(*  ── Monomorphic version as a proof object ──────────────────────────────────

    For NatList, Rocq automatically generates:

    NatList_rect: 
        ∀ (P : NatList → Type),
        P NNil →
        (∀ (h : nat) (t : NatList), P t → P (NCons h t)) →
        ∀ (l : NatList), P l

    P is the motive of the induction — the property we want to prove.
    The second argument is the proof of the base case.
    The third is the proof of the inductive step (receives IH as an argument).
*)

Definition nlength_napp_PO :
    forall (l1 l2 : NatList),
    nlength (napp l1 l2) = nlength l1 + nlength l2 :=
    fun l1 l2 =>
    (* TODO: Print NatList_rect and NatList_ind; analyse the difference.     *)
    NatList_rect
        (* motive P *)
        (fun l1 => nlength (napp l1 l2) = nlength l1 + nlength l2)
        (* base case: P NNil = (nlength l2 = nlength l2) *)
        eq_refl
        (* inductive step: given h, t, IH : P t, produce P (NCons h t) *)
        (fun _h _t IH => f_equal S IH)
        (* main argument *)
        l1.

(*  ── Polymorphic version as a proof object ──────────────────────────────────

    For PList, Rocq generates:

        PList_rect :
            ∀ (A : Type) (P : PList A → Type),
            P PNil →
            (∀ (a : A) (l : PList A), P l → P (PCons a l)) →
            ∀ (l : PList A), P l

    We need to pass A explicitly as the first argument. 
*)

Definition plength_papp_PO :
    forall {A : Type} (l1 l2 : PList A),
    plength (papp l1 l2) = plength l1 + plength l2 :=
    fun A l1 l2 =>
    PList_rect A
        (* motive P *)
        (fun l1 => plength (papp l1 l2) = plength l1 + plength l2)
        (* base case *)
        eq_refl
        (* inductive step *)
        (fun _h _t IH => f_equal S IH)
        (* main argument *)
        l1.

Check nlength_napp_PO (1 :n: [[]]) ([[]]) = nlength_napp (1 :n: [[]]) ([[]]).
        
(** EXPL C — Coparing the proofs (lambda terms) 

    nlength_napp_PO                        plength_papp_PO                     
    ──────────────────────                 ──────────────────────              
    fun l1 l2 =>                           fun A l1 l2 =>                      
        NatList_rect                           PList_rect A                      
        (fun l1 => ...)                      (fun l1 => ...)                   
        eq_refl                               eq_refl                            
        (fun _ _ IH =>                       (fun _ _ IH =>                    
            f_equal S IH)                             f_equal S IH)                        
        l1.                                  l1.                               
                                                                        
    Difference: NatList_rect vs PList_rect A.
*)

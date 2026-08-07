Unset Universe Polymorphism.
Unset Uniform Inductive Parameters. 

Inductive testFalse : Set :=.

Inductive testUnit : Set := 
| TT : testUnit.

Inductive testBool : Set := 
| Falseb 
| Trueb.

Inductive Wrap : Set :=
| KWrap1 : forall _ : testUnit, Wrap.

Inductive WrapMore : Set :=
| KWrap : forall (_: testUnit) (_ : testBool), WrapMore
| KWrapWrap : forall (_ : Wrap), WrapMore
| F : forall (_ : testUnit) (_ : testUnit) (_ : testUnit), WrapMore.

Inductive Nat : Set :=
| O' 
| S' : forall (_ : Nat), Nat.

Inductive Box (A : Type) : Type :=
| B : forall (_: A), Box A.

Inductive Option (A : Type) : Type :=
| None' : Option A 
| Some' : forall (_ : A), Option A.

Inductive Prod (A B : Type) : Type :=
| PR : forall (_ : A) (_ : B), Prod A B. 

Inductive ThreeTypes (A B C : Type) :=
| C1 : forall (_ : A), ThreeTypes A B C
| C2 : forall (_ : B), ThreeTypes A B C
| C3 : forall (_ : C), ThreeTypes A B C.

Inductive List (A : Type) : Type :=
| Nil : List A 
| Cons : forall (_ : A) (_ : List A), List A.

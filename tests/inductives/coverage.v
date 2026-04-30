Unset Universe Polymorphism.
From elpi Require Import elpi.
From elpi.apps Require Import derive derive.param2.

From Trocq Require Import sym.
Unset Uniform Inductive Parameters. 

Inductive testFalse : Set :=.

Inductive testUnit : Set := 
| TT : testUnit.

Inductive testBool : Set := 
| Falseb 
| Trueb.

Inductive Wrap : Set :=
| KWrap1 : testUnit -> Wrap.

Inductive WrapMore : Set :=
| KWrap : testUnit -> testBool -> WrapMore
| KWrapWrap : Wrap -> WrapMore
| F : testUnit -> testUnit -> testUnit -> WrapMore.

Inductive Nat : Set :=
| O' 
| S' : Nat -> Nat.

Inductive Box (A : Type) : Type :=
| B : A -> Box A.

Inductive Option (A : Type) : Type :=
| None' : Option A 
| Some' : A -> Option A.

Inductive Prod (A B : Type) : Type :=
| PR : A -> B -> Prod A B. 

Inductive ThreeTypes (A B C : Type) :=
| C1 : A -> ThreeTypes A B C
| C2 : B -> ThreeTypes A B C
| C3 : C -> ThreeTypes A B C.

Inductive List (A : Type) : Type :=
| Nil : List A 
| Cons : A -> List A -> List A.

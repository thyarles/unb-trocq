Inductive False : Set :=.

Inductive Unit : Set := 
| TT : Unit.

Inductive Bool : Set := 
| Falseb 
| Trueb.

Inductive Wrap : Set :=
| KWrap1 : Unit -> Wrap.

Inductive WrapMore : Set :=
| KWrap : Unit -> Bool -> WrapMore
| KWrapWrap : Wrap -> WrapMore
| F : Unit -> Unit -> Unit -> WrapMore.

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

Inductive Mix (A : Type) : Type :=
| Con : A -> Unit -> Mix A.

Inductive ThreeTypes (A B C : Type) :=
| C1 : A -> ThreeTypes A B C
| C2 : B -> ThreeTypes A B C
| C3 : C -> ThreeTypes A B C.

Inductive List (A : Type) : Type :=
| Nil : List A 
| Cons : A -> List A -> List A.

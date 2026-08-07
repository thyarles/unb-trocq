From Trocq Require Import injection_lemmas.
Require Import coverage.
Unset Uniform Inductive Parameters.

Elpi derive.projK testFalse.
Elpi derive.injections testFalse.

Elpi derive.projK testUnit.
Elpi derive.injections testUnit.

Elpi derive.projK testBool.
Elpi derive.injections testBool.

Elpi derive.projK Wrap.
Elpi derive.injections Wrap.

Elpi derive.projK WrapMore.
Elpi derive.injections WrapMore.

Elpi derive.projK Nat.
Elpi derive.injections Nat.

Elpi derive.projK Box.
Elpi derive.injections Box.

Elpi derive.projK Option.
Elpi derive.injections Option.

Elpi derive.projK Prod.
Elpi derive.injections Prod.

Elpi derive.projK ThreeTypes.
Elpi derive.injections ThreeTypes.

Elpi derive.projK List.
Elpi derive.injections List.
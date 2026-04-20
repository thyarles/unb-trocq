From Trocq Require Import injK.
Require Import coverage.
Unset Uniform Inductive Parameters.

Elpi derive.projK False.
Elpi derive.injections False.
Elpi derive.injK False.

Elpi derive.projK testUnit.
Elpi derive.injections testUnit.
Elpi derive.injK testUnit.

Elpi derive.projK testBool.
Elpi derive.injections testBool.
Elpi derive.injK testBool.

Elpi derive.projK Wrap.
Elpi derive.injections Wrap.
Elpi derive.injK Wrap.

Elpi derive.projK WrapMore.
Elpi derive.injections WrapMore.
Elpi derive.injK WrapMore.

Elpi derive.projK Nat.
Elpi derive.injections Nat.
Elpi derive.injK Nat.

Elpi derive.projK Box.
Elpi derive.injections Box.
Elpi derive.injK Box.

Elpi derive.projK Option.
Elpi derive.injections Option.
Elpi derive.injK Option.

Elpi derive.projK Prod.
Elpi derive.injections Prod.
Elpi derive.injK Prod.

Elpi derive.projK ThreeTypes.
Elpi derive.injections ThreeTypes.
Elpi derive.injK ThreeTypes.

Elpi derive.projK List.
Elpi derive.injections List.
Elpi derive.injK List.
---
article_id: af_df471aad9bbb8883f7e475b7
declaration: definition
origin: cited
source_units: [chapter-ii-sections-6-7]
---

# The Weil divisor group

For a scheme `X` satisfying `(*)`, define a prime divisor as an integral
closed subscheme of codimension one and identify it with its codimension-one
generic point. Define `Div X` as the additive group of integer-valued
algebraic cycles supported on those points, and define effectiveness by
coefficientwise nonnegativity.

Prove that on a Noetherian scheme this cycle representation is the free
abelian group on prime divisors: local finiteness of the support is equivalent
to the finite support used by Hartshorne.

## Depends on

- [Regularity in codimension one](regular-in-codimension-one.md)
- [Codimension-one stalks are DVRs](codimension-one-stalk-dvr.md)
- [Generic points of irreducible closed subsets](../../foundational-properties/generic-points.md)

## Proof depends on

- `AlgebraicGeometry.AlgebraicCycle` from
  `Mathlib/AlgebraicGeometry/AlgebraicCycle/Basic.lean`.
- A locally finite family in a quasi-compact space has finite support.

## Sources

- [Hartshorne II.6, prime and Weil divisor definitions on printed p.130](../../../../sources/hartshorne-ii-6.md#weil-divisors-and-class-groups)

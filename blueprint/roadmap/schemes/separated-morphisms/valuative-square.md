---
article_id: af_b1f590b6e9f03bcd999f1df2
declaration: structure
origin: cited
mathlib: true
mathlib_declaration: AlgebraicGeometry.ValuativeCommSq
mathlib_file: Mathlib/AlgebraicGeometry/ValuativeCriterion.lean
---

# Valuative commutative squares

For a morphism $f : X \longrightarrow Y$, a valuative square consists of a valuation
ring $R$, a field $K$ with $K$ as the fraction field of $R$, and a commutative square

$\operatorname{Spec} K \longrightarrow X$, $\operatorname{Spec} R \longrightarrow Y$.

A lift is a morphism $\operatorname{Spec} R \longrightarrow X$ with the two expected equations.
Existence means every such square has a lift, uniqueness means its lift type is
a subsingleton, and the full valuative criterion means that lift type is
inhabited and unique. The fraction-ring presentation avoids requiring a
literal inclusion $R \subseteq K$.

## Depends on

- [The contravariant Spec functor](../spectrum-and-schemes/spec-functor.md)

## Proof depends on

- The lifting property for a commutative square.

## Sources

- [Hartshorne II.4, Theorems 4.3 and 4.7](../../../sources/hartshorne-ii-4.md#separatedness-and-the-valuative-criterion)

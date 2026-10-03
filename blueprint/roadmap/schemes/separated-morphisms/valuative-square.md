---
declaration: structure
origin: cited
source_units: [chapter-ii-section-4]
mathlib: true
mathlib_declaration: AlgebraicGeometry.ValuativeCommSq
mathlib_file: Mathlib/AlgebraicGeometry/ValuativeCriterion.lean
---

# Valuative commutative squares

For a morphism `f : X ⟶ Y`, a valuative square consists of a valuation
ring `R`, a field `K` with `IsFractionRing R K`, and a commutative square

`Spec K ⟶ X`, `Spec R ⟶ Y`.

A lift is a morphism `Spec R ⟶ X` with the two expected equations.
Existence means every such square has a lift, uniqueness means its lift type is
a subsingleton, and the full valuative criterion means that lift type is
inhabited and unique. The fraction-ring presentation avoids requiring a
literal inclusion `R ⊆ K`.

## Depends on

- [The contravariant Spec functor](../spectrum-and-schemes/spec-functor.md)

## Proof depends on

- The categorical `CommSq.LiftStruct` API.

## Sources

- [Hartshorne II.4, Theorems 4.3 and 4.7](../../../sources/hartshorne-ii-4.md#separatedness-and-the-valuative-criterion)

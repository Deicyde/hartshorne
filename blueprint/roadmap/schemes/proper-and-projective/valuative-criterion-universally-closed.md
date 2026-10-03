---
declaration: lemma
origin: cited
source_units: [chapter-ii-section-4]
mathlib: true
mathlib_declaration: AlgebraicGeometry.UniversallyClosed.eq_valuativeCriterion
mathlib_file: Mathlib/AlgebraicGeometry/ValuativeCriterion.lean
---

# Valuative criterion for universal closedness

Universal closedness is exactly the conjunction of quasi-compactness and the
existence part of the valuative criterion. Equivalently, a quasi-compact
morphism is universally closed when every valuative commutative square admits
a lift.

Existence of lifts makes every base change specializing: given a
specialization, factor the corresponding local-ring map through a dominating
valuation ring. Conversely, a universally specializing map supplies the
closed-point lift by comparing stalks inside the fraction field. A
quasi-compact specializing scheme morphism is closed, yielding universal
closedness after every base change.

## Depends on

- [Universally closed morphisms](universally-closed-morphism.md)
- [Valuative commutative squares](../separated-morphisms/valuative-square.md)
- [Quasi-compact morphisms](../first-properties/quasi-compact-morphism.md)

## Proof depends on

- [Closed images and specialization](../separated-morphisms/quasi-compact-image-closed.md)
- [Every local subring is dominated by a valuation ring](../../nonsingular-curves/valuation-ring-dominates-local-subring.md)

## Sources

- [Hartshorne II.4, existence argument in Theorem 4.7](../../../sources/hartshorne-ii-4.md#properness-and-the-valuative-criterion)

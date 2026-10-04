---
article_id: af_ecf63b3f6b49a569c24a1d09
declaration: lemma
origin: cited
source_units: [chapter-ii-section-4]
mathlib: true
mathlib_declaration: AlgebraicGeometry.IsSeparated.eq_valuativeCriterion
mathlib_file: Mathlib/AlgebraicGeometry/ValuativeCriterion.lean
---

# Valuative criterion for separatedness

For a scheme morphism `f`, separatedness is equivalent to the conjunction of
quasi-separatedness and uniqueness of lifts in every valuative commutative
square. Consequently, if the source is Noetherian, `f` is separated exactly
when every valuation square has at most one lift, which is Theorem 4.3.

The forward direction compares two lifts through the closed diagonal. For the
reverse direction, uniqueness forces the diagonal to satisfy the existence
criterion for universal closedness; quasi-separatedness makes the diagonal
quasi-compact, so it is a closed immersion. Hartshorne's proof instead uses
closedness of the diagonal range under specialization.

## Depends on

- [Separated morphisms](separated-morphism.md)
- [Valuative commutative squares](valuative-square.md)
- [Locally Noetherian schemes](../first-properties/locally-noetherian.md)

## Proof depends on

- [Closed range of the diagonal](diagonal-range-closed.md)
- [Maps from spectra of valuation rings](valuation-spectrum-map-classification.md)
- [Closed images and specialization](quasi-compact-image-closed.md)

## Sources

- [Hartshorne II.4, Theorem 4.3](../../../sources/hartshorne-ii-4.md#separatedness-and-the-valuative-criterion)

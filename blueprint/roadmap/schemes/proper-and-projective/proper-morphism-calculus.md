---
article_id: af_e89ce409714107e99d048946
declaration: theorem
origin: cited
source_units: [chapter-ii-section-4]
---

# Proper-morphism calculus

Proper morphisms satisfy all clauses of Corollary 4.8: closed immersions are
proper; composites and base changes of proper morphisms are proper; products
over a base are proper; if `g ∘ f` is proper and `g` is separated, then `f`
is proper; and properness is local on the target.

Package these statements together as the working API. Use the corresponding
separated and local-finite-type calculus for those components. Universal
closedness is stable under composition and base change, and cancels from a
composite against a separated second map by applying the diagonal argument.
Alternatively, all clauses follow uniformly from unique valuation lifts.

## Depends on

- [Proper morphisms](proper-morphism.md)
- [Separated morphisms](../separated-morphisms/separated-morphism.md)

## Proof depends on

- [Valuative criterion for properness](valuative-criterion-proper.md)
- [Separated-morphism calculus](../separated-morphisms/separated-morphism-calculus.md)
- [Finite-type morphisms compose](../first-properties/finite-type-composition.md)
- [Finite type is stable under base extension](../fiber-products/finite-type-base-change.md)
- `IsProper.stableUnderComposition`, `IsProper.isStableUnderBaseChange`, and
  `IsProper.of_comp` from `Mathlib/AlgebraicGeometry/Morphisms/Proper.lean`.

## Sources

- [Hartshorne II.4, Corollary 4.8](../../../sources/hartshorne-ii-4.md#properness-and-the-valuative-criterion)

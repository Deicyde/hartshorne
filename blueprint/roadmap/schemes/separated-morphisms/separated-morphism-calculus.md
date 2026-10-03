---
declaration: theorem
origin: cited
source_units: [chapter-ii-section-4]
---

# Separated-morphism calculus

Separated morphisms satisfy all clauses of Corollary 4.6: open and closed
immersions are separated; composites and base changes of separated morphisms
are separated; products over a base are separated; if `g ∘ f` is separated,
then `f` is separated; and separatedness is local on the target.

Package these clauses as the working calculus for later chapters. Composition,
base change, and target locality follow from the corresponding properties of
closed immersions applied to the diagonal. Products are two base changes
followed by composition. Cancellation identifies the relative diagonal of
`f` with a pullback/closed factor of the diagonal of the composite. The
valuative criterion gives an alternative uniform proof.

## Depends on

- [Separated morphisms](separated-morphism.md)
- [Open immersions and open subschemes](../subschemes-and-dimension/open-immersions.md)
- [Closed immersions and closed subschemes](../subschemes-and-dimension/closed-immersions.md)

## Proof depends on

- [Valuative criterion for separatedness](valuative-criterion-separated.md)
- `IsSeparated.stableUnderComposition`,
  `IsSeparated.isStableUnderBaseChange`, and `IsSeparated.of_comp` from
  `Mathlib/AlgebraicGeometry/Morphisms/Separated.lean`.

## Sources

- [Hartshorne II.4, Corollary 4.6](../../../sources/hartshorne-ii-4.md#separatedness-and-the-valuative-criterion)

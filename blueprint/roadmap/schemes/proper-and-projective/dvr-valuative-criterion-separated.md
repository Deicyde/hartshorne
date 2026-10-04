---
article_id: af_76c399f9efcbb25ce4ccd596
declaration: theorem
origin: cited
source_units: [chapter-ii-section-4]
---

# DVR-valuative criterion for separatedness

Let `f : X ⟶ Y` be a finite-type morphism of Noetherian schemes. Then `f`
is separated if and only if every valuative commutative square whose valuation
ring is a discrete valuation ring has at most one lift.

The forward implication restricts the ordinary uniqueness criterion. For the
converse, prove that the diagonal range is stable under specialization. An
equality specialization is immediate. For a strict specialization, the local
domain on the reduced closure has nonzero maximal ideal, and finite type makes
the relevant residue-field extension finitely generated. Choose a dominating
DVR, apply uniqueness to the two projected lifts, and conclude that the
specialized point remains on the diagonal. Quasi-compactness then makes the
range closed.

## Depends on

- [Valuative commutative squares](../separated-morphisms/valuative-square.md)
- [Separated morphisms](../separated-morphisms/separated-morphism.md)
- [Morphisms of finite type](../first-properties/finite-type.md)
- [Noetherian schemes and finite affine covers](../first-properties/noetherian-scheme.md)

## Proof depends on

- [A dominating DVR in a finitely generated extension](dominating-dvr-finitely-generated-extension.md)
- [Valuative criterion for separatedness](../separated-morphisms/valuative-criterion-separated.md)
- [Closed images and specialization](../separated-morphisms/quasi-compact-image-closed.md)
- [Maps from spectra of valuation rings](../separated-morphisms/valuation-spectrum-map-classification.md)

## Sources

- [Hartshorne II.4, separatedness clause of Exercise 4.11(b)](../../../sources/hartshorne-ii-4.md#adopted-exercises)

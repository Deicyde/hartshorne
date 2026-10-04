---
article_id: af_6941c1b179a9b3929ef4bbf0
declaration: theorem
origin: cited
source_units: [chapter-ii-section-4]
---

# DVR-valuative criterion for properness

Let `f : X ⟶ Y` be a finite-type morphism of Noetherian schemes. Then `f`
is proper if and only if every valuative commutative square whose valuation
ring is a discrete valuation ring has a unique lift.

The forward implication restricts the full valuative criterion. Conversely,
uniqueness first gives separatedness by the DVR criterion. To obtain universal
closedness, work after an arbitrary base change and prove that the image of
each reduced closed subscheme is stable under specialization. Equality
specializations are immediate; for strict specializations use the nonzero
maximal ideal on the reduced closure, choose a dominating DVR in the relevant
finitely generated residue-field extension, and apply existence of a lift.
Quasi-compactness converts specialization stability to closedness.

## Depends on

- [Valuative commutative squares](../separated-morphisms/valuative-square.md)
- [Proper morphisms](proper-morphism.md)
- [Morphisms of finite type](../first-properties/finite-type.md)
- [Noetherian schemes and finite affine covers](../first-properties/noetherian-scheme.md)

## Proof depends on

- [DVR-valuative criterion for separatedness](dvr-valuative-criterion-separated.md)
- [A dominating DVR in a finitely generated extension](dominating-dvr-finitely-generated-extension.md)
- [Valuative criterion for properness](valuative-criterion-proper.md)
- [Closed images and specialization](../separated-morphisms/quasi-compact-image-closed.md)
- [Maps from spectra of valuation rings](../separated-morphisms/valuation-spectrum-map-classification.md)

## Sources

- [Hartshorne II.4, properness clause of Exercise 4.11(b)](../../../sources/hartshorne-ii-4.md#adopted-exercises)

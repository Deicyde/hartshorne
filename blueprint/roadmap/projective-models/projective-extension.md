---
article_id: af_c7a69237e8196e17b7390436
declaration: theorem
origin: cited
source_units: [chapter-i-section-6-projective-model]
statement: formalized
proof: formalized
lean: Hartshorne.ValuationSpace.existsUnique_projective_extension
---

# Extension to a projective target

Let `X` be an abstract nonsingular curve, `P ∈ X`, and `Y` a projective
variety.  Every morphism `X \ {P} → Y` extends to a unique morphism `X → Y`.
This is Proposition 6.8.  The sole main declaration is
`Hartshorne.ValuationSpace.existsUnique_projective_extension`.

The proof also establishes simultaneous extension from an arbitrary
nonempty open subset, which is what Theorem 6.9 consumes, but the public
headline must retain the source's punctured-curve statement and uniqueness.
Embed `Y` as a closed subvariety of projective space, choose a nonvanishing
coordinate, use the valuation-minimal pivot, and extend the resulting affine
ratios as regular functions near `P`.  Density keeps the value in `Y`, and
Lemma 4.1 gives uniqueness.

## Depends on

- [Abstract nonsingular curves](../curve-normalization/abstract-nonsingular-curve.md)
- [Projective and quasi-projective varieties](../projective-varieties/projective-variety.md)
- [Morphisms](../morphisms/morphism.md)

## Proof depends on

- [Regularity near a valuation](regular-near-valuation.md)
- [A projective coordinate pivot](valuation-projective-pivot.md)
- [Criterion for a morphism to an affine variety](../morphisms/morphism-to-affine-criterion.md)
- [Morphisms agreeing on an open set](../rational-maps/morphism-agreement.md)

## Sources

- [Hartshorne I.6, Proposition 6.8 (pp. 43--44)](../../sources/hartshorne.md#i6-projective-models)

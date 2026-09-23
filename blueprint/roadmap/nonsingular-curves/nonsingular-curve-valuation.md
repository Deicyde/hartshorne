---
article_id: af_82b63943cf8eb3b9f988705c
declaration: def
origin: cited
source_units: [chapter-i-section-6-local-structure]
statement: formalized
lean: Hartshorne.Variety.HasAffineOpenBasis.valuationSubringAt
---

# Nonsingular curve points define discrete valuations

For a nonsingular point `P` on a curve `X`, package the image of its local ring
inside the function field as a valuation subring

`valuationSubringAt P : ValuationSubring X.FunctionField`.

Its underlying subring is `X.localRingRange P`; its fraction field is `K(X)`;
and the corresponding valuation is discrete and trivial on the embedded base
field `k`. This is the precise Lean form of Hartshorne's statement that
`𝒪_{P,X}` is a valuation ring of `K(X)/k`.

The pinned Mathlib can construct the valuation subring from a valuation-ring
structure, but does not yet directly transport discreteness to the associated
valuation. Record the discreteness at the ring/subring level and expose any
valuation-valued corollary that the pinned API supports; do not rely on open PR
#43655.

## Depends on

- [The function field is the fraction field of every local ring](local-ring-fraction-field.md)
- [Local rings of nonsingular curves are DVRs](nonsingular-curve-local-ring-dvr.md)

## Proof depends on

- [Global regular functions are the intersection of the local rings](../morphisms/global-functions/global-regular-intersection-local-rings.md)

## Sources

- [Hartshorne I.6, local rings as valuation rings of `K(Y)/k` (p. 41)](../../sources/hartshorne.md#i6-local-structure-and-point-separation)

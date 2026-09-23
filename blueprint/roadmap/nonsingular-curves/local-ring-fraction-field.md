---
article_id: af_20bb708fcbe056188c33a53a
declaration: theorem
origin: cited
source_units: [chapter-i-section-6-local-structure]
statement: formalized
lean: Hartshorne.Variety.HasAffineOpenBasis.isFractionRing_localRingAt
---

# The function field is the fraction field of every local ring

Let `X` be a variety with an affine-open basis and `P : X`. The canonical
injection

`𝒪_{P,X} →ₐ[k] K(X)`

exhibits `K(X)` as a fraction field of `𝒪_{P,X}`. In particular the local ring
is a domain, and its image is the subalgebra `X.localRingRange P` already used
to state intersections of local rings inside the function field.

Choose an affine open neighbourhood of `P`. Local rings are unchanged by
restriction to that neighbourhood, its function field is canonically `K(X)`,
and in affine coordinates both rings embed in the fraction field of the
coordinate ring. The same pull request should install the supporting
`IsDomain (X.LocalRingAt P)` instance from the injective canonical map.

## Depends on

- [The local ring at a point](../morphisms/local-ring.md)
- [The function field of an arbitrary variety](../morphisms/function-field-abstract.md)
- [Global regular functions are the intersection of the local rings](../morphisms/global-functions/global-regular-intersection-local-rings.md)
- [Open affine sets are a base for the topology](../rational-maps/affine-base.md)

## Proof depends on

- [The local ring is a localisation](../morphisms/local-ring-is-localization.md)
- [The function field is the fraction field](../morphisms/function-field-is-fraction-field.md)
- [Local rings are unchanged on open neighbourhoods](../nonsingular-varieties/local-ring-open-invariance.md)
- [Rational maps and function fields](../rational-maps/rational-map-function-field.md)

## Sources

- [Hartshorne I.6, the local ring of a curve point inside its function field (p. 41)](../../sources/hartshorne.md#i6-local-structure-and-point-separation)

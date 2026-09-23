---
article_id: af_2be48af475bcbe3565ef8435
declaration: theorem
origin: bridged
source_units: [chapter-i-section-6-local-structure]
---

# Dimension of the local ring of a variety

Let `X` be a variety with an affine-open basis and `P : X`. Then

`ringKrullDim (𝒪_{P,X}) = topologicalKrullDim X.carrier`.

This is Theorem 3.2(c), already proved for affine varieties, transported to the
abstract interface needed in §6. Choose an affine open neighbourhood of `P`.
Its local ring is isomorphic to `𝒪_{P,X}`; its dimension equals its coordinate-
ring dimension; and a nonempty open subset of an irreducible space has the same
topological dimension as the ambient variety.

The finite-dimensionality witness should remain explicit so the conclusion can
be rewritten to a natural number. In particular, if `X.IsCurve`, every local
ring has Krull dimension one.

## Depends on

- [The local ring at a point](../morphisms/local-ring.md)
- [Open affine sets are a base for the topology](../rational-maps/affine-base.md)

## Proof depends on

- [The local ring and function field of an affine variety](../morphisms/affine-variety-rings.md)
- [Local rings are unchanged on open neighbourhoods](../nonsingular-varieties/local-ring-open-invariance.md)
- [Dimension of a quasi-affine variety](../affine-varieties/dim-quasi-affine.md)

## Sources

- [Hartshorne I.3, Theorem 3.2(c), and I.6, application to curves (pp. 17, 41)](../../sources/hartshorne.md#i6-local-structure-and-point-separation)

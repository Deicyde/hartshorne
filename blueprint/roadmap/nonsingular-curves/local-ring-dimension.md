---
article_id: af_2be48af475bcbe3565ef8435
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.Variety.HasAffineOpenBasis.ringKrullDim_localRingAt_eq
---

# Dimension of the local ring of a variety

Let $X$ be a variety with an affine-open basis and let $P\in X$. Then

$$\dim \mathcal{O}_{P,X} = \dim X.$$

This extends Theorem 3.2(c) from affine varieties to the setting needed in §6.
Choose an affine open neighbourhood of $P$. Its local ring at $P$ is
isomorphic to $\mathcal{O}_{P,X}$, and the affine theorem identifies its
dimension with that of the coordinate ring. The affine open and the ambient
variety have the same function field, so their dimensions agree.

In particular, every local ring of a curve has Krull dimension one.

## Depends on

- [The local ring at a point](../morphisms/local-ring.md)
- [Open affine sets are a base for the topology](../rational-maps/affine-base.md)

## Proof depends on

- [The local ring and function field of an affine variety](../morphisms/affine-variety-rings.md)
- [Local rings are unchanged on open neighbourhoods](../nonsingular-varieties/local-ring-open-invariance.md)
- [Dimension of a quasi-affine variety](../affine-varieties/dim-quasi-affine.md)
- [Rational maps and function fields](../rational-maps/rational-map-function-field.md)

## Sources

- [Hartshorne I.3, Theorem 3.2(c), and I.6, application to curves (pp. 17, 41)](../../sources/hartshorne.md#i6-local-structure-and-point-separation)

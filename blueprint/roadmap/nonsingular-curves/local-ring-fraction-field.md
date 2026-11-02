---
article_id: af_20bb708fcbe056188c33a53a
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.Variety.HasAffineOpenBasis.isFractionRing_localRingAt
---

# The function field is the fraction field of every local ring

Let $X$ be a variety over $k$ with an affine-open basis and let $P\in X$.
The canonical injection of $k$-algebras

$$\mathcal{O}_{P,X} \hookrightarrow K(X)$$

exhibits $K(X)$ as the fraction field of $\mathcal{O}_{P,X}$. In particular,
the local ring is a domain. Through this injection, it can be regarded as a
subalgebra of the function field.

Choose an affine open neighbourhood of $P$. Restricting to this neighbourhood
preserves the local ring at $P$ and the function field. In affine coordinates,
the local ring is a localization of the coordinate ring, so both have the
same fraction field.

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

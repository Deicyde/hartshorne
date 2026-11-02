---
article_id: af_82b63943cf8eb3b9f988705c
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.Variety.HasAffineOpenBasis.valuationAt Hartshorne.Variety.HasAffineOpenBasis.valuationSubringAt
---

# Nonsingular curve points define discrete valuations

Let $X$ be a curve over $k$ with an affine-open basis, and let $P$ be a
nonsingular point of $X$. The image of the local ring $\mathcal{O}_{P,X}$ in
the function field $K(X)$ is a discrete valuation ring with fraction field
$K(X)$.

The corresponding discrete valuation is trivial on the embedded base field
$k$. Thus $\mathcal{O}_{P,X}$, viewed inside $K(X)$, is a valuation ring of
$K(X)/k$.

## Depends on

- [The function field is the fraction field of every local ring](local-ring-fraction-field.md)
- [Local rings of nonsingular curves are DVRs](nonsingular-curve-local-ring-dvr.md)

## Proof depends on

- [Global regular functions are the intersection of the local rings](../morphisms/global-functions/global-regular-intersection-local-rings.md)

## Sources

- [Hartshorne I.6, local rings as valuation rings of $K(Y)/k$ (p. 41)](../../sources/hartshorne.md#i6-local-structure-and-point-separation)

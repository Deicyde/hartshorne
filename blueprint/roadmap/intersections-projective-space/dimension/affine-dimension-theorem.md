---
article_id: af_e751a901985e442f87371072
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.affine_dimension_theorem
---

# The affine dimension theorem

Let $Y,Z\subseteq\mathbb A^n$ be affine varieties and let $W$ be an
irreducible component of $Y\cap Z$. Then

$$\dim Y+\dim Z\leq\dim W+n.$$

This is Hartshorne's Proposition I.7.1, equivalently
$\dim W\geq\dim Y+\dim Z-n$.

The affine product $Y\times Z$ has dimension $\dim Y+\dim Z$.
Its diagonal section is cut out by at most $n$ equations, so the finite-cut
dimension bound applies. The diagonal homeomorphism identifies its
components with those of $Y\cap Z$ and preserves their dimensions.

## Depends on

- [Dimension of an affine product](affine-product-dimension.md)
- [A finite set of equations lowers component dimension by at most its size](finite-cut-component-dimension.md)
- [The diagonal section of an affine product](affine-diagonal-section.md)

## Sources

- [Hartshorne I.7, Proposition 7.1 (p. 48)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)

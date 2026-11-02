---
article_id: af_c32cfee507fdcd0696b127dd
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.projDim_lt_of_closed_ssubset_isProjVariety Hartshorne.exists_projDim_eq_nat_of_isProjVariety
---

# Proper closed subsets of projective varieties have smaller dimension

Let $Y$ be a projective variety and let $Z\subsetneq Y$ be a closed
subset. Then

$$\dim Z<\dim Y.$$

Adjoining the irreducible closed set $Y$ to a chain inside $Z$ increases
its length by one. The dimension of $Y$ is finite: a nonempty standard
affine chart has a finitely generated coordinate ring of finite Krull
dimension. Thus the chain argument gives a strict dimension drop.

## Depends on

- [Dimension in projective space](../../projective-varieties/projective-dimension.md)
- [Projective and quasi-projective varieties](../../projective-varieties/projective-variety.md)

## Proof depends on

- [Varieties are covered by affine pieces](../../projective-varieties/affine-cover.md)
- [Dimension of the homogeneous coordinate ring](../../projective-varieties/homogeneous-coordinate-ring-dimension.md)
- [Dimension of a topological space and of a ring](../../affine-varieties/dimension.md)
- [Dimension is the dimension of the coordinate ring](../../affine-varieties/dim-eq-coordinate-ring-dim.md)
- [A finitely generated algebra over a field has finite dimension](../../affine-varieties/dim-fg-algebra-finite.md)

## Sources

- [Hartshorne I.7, dimension arguments used in Theorem 7.7 (p. 53)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)

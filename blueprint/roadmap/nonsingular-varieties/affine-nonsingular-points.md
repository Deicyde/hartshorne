---
article_id: af_2136720d3c5831f8df18c545
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.IsAffineNonsingularAt Hartshorne.IsAffineNonsingular
---

# Nonsingular points of an affine variety

Let $Y\subseteq\mathbb A^n$ be an affine variety of dimension $r$.
A point $P\in Y$ is *nonsingular in affine coordinates* if its Jacobian
matrix has rank $n-r$ at $P$.

Equivalently,

$$\operatorname{rank}J(P)+\dim Y=n.$$

The variety is nonsingular if this holds at every point. The intrinsic
Jacobian row space makes the condition independent of a generating family
for $I(Y)$; every finite generating family gives the same matrix rank.

## Depends on

- [Jacobian rank is independent of generators](jacobian-rank-invariance.md)
- [Dimension of a topological space and of a ring](../affine-varieties/dimension.md)

## Proof depends on

- [Dimension is the dimension of the coordinate ring](../affine-varieties/dim-eq-coordinate-ring-dim.md)
- [A finitely generated algebra over a field has finite dimension](../affine-varieties/dim-fg-algebra-finite.md)

## Sources

- [Hartshorne I.5, definition of affine nonsingularity (pp. 31-32)](../../sources/hartshorne.md#i5)

---
article_id: af_2b5eb74d5e0861e7dca01d34
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.dim_eq_ringKrullDim_coordinateRing
---

# Dimension is the dimension of the coordinate ring

For an affine algebraic set $Y$, the dimension of $Y$ as a topological
space equals the Krull dimension of its coordinate ring:

$$\dim Y=\dim A(Y).$$

This is Hartshorne's Proposition I.1.7. Irreducible closed subsets of $Y$
correspond to prime ideals of the polynomial ring containing $I(Y)$, and
hence to prime ideals of $A(Y)$. The correspondence reverses inclusion,
so chains of the same length correspond and their suprema agree.

## Depends on

- [Dimension of a topological space and of a ring](dimension.md)
- [The affine coordinate ring](affine-coordinate-ring.md)

## Proof depends on

- [Algebraic sets and radical ideals](radical-ideal-correspondence.md)
- [Every finitely generated domain is a coordinate ring](coordinate-ring-realization.md)

## Sources

- [Hartshorne I.1, Proposition 1.7 (p. 6)](../../sources/hartshorne.md#i1)

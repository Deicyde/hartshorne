---
article_id: af_a9e57f8d9d634fcf8140cc0b
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.dimAffineSpace_eq Hartshorne.vanishingIdeal_univ
---

# The dimension of affine space

$$\dim\mathbb{A}^n=n.$$

This is Hartshorne's Proposition I.1.9. By
[the coordinate-ring dimension theorem](dim-eq-coordinate-ring-dim.md),
it is enough to compute the Krull dimension of $k[x_1,\ldots,x_n]$.
[Theorem I.1.8A(a)](dim-fg-domain.md) identifies this dimension with the
transcendence degree of $k(x_1,\ldots,x_n)$ over $k$, which is $n$.

## Depends on

- [Dimension is the dimension of the coordinate ring](dim-eq-coordinate-ring-dim.md)
- [Dimension of a finitely generated domain](dim-fg-domain.md)

## Sources

- [Hartshorne I.1, Proposition 1.9 (p. 6)](../../sources/hartshorne.md#i1)

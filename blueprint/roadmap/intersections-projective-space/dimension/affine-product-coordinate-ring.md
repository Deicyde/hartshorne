---
article_id: af_e2b12c96da8249f2a9c75798
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.coordinateRing_affineProductEquiv
---

# The coordinate ring of an affine product

For affine varieties $X\subseteq\mathbb A^m$ and
$Y\subseteq\mathbb A^n$, there is a canonical isomorphism of $k$-algebras

$$A(X\times Y)\cong A(X)\otimes_k A(Y).$$

This is Hartshorne's Exercise I.3.15(b). Tensoring the two coordinate-ring
quotient maps gives a surjective map from the polynomial ring in the two
coordinate blocks. Point evaluations separate the elements of each
coordinate ring and, after choosing a basis in one factor, those of their
tensor product. Its kernel is therefore the vanishing ideal of $X\times Y$.
Quotienting gives the isomorphism. This evaluation argument works for
arbitrary subsets over any field and does not need the Nullstellensatz.

## Depends on

- [Affine products are varieties](affine-product-variety.md)
- [The affine coordinate ring](../../affine-varieties/affine-coordinate-ring.md)

## Sources

- [Hartshorne I.3, Exercise 3.15(b), used in the dimension calculation required by I.7](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)

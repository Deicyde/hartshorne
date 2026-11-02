---
article_id: af_7235a2f155374776b41b4872
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.dim_affineProduct
---

# Dimension of an affine product

If $X\subseteq\mathbb A^m$ and $Y\subseteq\mathbb A^n$ are affine
varieties over an algebraically closed field, then

$$\dim(X\times Y)=\dim X+\dim Y.$$

This is Hartshorne's Exercise I.3.15(d), used in
[Proposition I.7.1](affine-dimension-theorem.md).

The coordinate ring of the product is $A(X)\otimes_k A(Y)$ and is a
domain because the affine product is a variety. Apply the tensor-product
dimension theorem and identify geometric dimensions with coordinate-ring
dimensions.

## Depends on

- [Affine products are varieties](affine-product-variety.md)
- [The coordinate ring of an affine product](affine-product-coordinate-ring.md)
- [Dimension of a tensor product of affine domains](tensor-product-dimension.md)
- [Dimension is the dimension of the coordinate ring](../../affine-varieties/dim-eq-coordinate-ring-dim.md)

## Sources

- [Hartshorne I.3, Exercise 3.15(d), and I.7, proof of Proposition 7.1](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)

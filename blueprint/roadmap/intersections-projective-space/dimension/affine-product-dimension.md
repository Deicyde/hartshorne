---
article_id: af_7235a2f155374776b41b4872
declaration: theorem
origin: cited
source_units: [chapter-i-section-7-main]
statement: formalized
proof: formalized
lean: Hartshorne.dim_affineProduct
---

# Dimension of an affine product

If `X ⊆ 𝔸^σ` and `Y ⊆ 𝔸^τ` are affine varieties over an algebraically closed
field, then

`dim (affineProduct X Y) = dim X + dim Y`.

The sole main declaration is planned as `Hartshorne.dim_affineProduct`.  This
is Exercise I.3.15(d), which Hartshorne uses verbatim in Proposition 7.1.

Pass from all three geometric dimensions to coordinate-ring dimensions.  The
coordinate ring of the product is the tensor product of the coordinate rings,
and it is a domain because the affine product is a variety.  The tensor-product
dimension theorem then gives the equality.

## Depends on

- [Affine products are varieties](affine-product-variety.md)
- [The coordinate ring of an affine product](affine-product-coordinate-ring.md)
- [Dimension of a tensor product of affine domains](tensor-product-dimension.md)
- [Dimension is the dimension of the coordinate ring](../../affine-varieties/dim-eq-coordinate-ring-dim.md)

## Sources

- [Hartshorne I.3, Exercise 3.15(d), and I.7, proof of Proposition 7.1](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)

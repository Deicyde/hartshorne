---
article_id: af_43c075991ef42c98863acc26
declaration: bilinear_map
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.externalProduct Hartshorne.externalProductPoint Hartshorne.closure_externalProductPoint Hartshorne.externalProduct_apply_of_eq_single
---

# External products of cycles

For varieties $X,Y$, send irreducible subvarieties $V \subset X$ and
$W \subset Y$ to the product cycle $[V \times W]$, and extend bilinearly:

$\mathbb{Z}^r(X) \times \mathbb{Z}^s(Y) \to \mathbb{Z}^{r+s}(X \times Y)$.

This operation descends to external products on Chow groups once rational
equivalence is shown compatible with products.

## Depends on

- [Codimension cycles](../cycles/codimension-cycle-group.md)
- [The universal property of a fiber product](../../../schemes/fiber-products/fiber-product-universal-property.md)

## Proof depends on

- [Every finitely generated domain is a coordinate ring](../../../affine-varieties/coordinate-ring-realization.md)
- [Affine products are varieties](../../../intersections-projective-space/dimension/affine-product-variety.md)
- [The coordinate ring of an affine product](../../../intersections-projective-space/dimension/affine-product-coordinate-ring.md)
- [Dimension of a tensor product of affine domains](../../../intersections-projective-space/dimension/tensor-product-dimension.md)
- [Dimension of a finitely generated domain](../../../affine-varieties/dim-fg-domain.md)
- [The dimension formula for a finitely generated domain](../../../affine-varieties/dim-formula-catenary.md)

## Informally uses

- [Products of varieties](../../../rational-maps/product-variety.md)
- [Rational equivalence via normalizations](../cycles/rational-equivalence-via-normalizations.md)

## Sources

- [Hartshorne Appendix A.1, products in A5, pp.426–427](../../../../sources/hartshorne-appendix-a-1-2.md)

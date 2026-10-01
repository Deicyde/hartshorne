---
article_id: af_e2b12c96da8249f2a9c75798
declaration: def
origin: cited
source_units: [chapter-i-section-7-main]
statement: formalized
proof: formalized
lean: Hartshorne.coordinateRing_affineProductEquiv
---

# The coordinate ring of an affine product

For affine varieties `X ⊆ 𝔸^σ` and `Y ⊆ 𝔸^τ`, there is a canonical
`k`-algebra equivalence

`A(X × Y) ≃ₐ[k] A(X) ⊗[k] A(Y)`.

The sole main declaration is planned as
`Hartshorne.coordinateRing_affineProductEquiv`.  This is Exercise I.3.15(b),
adopted as the algebraic input to the dimension assertion in part (d).

Under `MvPolynomial.tensorEquivSum`, tensoring the two quotient maps gives a
surjective map from the polynomial ring on `σ ⊕ τ` to
`A(X) ⊗[k] A(Y)`.  Point evaluations separate each coordinate ring and,
after choosing a basis in one factor, jointly separate their tensor product.
The kernel is therefore exactly the polynomials vanishing on the affine
product.  Quotienting by that kernel gives the displayed equivalence.  This
direct argument works for arbitrary subsets over any field and does not need
the Nullstellensatz.

## Depends on

- [Affine products are varieties](affine-product-variety.md)
- [The affine coordinate ring](../../affine-varieties/affine-coordinate-ring.md)

## Sources

- [Hartshorne I.3, Exercise 3.15(b), used in the dimension calculation required by I.7](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)

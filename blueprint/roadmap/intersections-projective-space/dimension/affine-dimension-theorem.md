---
article_id: af_e751a901985e442f87371072
declaration: theorem
origin: cited
source_units: [chapter-i-section-7-main]
---

# The affine dimension theorem

Let `Y,Z ⊆ 𝔸^σ` be affine varieties and let `W` be an irreducible component of
`Y ∩ Z`.  Then

`dim Y + dim Z ≤ dim W + Nat.card σ`.

The sole main declaration is planned as `Hartshorne.affine_dimension_theorem`.
For `σ = Fin n` and natural dimensions `r,s,t`, this is exactly the
subtraction-free form `r + s ≤ t + n` of Proposition 7.1's
`t ≥ r + s - n`.

Apply the finite-cut dimension theorem to `Y × Z`.  Its dimension is the sum
of the dimensions of the factors; the diagonal is cut out by at most
`Nat.card σ` equations; and the diagonal-section homeomorphism identifies its
components and their dimensions with those of `Y ∩ Z`.

## Depends on

- [Dimension of an affine product](affine-product-dimension.md)
- [A finite set of equations lowers component dimension by at most its size](finite-cut-component-dimension.md)
- [The diagonal section of an affine product](affine-diagonal-section.md)

## Sources

- [Hartshorne I.7, Proposition 7.1 (p. 48)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)

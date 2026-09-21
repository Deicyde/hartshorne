---
article_id: af_dfbfb056049d16cdd33cb367
declaration: theorem
origin: cited
source_units: [chapter-i-section-5-geometry]
statement: formalized
lean: Hartshorne.definingIdealGradientSpace_eq_jacobianRowSpace_of_span_eq Hartshorne.jacobianMatrix_rank_eq_jacobianRank Hartshorne.jacobianMatrix_rank_eq_of_span_eq Hartshorne.exists_fin_jacobianMatrix_rank_eq_jacobianRank
---

# Jacobian rank is independent of generators

For an affine variety `Y ⊆ 𝔸ⁿ` and `P ∈ Y`, define its intrinsic
*Jacobian row space at `P`* to be

`J_P(Y) = span_k {∇f(P) | f ∈ I(Y)} ⊆ kⁿ`,

and define `jacobianRank(Y,P) = dim_k J_P(Y)`. If
`f₁,…,fₜ` is any finite generating family for `I(Y)`, then `J_P(Y)` is
already spanned by the rows

`((∂fᵢ/∂xⱼ)(P))_j`.

Thus `jacobianRank(Y,P)` is the rank of Hartshorne's displayed Jacobian
matrix, and any two finite generating families give the same rank.

For the nontrivial containment, write an arbitrary `f ∈ I(Y)` as
`∑ gᵢ fᵢ`. The product rule and `fᵢ(P)=0` show
`∇f(P)=∑ gᵢ(P)∇fᵢ(P)`. The reverse containment is immediate. The
finite-generation input is available because the polynomial ring has finitely
many variables and is Noetherian.

## Depends on

- [The cotangent space of affine space](ambient-cotangent-space.md)
- [The defining ideal and the local cotangent space](defining-ideal-cotangent-sequence.md)
- [The vanishing ideal](../affine-varieties/vanishing-ideal.md)

## Sources

- [Hartshorne I.5, definition of the Jacobian and generator-independence remark (pp. 31-32)](../../sources/hartshorne.md#i5)

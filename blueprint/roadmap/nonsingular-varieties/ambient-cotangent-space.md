---
article_id: af_3ba438db4aaadf9e7dbd4162
declaration: theorem
origin: cited
source_units: [chapter-i-section-5-geometry]
---

# The cotangent space of affine space

For `P = (a₁,…,aₙ) ∈ 𝔸ⁿ`, let
`𝔫_P = ker(eval_P) ⊆ k[x₁,…,xₙ]`. The derivative map

`θ_P(f) = ((∂f/∂x₁)(P),…,(∂f/∂xₙ)(P))`

vanishes on `𝔫_P²` and induces a linear equivalence

`𝔫_P/𝔫_P² ≃ₗ[k] kⁿ`.

Under this equivalence the class of `xᵢ − aᵢ` is the `i`th standard basis
vector, and the class of any `f ∈ 𝔫_P` is sent to its gradient at `P`.
This is Hartshorne's map `θ'` in the proof of Theorem 5.1.

Mathlib supplies `MvPolynomial.pderiv`, the Leibniz rule, and the canonical
basis for polynomial Kähler differentials. In particular,
`Algebra.Generators.cotangentSpaceBasis` and
`Algebra.Generators.cotangentSpaceBasis_repr_one_tmul` are close to the desired
coordinate calculation. The missing project bridge is the point-evaluation
formulation and its identification with `Ideal.Cotangent 𝔫_P`; proving it
directly on the generators `xᵢ − aᵢ` also keeps the
characteristic-independent argument visible.

## Depends on

No project-local prerequisites.

## Sources

- [Hartshorne I.5, proof of Theorem 5.1 (p. 32)](../../sources/hartshorne.md#i5)

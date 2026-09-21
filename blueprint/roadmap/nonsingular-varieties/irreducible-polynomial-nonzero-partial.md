---
article_id: af_4c4647da1060e1836668271e
declaration: theorem
origin: bridged
source_units: [chapter-i-section-5-geometry]
statement: formalized
lean: Hartshorne.exists_pderiv_ne_zero_of_irreducible
---

# An irreducible polynomial has a nonzero partial derivative

Let `k` be algebraically closed and let `f ∈ k[x₁,…,xₙ]` be irreducible
and nonconstant. Then `∂f/∂xᵢ ≠ 0` for at least one `i`.

In characteristic zero, choose a variable occurring with positive exponent in
`f`; differentiation cannot kill every such term. In characteristic `p > 0`,
vanishing of every partial says that every exponent in every monomial of `f`
is divisible by `p`. Algebraic closedness makes Frobenius surjective on
coefficients, so coefficientwise `p`th roots produce a polynomial `g` with
`f = gᵖ`. Since `f` is nonconstant, `g` is a nonunit, contradicting the
irreducibility of `f`.

The positive-characteristic clause is essential: over a nonperfect field a
polynomial can have zero gradient without being a polynomial `p`th power over
that field. Mathlib's `MvPolynomial.map_frobenius_expand` and the
`PerfectField` instance supplied by algebraic closedness are the closest
existing ingredients; no theorem packaging this multivariable conclusion was
found in the pinned checkout.

## Depends on

No project-local prerequisites.

## Sources

- [Hartshorne I.5, final paragraph of the proof of Theorem 5.3 (p. 33)](../../sources/hartshorne.md#i5)

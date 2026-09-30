---
article_id: af_e1172cc5a288e77e36d14b58
declaration: definition
origin: cited
source_units: [chapter-i-section-7-main]
---

# Numerical polynomials

A polynomial `P ∈ ℚ[z]` is numerical when `P(n)` is an integer for every
sufficiently large integer `n`. The sole main declaration is planned as
`Hartshorne.IsNumericalPolynomial`.

Represent eventuality with the `atTop` filter on `ℤ`, and represent
integer-valuedness by the existence of `m : ℤ` whose image in `ℚ` is the
evaluation. This records Hartshorne's quantifier `n ≫ 0` literally and leaves
negative evaluations as the conclusion of Proposition 7.3(a), not part of the
definition.

The supporting binomial polynomial

`numericalBinomial r = (r!)⁻¹ • Polynomial.descPochhammer ℚ r`

represents `z(z-1)⋯(z-r+1)/r!`. Pinned Mathlib supplies
`Polynomial.descPochhammer`, `Ring.choose`, and their evaluation identity, but
does not define Hartshorne's numerical-polynomial predicate.

## Depends on

No project-local statement prerequisites.

## Sources

- [Hartshorne I.7, definition before Proposition 7.3 (p. 49)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)

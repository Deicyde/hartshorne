---
article_id: af_8f4533c12c01e96df3437796
declaration: theorem
origin: cited
source_units: [chapter-i-section-7-main]
---

# Numerical polynomials have integral binomial expansions

If `P ∈ ℚ[z]` is numerical, then there is a finitely supported family of
integers `c_r` such that

`P = ∑ r, c_r · numericalBinomial r`.

Conversely, every such integral combination is numerical. The sole main
declaration is planned as
`Hartshorne.isNumericalPolynomial_iff_exists_binomialExpansion`; it packages
Proposition 7.3(a) in a support-bounded form and yields Hartshorne's consequence
that `P(n)` is integral for every `n : ℤ`, not merely for large `n`.

The proof is by induction on `P.natDegree`. Forward difference sends the
degree-`r` binomial polynomial to the degree-`r-1` one, so induction makes all
coefficients except the constant integral; one sufficiently large integral
evaluation then makes the last coefficient integral. The result should also
record the top-coefficient identity
`r! · P.leadingCoeff = c_r`, since the definition and positivity of
projective degree use it later.

Pinned Mathlib supplies the Pochhammer degree, leading-coefficient, and
integer-evaluation lemmas, but not the integral-basis characterization.

## Depends on

- [Numerical polynomials](numerical-polynomial.md)

## Sources

- [Hartshorne I.7, Proposition 7.3(a) (pp. 49–50)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)

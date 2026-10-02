---
article_id: af_0f9b546532f105d1551796cb
declaration: theorem
origin: bridged
source_units: [chapter-i-section-7-main]
statement: formalized
proof: formalized
lean: Hartshorne.gradedHilbertPolynomial_coeff_eq_sum_minimalPrimes
---

# The leading Hilbert coefficient is a sum over minimal primes

Let `M` be a finite integer-graded module over `S = k[x₀,…,xₙ]`, and suppose
its projective support has dimension `r`. The coefficient of `z^r` in `P_M`
is

`(1/r!) · ∑ p, μ_p(M) · projectiveDegree (Z(p))`,

where the sum ranges over the minimal primes of `Ann M` whose projective zero
sets have dimension `r`. Terms of smaller dimension do not affect the leading
coefficient.

This isolates the filtration calculation in Hartshorne's proof of Theorem 7.7.
The occurrence-count theorem converts repeated prime factors into localized
module lengths; twists leave leading coefficients unchanged.

## Depends on

- [Multiplicity in a graded prime filtration](../hilbert/graded-multiplicity.md)
- [Minimal primes in a graded prime filtration](../hilbert/prime-filtration-support.md)
- [Hilbert–Serre](../hilbert/hilbert-serre.md)
- [Hilbert polynomials and degrees of projective algebraic sets](../hilbert/projective-hilbert-polynomial-and-degree.md)

## Sources

- [Hartshorne I.7, proof of Theorem 7.7 (p. 53)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)

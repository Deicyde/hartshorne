---
article_id: af_a52cb991e62958c97fc00e45
declaration: theorem
origin: cited
source_units: [chapter-i-section-7-main]
---

# Hilbert–Serre

Let `M` be a finite integer-graded module over
`S = k[x₀,…,xₙ]`. There is a unique polynomial `P_M ∈ ℚ[z]` such that

`φ_M(d) = P_M(d)`

for every sufficiently large integer `d`. It is numerical, and its degree,
with the zero polynomial assigned degree `-1`, is

`dim Z(Ann M) ⊆ ℙⁿ`.

The sole main declaration is planned as `Hartshorne.hilbertSerre`. A supporting
canonical choice `Hartshorne.gradedHilbertPolynomial` exposes its unique
polynomial to later definitions. Represent the common degree type by
`WithBot ℕ∞`: map a nonzero polynomial to its natural degree and the zero
polynomial to `⊥`. This matches the project's `projDim` convention without an
ad hoc cast between `Polynomial.degree : WithBot ℕ` and topological
dimension.

Apply Hilbert-function additivity along a graded prime filtration and sum the
polynomials of its shifted prime quotients. The filtration-support theorem
identifies `Z(Ann M)` with the union of the factor supports. Factors of maximal
dimension have positive leading coefficient, so their contributions cannot
cancel; lower-dimensional factors do not change the degree. Uniqueness follows
because two rational polynomials agreeing at all sufficiently large integers
agree on an infinite set.

Pinned Mathlib's `Polynomial.hilbertPoly` proves the eventual polynomial for a
power series already presented as `p/(1-X)^d`; that file explicitly leaves
Hilbert polynomials of finite graded modules as a TODO, so it is supporting
prior art rather than an exact match.

## Depends on

- [Numerical polynomials have integral binomial expansions](numerical-binomial-expansion.md)
- [Homogeneous annihilators and cyclic modules](graded-annihilator.md)
- [Graded prime filtrations](graded-prime-filtration.md)
- [Minimal primes in a graded prime filtration](prime-filtration-support.md)
- [The Hilbert function](hilbert-function.md)
- [Hilbert polynomials of shifted prime quotients](hilbert-polynomial-prime-quotient.md)

## Proof depends on

- [The projective dimension theorem](../dimension/projective-dimension-theorem.md)

## Sources

- [Hartshorne I.7, Theorem 7.5 and its proof (pp. 51–52)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)

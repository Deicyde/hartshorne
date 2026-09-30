---
article_id: af_c6af33de69690ddc1dd4ade6
declaration: theorem
origin: bridged
source_units: [chapter-i-section-7-main]
---

# Hilbert polynomials of shifted prime quotients

Let `p` be a homogeneous prime ideal of `S = k[x₀,…,xₙ]` and let
`l : ℤ`. There is a unique numerical polynomial `P ∈ ℚ[z]` whose value at
every sufficiently large integer `d` is the Hilbert function of `(S/p)(l)`.
If `Z(p)` is empty, then `P = 0`. If `projDim Z(p) = r`, then `P ≠ 0`,
`P.natDegree = r`, and its leading coefficient is positive. The sole main
declaration is planned as
`Hartshorne.existsUnique_hilbertPolynomial_primeQuotient`.

For the empty case, primeness and the projective ideal correspondence force
`p` to be the irrelevant ideal, so positive pieces vanish. Otherwise choose a
variable `x_i ∉ p`. Multiplication by `x_i` is injective on `S/p`, and its
graded cokernel is `S/(p+(x_i))`. Degreewise exactness gives the finite
difference of Hilbert functions. Every irreducible component of
`Z(p) ∩ Z(x_i)` has dimension exactly one less than `Z(p)`: the projective
dimension theorem supplies the lower bound, while properness of the
hyperplane section supplies the upper bound. Induction on dimension and
discrete antidifferentiation then give the asserted polynomial and degree.

This is the prime-factor case inside Hartshorne's proof of Theorem 7.5, isolated
so the general finite module can be reconstructed from its graded prime
filtration.

## Depends on

- [Discrete antidifferentiation of a numerical polynomial](numerical-antidifference.md)
- [The integer grading on a polynomial ring](integer-polynomial-grading.md)
- [Integer-graded module twists](graded-module-twists.md)
- [The Hilbert function](hilbert-function.md)

## Proof depends on

- [The projective dimension theorem](../dimension/projective-dimension-theorem.md)
- [Algebraic sets and homogeneous radical ideals](../../projective-varieties/homogeneous-ideal-correspondence.md)

## Sources

- [Hartshorne I.7, prime-quotient induction in the proof of Theorem 7.5 (p. 51)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)

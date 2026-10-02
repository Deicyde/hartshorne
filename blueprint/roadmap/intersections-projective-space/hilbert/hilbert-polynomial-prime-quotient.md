---
article_id: af_c6af33de69690ddc1dd4ade6
declaration: theorem
origin: bridged
source_units: [chapter-i-section-7-main]
statement: formalized
proof: formalized
lean: Hartshorne.existsUnique_hilbertPolynomial_primeQuotient
---

# Hilbert polynomials of shifted prime quotients

Let `p` be a homogeneous prime ideal of `S = k[x₀,…,xₙ]` and let
`l : ℤ`. There is a unique numerical polynomial `P ∈ ℚ[z]` whose value at
every sufficiently large integer `d` is the Hilbert function of `(S/p)(l)`.
If `Z(p)` is empty, then `P = 0`. If `projDim Z(p) = r`, then `P ≠ 0`,
`P.natDegree = r`, and its leading coefficient is positive. The sole main
declaration is planned as
`Hartshorne.existsUnique_hilbertPolynomial_primeQuotient`.

Apply Hilbert–Serre to the finite graded module `(S/p)(l)`. Twisting does not
change its annihilator, so the homogeneous ideal correspondence identifies its
projective support with `Z(p)`. Hilbert–Serre therefore supplies the unique
numerical polynomial, gives zero in the empty case, and identifies its degree
with `projDim Z(p)` otherwise. In the nonempty case the polynomial is nonzero;
because its values are the eventually nonnegative Hilbert-function values, its
leading coefficient is positive. The twist merely translates the eventual
polynomial's argument and does not change its degree or leading coefficient.

This records the shifted-prime specialization of Hilbert–Serre as a named API
corollary. The hyperplane-section induction belongs in the simultaneous proof
of Hilbert–Serre: `p+(x_i)` need not be prime or radical, so its quotient must
be handled by the induction hypothesis for arbitrary finite graded modules.

## Depends on

- [Hilbert–Serre](hilbert-serre.md)
- [Homogeneous annihilators and cyclic modules](graded-annihilator.md)
- [The integer grading on a polynomial ring](integer-polynomial-grading.md)
- [Integer-graded module twists](graded-module-twists.md)
- [The Hilbert function](hilbert-function.md)

## Proof depends on

- [Algebraic sets and homogeneous radical ideals](../../projective-varieties/homogeneous-ideal-correspondence.md)

## Sources

- [Hartshorne I.7, prime-quotient induction in the proof of Theorem 7.5 (p. 51)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)

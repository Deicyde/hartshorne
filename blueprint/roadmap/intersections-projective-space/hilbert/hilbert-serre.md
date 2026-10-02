---
article_id: af_a52cb991e62958c97fc00e45
declaration: theorem
origin: cited
source_units: [chapter-i-section-7-main]
statement: formalized
proof: formalized
lean: Hartshorne.hilbertSerre Hartshorne.gradedHilbertPolynomial
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

Prove the result simultaneously for all finite graded modules by strong
induction on the dimension of their projective support, strengthening the
induction claim with positivity of the leading coefficient whenever the
support is nonempty. Apply Hilbert-function additivity along a graded prime
filtration. A factor whose support has smaller dimension is covered directly
by the induction hypothesis. For a
maximal-dimensional shifted prime factor `(S/p)(l)`, choose a variable
`x_i ∉ p`. Multiplication by `x_i`, viewed as a degree-zero map from the
correspondingly shifted source, is injective and has cokernel
`(S/(p+(x_i)))(l)`. Its projective support has smaller dimension (or is empty
in the zero-dimensional case). Crucially, `p+(x_i)` need not be prime or
radical; the induction hypothesis applies because the cokernel is an arbitrary
finite graded module. Degreewise exactness identifies its Hilbert function
with the finite difference of the prime factor's Hilbert function, and
discrete antidifferentiation produces the required numerical polynomial.

The empty-support case starts the induction. For a zero-dimensional nonempty
prime support, the cokernel has empty support, so antidifferentiation gives an
eventual constant. It is positive: `x_i ∉ p` and primeness imply
`x_i^d ∉ p` for every `d`, hence the large-degree pieces of `S/p` do not
vanish. This also supplies the positivity base case for the strengthened
induction.

Sum the factor polynomials to obtain the polynomial for `M`. The
filtration-support theorem identifies `Z(Ann M)` with the union of the factor
supports. Maximal-dimensional prime factors have positive leading coefficient,
so their contributions cannot cancel; lower-dimensional factors do not change
the degree. Uniqueness follows because two rational polynomials agreeing at all
sufficiently large integers agree on an infinite set.

Pinned Mathlib's `Polynomial.hilbertPoly` proves the eventual polynomial for a
power series already presented as `p/(1-X)^d`; that file explicitly leaves
Hilbert polynomials of finite graded modules as a TODO, so it is supporting
prior art rather than an exact match.

## Depends on

- [Numerical polynomials have integral binomial expansions](numerical-binomial-expansion.md)
- [Discrete antidifferentiation of a numerical polynomial](numerical-antidifference.md)
- [Homogeneous annihilators and cyclic modules](graded-annihilator.md)
- [Graded prime filtrations](graded-prime-filtration.md)
- [Minimal primes in a graded prime filtration](prime-filtration-support.md)
- [The Hilbert function](hilbert-function.md)

## Proof depends on

- [The projective dimension theorem](../dimension/projective-dimension-theorem.md)
- [Projective varieties of complementary dimension meet](../dimension/projective-intersection-nonempty.md)
- [Projective codimension one is a hypersurface](../bezout/projective-codimension-one-hypersurface.md)
- [Algebraic sets and homogeneous radical ideals](../../projective-varieties/homogeneous-ideal-correspondence.md)

## Sources

- [Hartshorne I.7, Theorem 7.5 and its proof (pp. 51–52)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)

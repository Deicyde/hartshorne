---
article_id: af_ca2bfce28489b72dde40649c
declaration: theorem
origin: cited
source_units: [chapter-i-section-7-main]
statement: formalized
proof: formalized
lean: Hartshorne.exists_isNumericalPolynomial_eventuallyEq_of_diff
---

# Discrete antidifferentiation of a numerical polynomial

Let `f : ℤ → ℤ`. If a numerical polynomial `Q ∈ ℚ[z]` satisfies

`f(n+1) - f(n) = Q(n)`

for all sufficiently large `n`, then there is a numerical polynomial `P` such
that `f(n) = P(n)` for all sufficiently large `n`. The sole main declaration
is planned as `Hartshorne.exists_isNumericalPolynomial_eventuallyEq_of_diff`.

Expand `Q` in the integral binomial basis and raise every basis index by one;
Pascal's identity makes the forward difference of the resulting polynomial
equal to `Q`. The remaining difference `f-P` is eventually constant, which is
absorbed into the degree-zero coefficient. Record as supporting consequences
that antidifferentiation raises the degree by one when `Q ≠ 0` and divides
its leading coefficient by the new degree; Hilbert–Serre needs those facts to
identify dimension, not merely eventual polynomiality.

## Depends on

- [Numerical polynomials](numerical-polynomial.md)

## Proof depends on

- [Numerical polynomials have integral binomial expansions](numerical-binomial-expansion.md)

## Sources

- [Hartshorne I.7, Proposition 7.3(b) (p. 50)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)

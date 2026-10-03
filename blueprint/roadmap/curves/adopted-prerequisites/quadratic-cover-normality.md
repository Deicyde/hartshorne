---
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-6-7]
---

# Normality of square-root covers

Let `k` be a field of characteristic different from two, let
`f in k[x_1,...,x_n]` be nonconstant and squarefree, and set

`A = k[x_1,...,x_n,z] / (z^2-f)`.

Then `A` is an integrally closed domain. More precisely, it is the integral
closure of `k[x_1,...,x_n]` in the quadratic extension obtained by adjoining
a square root of `f`.

## Depends on

No project-local prerequisites.

## Proof depends on

- Write an element of the quadratic function-field extension as `g+h*z` and
  use its trace and norm to show that integrality forces polynomial
  coefficients; squarefreeness excludes denominator valuations.

## Sources

- [Hartshorne II.6, Exercise 6.4, p.147](../../../sources/hartshorne-ii-6.md#adopted-exercises-and-later-use-evidence)

---
declaration: theorem
origin: cited
source_units: [chapter-iv-sections-1-2]
---

# Genus-two curves from six branch points

Let `k` be algebraically closed of characteristic different from two, and let
`a_1,...,a_6` be distinct elements of `k`. For the quadratic extension

`k(x)(z) / k(x)`,  `z^2 = product_i (x-a_i)`,

let `X` be its nonsingular projective curve model. Then `X` has genus two,
the induced degree-two morphism `X -> P^1_k` is ramified exactly over the six
points `x=a_i`, and this morphism is the canonical double cover.

## Depends on

- [Normality of square-root covers](../adopted-prerequisites/quadratic-cover-normality.md)
- [Nonsingular projective models of function fields](../../projective-models/function-field-projective-model.md)
- [The canonical double cover of a genus-two curve](genus-two-canonical-double-cover.md)
- [Riemann–Hurwitz](../ramification/riemann-hurwitz.md)

## Proof depends on

- The valuation of `product_i (x-a_i)` at each finite point and at infinity
  determines the six ramification points.
- Hurwitz's formula computes the genus.

## Sources

- [Hartshorne IV.2, Exercise 2.2(b), p.304](../../../sources/hartshorne-iv-2.md#exercise-disposition-pp304306)
- [Hartshorne II.6, Exercise 6.4](../../../sources/hartshorne-ii-6.md#excluded-exercises-and-wider-clauses)

---
article_id: af_d9fed0b1efd863e463100dd1
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-6-7]
---

# Degree of a pulled-back curve divisor

Let `f : X → Y` be a finite morphism of nonsingular curves over an
algebraically closed field. For every divisor `D` on `Y`, prove

`deg(f*D) = deg(f) * deg(D)`.

It suffices to treat one closed point `Q`. Localizing the integral closure
above `Q`, compare the dimension of `A'/tA'` with the sum of the orders of a
local parameter at the points above `Q`.

## Depends on

- [Pullback of divisors along finite curve morphisms](finite-curve-divisor-pullback.md)

## Proof depends on

- Finite torsion-free modules over a DVR are free.
- Chinese remaindering over the finitely many primes above `Q`.
- `Ideal.sum_ramification_inertia_eq_finrank`; residue degrees are one over
  the algebraically closed ground field.

## Sources

- [Hartshorne II.6, Proposition 6.9 on printed p.138](../../../../sources/hartshorne-ii-6.md#divisors-on-curves)

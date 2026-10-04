---
article_id: af_cdbea3a99cad059dae2102b0
declaration: theorem
origin: cited
source_units: [chapter-iv-sections-1-2]
---

# The Riemann–Roch theorem

Let `D` be a divisor on a Chapter IV curve `X` of genus `g`, and let `K` be a
canonical divisor. Then

`l(D) - l(K-D) = deg D + 1 - g`.

The equality is in the integers, even though each `l` is a natural-number
dimension.

## Depends on

- [Divisor sections and complete linear systems](curve-divisor-sections.md)
- [Differentials and canonical divisors on a curve](curve-differentials-canonical-divisor.md)
- [Euler characteristic and divisor degree](curve-euler-characteristic-degree.md)
- [Vector-bundle Serre duality](../../cohomology/serre-duality/projective-duality/vector-bundle-serre-duality.md)

## Proof depends on

- Serre duality identifies `H^1(X,O_X(D))` with the dual of
  `H^0(X,omega_X tensor O_X(-D))`, which is `H^0(X,O_X(K-D))` after choosing
  the canonical divisor.

## Sources

- [Hartshorne IV.1, Theorem 1.3, pp.295–296](../../../sources/hartshorne-iv-1.md#canonical-divisors-and-riemannroch-printed-pp295296)
- [Serre and Fulton alternative proofs; Stacks tag 0BS6](../../../sources/hartshorne-iv-1.md#canonical-divisors-and-riemannroch-printed-pp295296)

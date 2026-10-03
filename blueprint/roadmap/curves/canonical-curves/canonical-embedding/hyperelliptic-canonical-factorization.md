---
declaration: theorem
origin: cited
source_units: [chapter-iv-sections-5-6]
---

# The hyperelliptic canonical map factors through a rational normal curve

Let `X` be hyperelliptic of genus `g>=2` and choose a `g^1_2` with morphism
`f_0 : X -> P^1`. The canonical morphism factors as `f_0` followed by the
`(g-1)`-uple embedding

`P^1 -> P^(g-1)`.

It has degree two onto a nonsingular rational normal curve of degree `g-1`.

## Depends on

- [The canonical system is basepoint-free](canonical-system-basepoint-free.md)
- [Hyperelliptic curves and degree-two linear systems](hyperelliptic-linear-series-criterion.md)
- [The dimension bound for an effective divisor](../../riemann-roch/effective-divisor-linear-system-dimension-bound.md)
- [Minimal-degree curves are rational normal](../../projective-embeddings/exercises/rational-normal-curve-minimal-degree.md)

## Proof depends on

- The canonical map collapses every pair in the chosen pencil, so is not
  birational. Normalize its image and compare degree and linear-system
  dimension; equality in the curve dimension bound forces genus zero and the
  complete degree-`g-1` system on `P^1`.

## Sources

- [Hartshorne IV.5, first part of Proposition 5.3, pp.342–343](../../../../sources/hartshorne-iv-5.md)

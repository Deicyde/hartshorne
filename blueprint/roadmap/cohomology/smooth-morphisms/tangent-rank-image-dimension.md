---
declaration: theorem
origin: cited
source_units: [chapter-iii-section-10]
---

# The tangent-rank image-dimension bound

Let `f : X -> Y` be a morphism of finite-type schemes over an algebraically
closed field of characteristic zero. For the closed-point subset

`X_r = {x | rank(Tf_x) <= r}`,

the closure of `f(X_r)` has dimension at most `r`.

## Depends on

- [The Zariski tangent map](zariski-tangent-map.md)
- [Tangent-rank degeneracy loci](tangent-rank-locus-stratification.md)
- [Dominant maps are generically smooth on the source in characteristic zero](dominant-char-zero-generically-smooth-on-source.md)
- [Dimension of a scheme](../../schemes/subschemes-and-dimension/scheme-dimension.md)

## Proof depends on

- Apply generic smoothness to the reductions of the irreducible rank-locus
  components and their image closures, using the dense smooth strata supplied
  by the preceding bridge.
- At a smooth closed point, tangent dimension bounds the local dimension, and
  tangent maps for locally closed immersions are injective.

## Sources

- [Hartshorne III.10, Proposition 10.6, p.272](../../../sources/hartshorne-iii-10.md#characteristic-zero-generic-smoothness-pp271272)

---
declaration: theorem
origin: bridged
source_units: [chapter-iii-section-10]
---

# Constructible tangent-rank strata

Let `f : X -> Y` be a morphism of finite-type schemes over an algebraically
closed field. For every integer `r`, the closed-point subset

`rank(Tf_x) <= r`

is constructible. Produce a finite stratification of `X` by locally closed
reduced subschemes on which `X`, the relevant stratum of `Y`, and the
cotangent presentations are nonsingular and the rank is constant. Every
irreducible component of the closure of the rank subset contains a dense
irreducible stratum, and closed points remain dense on that stratum and its
image closure. This supplies the dense-point selection used in the
image-dimension argument without pretending that the rank subset is globally
a determinantal closed subscheme.

## Depends on

- [The Zariski tangent map](zariski-tangent-map.md)
- [The dense nonsingular locus](../../schemes/differentials/scheme-differentials/dense-nonsingular-locus.md)

## Proof depends on

- Generic freeness and flattening stratifications for the coherent cotangent
  presentations, followed by local matrix-minor rank strata.
- Noetherian induction to obtain finitely many locally closed strata and
  Chevalley constructibility for their images.

## Sources

- [Hartshorne III.10, rank loci in Proposition 10.6, p.272](../../../sources/hartshorne-iii-10.md#characteristic-zero-generic-smoothness-pp271272)

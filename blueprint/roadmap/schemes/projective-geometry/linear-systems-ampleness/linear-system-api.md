---
article_id: af_72a1a080625f60e38ac74daf
declaration: def
origin: cited
source_units: [chapter-ii-sections-6-7]
---

# Linear systems

Package complete linear systems, linear subsystems, their projective
dimensions, base points, and the trace of a system along a closed immersion
`i : Y -> X` of nonsingular projective varieties. The representation is a
finite-dimensional subspace of global sections modulo nonzero scalars, with
the corresponding effective divisors exposed by the API.

Geometrically, the trace contains `D.Y` only for divisors `D` in the system
whose support does not contain `Y`; it is the system obtained from the images
of the sections under `Gamma(X,L) -> Gamma(Y,i^*L)`. No intersection divisor
is assigned when `Y` lies in the support of `D`.

## Depends on

- [Divisors of invertible-sheaf sections](divisor-of-invertible-section.md)
- [Finite-dimensional projective global sections](../../projective-sheaves/projective-global-sections-finite.md)
- [Ambient hypersurfaces cut divisors](../../divisors/divisor-exercises/projective-intersection-divisor.md)

## Proof depends on

- Pullback of the associated invertible sheaf and restriction of sections
  along the closed immersion defining a trace.

## Sources

- [Hartshorne II.7, linear-system and trace definitions (pp.157–158)](../../../../sources/hartshorne-ii-7.md#morphisms-ampleness-and-linear-systems)

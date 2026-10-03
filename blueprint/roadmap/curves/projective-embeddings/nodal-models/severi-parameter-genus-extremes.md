---
declaration: theorem
origin: cited
source_units: [chapter-iv-section-3]
---

# Severi parameters, genus, and the extreme cases

For `d >= 1`, degree-`d` plane curves are parametrized by a projective space of dimension
`d*(d+3)/2`. The irreducible curves with exactly `r` ordinary nodes and no
other singularities form a locally closed Severi locus `V_(d,r)`. For every
member with normalization genus `g`,

`g = (d-1)*(d-2)/2 - r`.

Hence `0 <= r <= (d-1)*(d-2)/2`. Both extremes are nonempty: smooth
irreducible degree-`d` curves give `r=0`, and a rational normal curve of
degree `d`, projected generically to the plane, gives the maximal value.

## Depends on

- [Every curve has a birational nodal plane model](birational-nodal-plane-model.md)
- [Minimal-degree curves are rational normal](../exercises/rational-normal-curve-minimal-degree.md)
- [One projection lowers the ambient dimension](../linear-series/projection-embedding-one-step.md)
- [Embedded degree equals divisor degree](../linear-series/embedded-curve-degree-compatibility.md)
- [Nodes and ordinary cusps have defect one](../../riemann-roch/node-cusp-delta-one.md)
- [Arithmetic genus under normalization](../../riemann-roch/arithmetic-genus-normalization-formula.md)
- [Smooth hypersurfaces form a dense open family](../../../schemes/differentials/canonical-bertini/smooth-hypersurfaces-dense.md)

## Proof depends on

- The space of nonzero degree-`d` ternary forms modulo scalars has the stated
  dimension, and the ordinary-node/no-other-singularity condition is locally
  closed in the universal plane curve.
- The rational normal curve has pullback `O(1)=O_(P^1)(d)`, so its birational
  nodal plane projection still has degree `d`.

## Sources

- [Hartshorne IV.3, Remark 3.11.1, pp.314–315](../../../../sources/hartshorne-iv-3.md#severi-loci-printed-pp314315)

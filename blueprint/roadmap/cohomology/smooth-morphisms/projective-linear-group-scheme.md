---
declaration: structure
origin: bridged
source_units: [chapter-iii-section-10]
not_ready: true
---

# The projective linear group scheme

Construct `PGL(n+1)` over a field `k` as a smooth finite-type group object over
`Spec k`. Equip it with the universal algebraic action on projective space and
the contragredient action on the dual projective space of hyperplanes, and
identify the induced actions on field-valued points with the usual projective
linear actions.

Mathlib's abstract group `Matrix.ProjGenLinGroup` and pointwise action do not
provide this scheme-level group object or its action morphisms. This is the
single unresolved representation root for the III.10 Bertini branch.

## Depends on

- [Algebraic group actions and homogeneous spaces](homogeneous-space-api.md)
- [Projective space over a ring](../../schemes/projective-spectrum/projective-space-over-ring.md)
- [Smooth relative-dimension calculus](criteria/smooth-relative-dimension-calculus.md)

## Sources

- [Hartshorne III.10, Example 10.7.2 and Corollary 10.9, pp.273–275](../../../sources/hartshorne-iii-10.md#homogeneous-spaces-kleiman-and-bertini-pp272275)

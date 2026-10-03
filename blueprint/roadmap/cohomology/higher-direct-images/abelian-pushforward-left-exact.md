---
declaration: instance
origin: cited
source_units: [chapter-iii-sections-8-9]
---

# Abelian-sheaf pushforward is left exact

For a continuous map `f : X -> Y`, the direct-image functor on abelian
sheaves preserves finite limits and is therefore additive and left exact.

The unique result is the `PreservesFiniteLimits` interface needed to apply
`Functor.rightDerivedZeroIsoSelf`. The proof is source-shaped: direct image
is right adjoint to inverse image, so it preserves all limits that exist.
Pinned Mathlib supplies the adjunction and the generic preservation theorem,
but does not package this specialization as the higher-direct-image
interface used here.

## Depends on

- [Inverse image is left adjoint to direct image](../../schemes/sheaf-functors/inverse-direct-adjunction.md)
- [Sheaves of abelian groups](../../schemes/sheaves/sheaves-of-abelian-groups.md)

## Sources

- [Hartshorne III.8, definition and the left exactness of direct image, printed p.250](../../../sources/hartshorne-iii-8.md#definition-and-local-description-printed-pp-250251)

---
article_id: af_d74fadfd8da94d1da7c414c0
declaration: theorem
origin: cited
source_units: [chapter-iii-sections-8-9]
---

# Flasque sheaves have no positive higher direct images

If `F` is a flasque abelian sheaf on `X`, then for every continuous map
`f : X -> Y` and every `i>0`, the sheaf `R^i f_* F` is zero.

The unique main result is this vanishing. Pinned Mathlib has the definition
of flasqueness and proves that pushforward preserves it, but does not supply
this higher-direct-image consequence.

## Depends on

- [Higher direct images of abelian sheaves](higher-direct-images.md)

## Proof depends on

- [The local cohomology presheaf formula](local-cohomology-presheaf.md)
- [Flasque sheaves are acyclic](../sheaf-cohomology/flasque-sheaf-acyclic.md)
- Restriction of a flasque sheaf to an open subset is flasque.

## Sources

- [Hartshorne III.8, Corollary 8.3, printed p.251](../../../sources/hartshorne-iii-8.md#definition-and-local-description-printed-pp-250251)

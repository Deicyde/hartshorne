---
declaration: isomorphism
origin: cited
source_units: [chapter-iii-sections-8-9]
---

# Restriction of higher direct images to an open base

Let `j : V -> Y` be an open immersion, let `f' : f^{-1}(V) -> V` be the
restricted map, and let `F` be an abelian sheaf on `X`. For every `i`, prove
the natural isomorphism

`(R^i f_* F)|_V ~= R^i f'_* (F|_{f^{-1}(V)})`.

This is Corollary 8.2. Its unique main result includes naturality in `F` and
compatibility with nested open subsets.

## Depends on

- [Higher direct images of abelian sheaves](higher-direct-images.md)
- [Restriction and stalks](../../schemes/sheaf-functors/restriction-stalk.md)

## Proof depends on

- [The local cohomology presheaf formula](local-cohomology-presheaf.md)
- Preimages of opens under the restricted map agree with their preimages
  under `f`.

## Sources

- [Hartshorne III.8, Corollary 8.2, printed p.251](../../../sources/hartshorne-iii-8.md#definition-and-local-description-printed-pp-250251)

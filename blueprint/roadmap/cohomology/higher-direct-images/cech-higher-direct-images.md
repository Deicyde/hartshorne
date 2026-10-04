---
article_id: af_8d78c10a97777829b9f0345f
declaration: isomorphism
origin: cited
source_units: [chapter-iii-sections-8-9]
---

# Čech complexes compute higher direct images

Let `f : X -> Y` be a morphism of separated Noetherian schemes, let `F` be
quasi-coherent on `X`, and let `U` be an affine open cover of `X`. For every
`p`, construct the natural isomorphism

`R^p f_* F ~= h^p(f_* C^.(U,F))`.

The unique main result compares module sheaves on `Y`, not merely their
global sections. Mathlib's `cechComplexFunctor` is exact prior art for an
abstract Čech complex, but it does not prove this relative calculation.

## Depends on

- [Module and abelian higher direct images agree](module-higher-direct-image-comparison.md)
- [The Čech complex of an open cover](../cech-cohomology/open-cover-cech-complex.md)

## Proof depends on

- [Higher direct images over an affine target](affine-target-higher-direct-images.md)
- [Affine covers compute quasi-coherent cohomology](../cech-cohomology/affine-cover-comparison.md)
- [Affine intersections in a separated scheme](../../schemes/separated-morphisms/separated-affine-intersection.md)
- [Affine fibre products](../../schemes/fiber-products/affine-fiber-product.md)
- [Closed subschemes of affine schemes are affine](../../schemes/subschemes-and-dimension/affine-closed-subschemes.md)
- For an affine intersection `W` of members of the cover and an affine open
  `V` of `Y`, identify `W intersect f^-1(V)` with the inverse image of the
  closed graph of `W -> Y` inside the affine scheme `W times V`. The graph is
  closed because `Y` is separated, so this inverse image is affine.
- Direct image commutes termwise with the sections defining the Čech
  complex after restriction to an affine open of `Y`.
- [Restriction of higher direct images to an open base](open-base-restriction.md)

## Sources

- [Hartshorne III.8, Proposition 8.7, printed p.252](../../../sources/hartshorne-iii-8.md#affine-targets-and-quasi-coherence-printed-pp-251252)

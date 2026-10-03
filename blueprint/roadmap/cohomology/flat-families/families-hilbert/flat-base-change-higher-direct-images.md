---
declaration: isomorphism
origin: cited
source_units: [chapter-iii-sections-8-9]
---

# Flat base change for higher direct images

Let `f : X -> Y` be separated and finite type between Noetherian schemes,
let `F` be quasicoherent, and let `u : Y' -> Y` be a flat morphism with `Y'`
Noetherian. In the cartesian base-change square, the natural maps

`u^* R^i f_* F -> R^i g_* (v^* F)`

are isomorphisms for all `i >= 0`.

## Depends on

- [The higher-direct-image base-change map](higher-direct-image-base-change-map.md)

## Proof depends on

- [Cech complexes compute higher direct images](../../higher-direct-images/cech-higher-direct-images.md)
- [Higher direct images over an affine target](../../higher-direct-images/affine-target-higher-direct-images.md)
- [Affine covers compute quasicoherent cohomology](../../cech-cohomology/affine-cover-comparison.md)
- [The ordered Cech complex](../../cech-cohomology/open-cover-cech-complex.md)
- [Flat modules remain flat after base change](../flatness/flat-module-base-change.md)
- `Module.Flat.iff_lTensor_exact`: tensoring the Cech complex by the flat base
  algebra commutes with kernels, images, and cohomology.
- [Flat morphisms are stable under base change](../flatness/flat-morphism-base-change.md),
  together with preservation of separatedness and finite type.

## Sources

- [Hartshorne III.9, Proposition 9.3, p.255](../../../../sources/hartshorne-iii-9.md#cohomology-and-flat-base-change-pp255256)

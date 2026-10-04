---
article_id: af_f12d43eddb15d40dadcd429d
declaration: natural transformation
origin: cited
source_units: [chapter-iii-sections-8-9]
not_ready: true
---

# The higher-direct-image base-change map

Let `f : X -> Y` be a separated finite-type morphism of Noetherian schemes,
let `F` be a quasicoherent `O_X`-module, and let `u : Y' -> Y` be a morphism
with `Y'` Noetherian. For the cartesian square

`X' --v--> X`

` |          |`

`g           f`

` |          |`

`Y' --u--> Y`

and a quasicoherent `O_X`-module `F`, construct the natural comparison map

`u^* R^i f_* F -> R^i g_* (v^* F)`

for every `i`.

## Depends on

- [Higher direct images of abelian sheaves](../../higher-direct-images/higher-direct-images.md)
- [Module and abelian higher direct images agree](../../higher-direct-images/module-higher-direct-image-comparison.md)
- [Pullback preserves quasicoherence](../../../schemes/modules-and-quasicoherent/pullback-quasicoherent.md)
- [Module push-pull adjunction](../../../schemes/modules-and-quasicoherent/module-push-pull-adjunction.md)

## Proof depends on

- The degreewise right-derived representation of higher direct images of
  module sheaves and its functorial comparison under a cartesian square.
- [Sheaf cohomology](../../sheaf-cohomology/sheaf-cohomology.md) and the
  degreewise derived-functor comparison.

Pinned Mathlib has site cohomology but no higher-direct-image module-sheaf API
that determines this map, so this representation root is not ready.

## Sources

- [Hartshorne III.9, Remark 9.3.1, p.255](../../../../sources/hartshorne-iii-9.md#cohomology-and-flat-base-change-pp255256)

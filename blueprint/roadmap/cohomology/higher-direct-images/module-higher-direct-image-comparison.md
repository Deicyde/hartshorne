---
declaration: isomorphism
origin: cited
source_units: [chapter-iii-sections-8-9]
not_ready: true
---

# Module and abelian higher direct images agree

For a morphism of ringed spaces `f : (X,O_X) -> (Y,O_Y)`, use a project
ringed-space interface based on `SheafOfModules` to define module-valued
higher direct images as the degreewise right derived functors of
module-sheaf pushforward. After forgetting module structure, construct a
natural isomorphism from this functor to the abelian-sheaf `R^i f_*` of the
underlying sheaf.

The comparison is the unique main result and includes degree zero and the
connecting morphisms. It equips abelian higher direct images of module
sheaves with their canonical module structure. Pinned Mathlib provides
`Scheme.Modules.pushforward` and its additivity, but not this derived
comparison. In particular, the scheme-only wrapper is insufficient for
Hartshorne's ringed-space Proposition 8.4. This node remains not ready until
the project fixes the ringed-space module category, its forgetful functor to
abelian sheaves, and the comparison's universe parameters.

## Depends on

- [Higher direct images of abelian sheaves](higher-direct-images.md)
- [Module sheaves have enough injectives](../sheaf-cohomology/module-sheaves-enough-injectives.md)
- [Right derived functors](../derived-functors/right-derived-functors.md)
- [Pushforward, pullback, and their adjunction](../../schemes/modules-and-quasicoherent/module-push-pull-adjunction.md)

## Proof depends on

- [Module and abelian-sheaf cohomology agree](../sheaf-cohomology/module-cohomology-comparison.md)
- [Injective module sheaves are flasque](../sheaf-cohomology/injective-module-sheaf-flasque.md)
- [Acyclic resolutions compute derived functors](../derived-functors/acyclic-resolution-comparison.md)

## Sources

- [Hartshorne III.8, Proposition 8.4, printed p.251](../../../sources/hartshorne-iii-8.md#module-valued-higher-direct-images-printed-p-251)

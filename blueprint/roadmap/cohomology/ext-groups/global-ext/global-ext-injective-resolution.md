---
article_id: af_a8a006b5b8adef644af67dad
declaration: theorem
origin: cited
mathlib: true
mathlib_declaration: CategoryTheory.InjectiveResolution.extAddEquivCohomologyClass
mathlib_file: Mathlib/CategoryTheory/Abelian/Injective/Ext.lean
---

# Global Ext from an injective resolution

If $G \longrightarrow I^{\bullet}$ is an injective resolution in an abelian category, then
$\operatorname{Ext} ^n(F,G)$ is naturally additively equivalent to the degree-$n$ cohomology
classes of the Hom complex $\operatorname{Hom} (F,I^{\bullet} )$.

This identifies the right-derived-functor computation with global
Ext defined by shifted morphisms. It concerns global Ext groups;
the sheaves $\mathcal{E}xt$ are constructed separately.

## Depends on

- [Global Ext groups](global-ext-groups.md)
- [Injective resolutions](../../derived-functors/injective-resolutions.md)

## Sources

- [Hartshorne III.6, definition of global Ext, printed p.233](../../../../sources/hartshorne-iii-6.md#definitions-and-restriction-printed-pp233234)
- [Three-model distinction](../../../../sources/hartshorne-iii-6.md#boundary-and-the-three-ext-models)

---
article_id: af_a8a006b5b8adef644af67dad
declaration: theorem
origin: cited
source_units: [chapter-iii-sections-6-7]
mathlib: true
mathlib_declaration: CategoryTheory.InjectiveResolution.extAddEquivCohomologyClass
mathlib_file: Mathlib/CategoryTheory/Abelian/Injective/Ext.lean
---

# Global Ext from an injective resolution

If `G ⟶ I•` is an injective resolution in an abelian category, then
`Ext^n(F,G)` is naturally additively equivalent to the degree-`n` cohomology
classes of the Hom complex `Hom(F,I•)`.

This identifies Hartshorne's right-derived-functor computation with Mathlib's
shifted-morphism definition of global Ext. It is not a construction of the
sheaf `𝓔xt` or of an internal `R𝓗om` object.

## Depends on

- [Global Ext groups](global-ext-groups.md)
- [Injective resolutions](../../derived-functors/injective-resolutions.md)

## Sources

- [Hartshorne III.6, definition of global Ext, printed p.233](../../../../sources/hartshorne-iii-6.md#definitions-and-restriction-printed-pp233234)
- [Three-model distinction](../../../../sources/hartshorne-iii-6.md#boundary-and-the-three-ext-models)

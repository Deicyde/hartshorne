---
declaration: definition
origin: cited
source_units: [chapter-iii-sections-1-4]
mathlib: true
mathlib_declaration: CategoryTheory.Functor.rightDerived
mathlib_file: Mathlib/CategoryTheory/Abelian/RightDerived.lean
---

# Right derived functors

For an additive functor `F : A ⥤ B`, where `A` and `B` are abelian and `A`
has injective resolutions, define `RⁿF` by applying `F` to an injective
resolution and taking degree-`n` cohomology. The construction is functorial and
independent of the resolution.

The supporting exact pinned results include
`InjectiveResolution.isoRightDerivedObj`,
`Functor.isZero_rightDerived_obj_injective_succ`, and, for left exact `F`,
`Functor.rightDerivedZeroIsoSelf`.

## Depends on

- [Injective resolutions](injective-resolutions.md)

## Sources

- [Hartshorne III.1, Theorem 1.1A(a,b,e), printed pp. 204–205](../../../sources/hartshorne-iii-1-2.md#derived-functor-foundations-printed-pp-202206)


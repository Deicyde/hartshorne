---
declaration: theorem
origin: cited
source_units: [chapter-iii-sections-1-4]
mathlib: true
mathlib_declaration: CategoryTheory.InjectiveResolution.homotopyEquiv
mathlib_file: Mathlib/CategoryTheory/Abelian/Injective/Resolution.lean
---

# Injective resolutions

In an abelian category with enough injectives, every object admits an
injective resolution, and any two injective resolutions of the same object are
homotopy equivalent compatibly with their augmentations.

The unique main result is the comparison homotopy equivalence. Mathlib's
`InjectiveResolution.homotopyEquiv` is the exact pinned result; existence is
supplied by the resolution instances in the same file. The augmentation is
`InjectiveResolution.ι`, and compatibility of the comparison with it is
recorded by `InjectiveResolution.homotopyEquiv_hom_ι` and
`InjectiveResolution.homotopyEquiv_inv_ι`.

## Depends on

- [Complexes, homotopies, and cohomology](abelian-complexes-and-homotopy.md)

## Sources

- [Hartshorne III.1, injective resolutions, printed p. 204](../../../sources/hartshorne-iii-1-2.md#derived-functor-foundations-printed-pp-202206)


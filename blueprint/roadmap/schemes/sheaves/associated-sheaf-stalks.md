---
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
mathlib_file: Mathlib/Topology/Sheaves/Sheafify.lean
---

# Sheafification preserves stalks

For every presheaf `F` and point `x`, the map on stalks induced by the unit
`F ⟶ F⁺` is an isomorphism.

This is exactly
`TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso`. The node exposes
only this stalk comparison; the universal property and behavior on an existing
sheaf remain supporting API of [the associated sheaf](associated-sheaf.md).

## Depends on

- [The associated sheaf](associated-sheaf.md)
- [Stalks and germs](stalks-and-germs.md)

## Proof depends on

No additional project-local results.

## Sources

- [Hartshorne II.1, properties following Proposition–Definition 1.2 (p. 64)](../../../sources/hartshorne-ii-1.md#associated-sheaves-printed-p-64)

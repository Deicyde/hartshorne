---
declaration: definition
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: TopCat.Sheaf.pullback
mathlib_file: Mathlib/Topology/Sheaves/Functors.lean
---

# Inverse image of a sheaf

For a continuous map `f : X → Y` and a sheaf `G` on `Y`, define `f⁻¹G` as
the associated sheaf of the presheaf whose value on `U ⊆ X` is the colimit of
`G(V)` over opens `V ⊆ Y` containing `f(U)`.

Mathlib implements the presheaf as a left Kan extension and then sheafifies
it. The exact comparison is `TopCat.Sheaf.pullbackIso`, and the resulting
functor is `TopCat.Sheaf.pullback`.

## Depends on

- [The associated sheaf](../sheaves/associated-sheaf.md)

## Proof depends on

No additional project-local results.

## Sources

- [Hartshorne II.1, definition of inverse image (p. 65)](../../../sources/hartshorne-ii-1.md#sheaf-functors-printed-p-65)

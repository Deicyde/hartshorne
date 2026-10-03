---
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-1-3]
---

# Restriction preserves stalks

Let `i : Z ↪ X` be the inclusion of a topological subspace and define the
restriction `F|Z` as `i⁻¹F`. For every `z : Z`, construct a natural
isomorphism

`(F|Z)_z ≅ F_{i(z)}`.

Pinned Mathlib proves the presheaf comparison as
`TopCat.Presheaf.stalkPullbackIso`; this leaf packages it for sheaf pullback by
composing with the isomorphism on stalks induced by sheafification.

## Depends on

- [Inverse image of a sheaf](inverse-image.md)
- [Stalks and germs](../sheaves/stalks-and-germs.md)

## Proof depends on

- [Sheafification preserves stalks](../sheaves/associated-sheaf-stalks.md)

## Sources

- [Hartshorne II.1, restriction to a subspace and its stalks (p. 65)](../../../sources/hartshorne-ii-1.md#sheaf-functors-printed-p-65)

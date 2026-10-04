---
article_id: af_f49fcf230234f702b571fac1
declaration: definition
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: TopCat.Sheaf.pullbackPushforwardAdjunction
mathlib_file: Mathlib/Topology/Sheaves/Functors.lean
---

# Inverse image is left adjoint to direct image

For a continuous map `f : X → Y`, sheaves `G` on `Y`, and `F` on `X`,
there is a natural bijection

`Hom_X(f⁻¹G, F) ≃ Hom_Y(G, f_*F)`.

This is exactly the adjunction
`TopCat.Sheaf.pullbackPushforwardAdjunction` in pinned Mathlib.

## Depends on

- [Direct image of a sheaf](direct-image.md)
- [Inverse image of a sheaf](inverse-image.md)

## Proof depends on

No additional project-local results.

## Sources

- [Hartshorne II.1, Exercise 1.18 (p. 68), used on pp. 109–110](../../../sources/hartshorne-ii-1.md#adopted-exercises-and-later-use-evidence)

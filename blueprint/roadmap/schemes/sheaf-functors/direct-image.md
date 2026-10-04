---
article_id: af_4a417e63d714ab6f6e4c4aa5
declaration: definition
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: TopCat.Sheaf.pushforward
mathlib_file: Mathlib/Topology/Sheaves/Functors.lean
---

# Direct image of a sheaf

For a continuous map `f : X → Y` and a sheaf `F` on `X`, define the direct
image sheaf on `Y` by

`(f_*F)(V) = F(f⁻¹(V))`.

The restrictions are those of `F`, and the sheaf condition pulls back along
preimages of open covers. This is exactly `TopCat.Sheaf.pushforward`; the
section formula is `TopCat.Sheaf.pushforward_obj_val`.

## Depends on

- [Sheaves of abelian groups](../sheaves/sheaves-of-abelian-groups.md)

## Proof depends on

No additional project-local results.

## Sources

- [Hartshorne II.1, definition of direct image (p. 65)](../../../sources/hartshorne-ii-1.md#sheaf-functors-printed-p-65)

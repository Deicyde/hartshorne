---
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-1-3]
---

# Closed extension by zero

Let `i : Z ↪ X` be the inclusion of a closed subspace and `F` a sheaf of
abelian groups on `Z`. Show that direct image is extension by zero:

`(i_*F)ₓ ≅ Fₓ` for `x ∈ Z`, and `(i_*F)ₓ ≅ 0` for `x ∉ Z`.

The on-image comparison follows from Mathlib's
`TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing`. The off-image vanishing
requires using the open complement of `Z`; no exact packaged theorem was found.

## Depends on

- [Direct image of a sheaf](direct-image.md)
- [Stalks and germs](../sheaves/stalks-and-germs.md)

## Proof depends on

- [Sheaves of abelian groups](../sheaves/sheaves-of-abelian-groups.md), for zero sections on the empty open.

## Sources

- [Hartshorne II.1, Exercise 1.19(a) (p. 68), used on p. 196](../../../sources/hartshorne-ii-1.md#adopted-exercises-and-later-use-evidence)

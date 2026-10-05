---
article_id: af_22028ab9c58689fa84aba6a3
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-1-3]
statement: formalized
proof: formalized
lean: Hartshorne.imageSheafification_mono
---

# The image is a subsheaf

For a morphism of sheaves of abelian groups `φ : F ⟶ G`, sheafify the
pointwise image presheaf. The induced map `im φ ⟶ G` is a monomorphism, so the
image identifies canonically with a subsheaf of `G`.

The proof first shows that sheafification sends a sectionwise injective map to
a monomorphism, as in Exercise 1.4(a), then applies this to the inclusion of the
presheaf image. Mathlib has the exact Type-valued construction
`CategoryTheory.Sheaf.imageι` and the needed left-exact sheafification
machinery, but no verified AddCommGrp source-shaped wrapper.

## Depends on

- [The associated sheaf](associated-sheaf.md)

## Proof depends on

- Sheafification's preservation of finite limits in the pinned Mathlib.

## Sources

- [Hartshorne II.1, image sheaf (p. 64) and Exercise 1.4(a,b) (p. 66)](../../../sources/hartshorne-ii-1.md#adopted-exercises-and-later-use-evidence)

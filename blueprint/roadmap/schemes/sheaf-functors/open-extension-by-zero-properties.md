---
article_id: af_0bfcbd42273250dba6a2230e
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-1-3]
---

# Restriction, stalks, and characterization of open extension by zero

Let `j : U ↪ X` be an open immersion and `F` a sheaf on `U`. There is a
canonical isomorphism

`r_F : j^*j_!F ≅ F`.

The stalk of `j_!F` is `Fₓ` at every `x ∈ U` and zero at every `x ∉ U`.
Moreover, if a sheaf `G` on `X` has zero stalk outside `U` and is equipped
with an isomorphism `ρ : j^*G ≅ F`, there is a unique isomorphism
`e : j_!F ≅ G` satisfying

`j^*(e.hom) ≫ ρ.hom = r_F.hom`.

The fixed isomorphism `ρ` and the displayed compatibility are essential:
without them, a nontrivial automorphism of `F` contradicts uniqueness.

## Depends on

- [Open extension by zero](open-extension-by-zero.md)
- [Open extension by zero is left adjoint to restriction](open-extension-by-zero-adjunction.md)
- [Restriction preserves stalks](restriction-stalk.md)

## Proof depends on

- [Sheafification preserves stalks](../sheaves/associated-sheaf-stalks.md)
- [Isomorphisms are detected on stalks](../sheaves/stalkwise-isomorphism.md)

## Sources

- [Hartshorne II.1, Exercise 1.19(b), p. 68](../../../sources/hartshorne-ii-1.md#adopted-exercises-and-later-use-evidence)

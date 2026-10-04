---
article_id: af_a114ce1b2fcf4b3fda7cf09c
declaration: theorem
origin: cited
source_units: [chapter-ii-section-5]
---

# Tilde under affine change of rings

Let `A ⟶ B` induce `f : Spec B ⟶ Spec A`.  For a `B`-module `N` and an
`A`-module `M`, prove natural isomorphisms

`f_*(Ñ) ≅ (N restricted to A)̃`

and

`f*(M̃) ≅ (M ⊗[A] B)̃`.

This is Proposition 5.2(d,e).  Pinned Mathlib contains the affine pushforward
localization theorem `isIso_fromTildeΓ_pushforward`, but not stable named
isomorphisms giving both source-shaped formulas, so this remains one project
comparison leaf.

## Depends on

- [Pushforward, pullback, and their adjunction](module-push-pull-adjunction.md)
- [Tilde commutes with tensor products](tilde-tensor-compatibility.md)

## Proof depends on

- Restriction and extension of scalars commute with localization.
- The formulas may be checked on principal opens of the target and source.

## Sources

- [Hartshorne II.5, Proposition 5.2(d,e) on printed p. 111](../../../sources/hartshorne-ii-5.md#modules-quasi-coherence-and-exactness)

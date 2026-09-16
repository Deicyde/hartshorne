---
declaration: definition
origin: cited
---

# Rational maps

A *rational map* `φ : X ⇢ Y` between varieties is an equivalence class of pairs
`⟨U, φ_U⟩` with `U ⊆ X` nonempty open and `φ_U : U → Y` a morphism, where
`⟨U, φ_U⟩ ~ ⟨V, φ_V⟩` when `φ_U` and `φ_V` agree on `U ∩ V`. The rational map is
*dominant* if for some, equivalently every, representative the image of `φ_U` is
dense in `Y`.

A rational map is not a map of sets from `X` to `Y`. It has no value at a point
outside the open sets where it is represented, and the section never pretends
otherwise.

## Why this needs Lemma 4.1

Reflexivity and symmetry are immediate; transitivity is not. If `φ_U = φ_V` on
`U ∩ V` and `φ_V = φ_W` on `V ∩ W`, all that is directly available is agreement
on `U ∩ V ∩ W`, which is a nonempty open subset of `U ∩ W` rather than all of
it. `U ∩ W` is itself a variety and `U ∩ V ∩ W` is nonempty because `X` is
irreducible, so [Lemma 4.1](morphism-agreement.md) upgrades the agreement to all
of `U ∩ W`.

The same pattern already appeared in §3 for the function field, where rational
*functions* are equivalence classes of pairs `⟨U, f⟩`. There the identity
principle for regular functions was enough, because the target was `k`. Here the
target is an arbitrary variety and the identity principle is not enough; Lemma
4.1 is what replaces it.

That "for some, equivalently every" in the definition of dominant is the same
lemma once more: two representatives agree on the intersection, which is dense,
so their images have the same closure.

## Composition

Dominant rational maps compose: if `φ : X ⇢ Y` is represented by `⟨U, φ_U⟩` and
`ψ : Y ⇢ Z` by `⟨V, ψ_V⟩`, then `φ_U⁻¹(V)` is nonempty — this is exactly where
dominance is used, since a non-dominant `φ` could have image missing `V`
entirely — and `ψ_V ∘ φ_U` represents the composite. So there is a category of
varieties and dominant rational maps, and it is the category
[Theorem 4.4](rational-map-function-field.md) identifies.

## Depends on

- [Morphisms agreeing on an open set](morphism-agreement.md)
- [Morphisms](../morphisms/morphism.md)
- [Varieties](../morphisms/variety.md)

## Sources

- [Hartshorne I.4, definition of rational map (p. 24)](../../sources/hartshorne.md#i4)

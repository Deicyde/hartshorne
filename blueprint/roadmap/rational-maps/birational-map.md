---
declaration: definition
origin: cited
---

# Birational maps

A *birational map* `φ : X ⇢ Y` is a rational map admitting an inverse: a
rational map `ψ : Y ⇢ X` with `ψ ∘ φ = id_X` and `φ ∘ ψ = id_Y` as rational
maps. `X` and `Y` are *birationally equivalent*, or simply *birational*, when
one exists.

This is isomorphism in the category of varieties and dominant rational maps.
Both composites being identities forces both maps to be dominant, so the
definition stays inside that category without saying so.

The equations are equations of *rational* maps, not of maps of sets, and that is
the entire point. `ψ ∘ φ = id_X` says the composite agrees with the identity on
some nonempty open subset of `X`, which by
[Lemma 4.1](morphism-agreement.md) is the strongest thing it could say. Birational
varieties can differ a great deal outside such a subset: [blowing
up](blowing-up.md) is the standard example of a birational morphism that is not
an isomorphism, replacing a point by a whole `ℙⁿ⁻¹`.

Birational equivalence is coarser than isomorphism, and that is what makes it
useful: the classification of varieties up to isomorphism is hopeless, while up
to birational equivalence it becomes the classification of finitely generated
field extensions of `k`, which is [Theorem 4.4](rational-map-function-field.md).

## Depends on

- [Rational maps](rational-map.md)

## Sources

- [Hartshorne I.4, definition of birational map (p. 24)](../../sources/hartshorne.md#i4)

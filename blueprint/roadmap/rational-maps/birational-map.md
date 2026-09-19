---
article_id: af_9b610e24170abc06369e25d0
declaration: definition
origin: cited
source_units: [chapter-i-section-4]
---

# Birational maps

A *birational map* `φ : X ⇢ Y` is a rational map admitting an inverse: a
rational map `ψ : Y ⇢ X` with `ψ ∘ φ = id_X` and `φ ∘ ψ = id_Y` as rational
maps. `X` and `Y` are *birationally equivalent*, or simply *birational*, when
one exists.

The formalization takes this literally as an isomorphism in the category of
separated varieties and dominant rational maps. Dominance is already bundled in
that category's hom type, rather than inferred afterward from the inverse
equations.

The equations are equations of *rational* maps, not of maps of sets, and that is
the entire point. `ψ ∘ φ = id_X` says the composite agrees with the identity on
some nonempty open subset of `X`, which by
[Lemma 4.1](morphism-agreement.md) is the strongest thing it could say. Birational
varieties can differ a great deal outside such a subset:
[blowing up](blowing-up.md) is the standard example of a birational morphism
that is not an isomorphism, replacing a point by a whole `ℙⁿ⁻¹`.

Birational equivalence is coarser than isomorphism, and that is what makes it
useful: the classification of varieties up to isomorphism is hopeless, while up
to birational equivalence it becomes the classification of finitely generated
field extensions of `k`, which is [Theorem 4.4](rational-map-function-field.md).

## Lean shape and prior art

The small project-native definition is an abbreviation
`BirationalMap X Y := X ≅ Y` in the category of separated varieties, followed
by `Birational X Y := Nonempty (BirationalMap X Y)`. The pinned Mathlib also
has scheme-level `Scheme.PartialIso` and `Scheme.Birational`; those are useful
design references but do not directly replace this project's classical
`Variety` model. Before implementation, also recheck the open Mathlib pull
request [#40871, “add birational maps”](https://github.com/leanprover-community/mathlib4/pull/40871).

## Depends on

- [Composition of dominant rational maps](rational-map-composition.md)

## Sources

- [Hartshorne I.4, definition of birational map (p. 24)](../../sources/hartshorne.md#i4)

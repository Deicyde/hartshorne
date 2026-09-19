---
article_id: af_50d38585932c26a7be65604d
declaration: definition
origin: bridged
source_units: [chapter-i-section-4]
statement: formalized
proof: formalized
lean: Hartshorne.DominantRatMap.comp
---

# Composition of dominant rational maps

Dominant rational maps compose. If `φ : X ⇢ Y` is represented by
`⟨U, φ_U⟩` and `ψ : Y ⇢ Z` by `⟨V, ψ_V⟩`, then `φ_U⁻¹(V)` is a nonempty open
subset of `X`: dominance is used here because a non-dominant `φ` could have
image disjoint from `V`. Restricting `φ_U` to that preimage and composing with
`ψ_V` gives a representative of `ψ ∘ φ`.

This construction is independent of both representatives, is associative, and
has the everywhere-defined identity morphisms as identities. It therefore gives
the category of varieties and dominant rational maps used in Theorem 4.4.

The supporting geometric operation is restriction on both sides: a morphism
`φ : A → B` and an open `V ⊆ B` with nonempty preimage induce a morphism from
the open subvariety `φ⁻¹(V)` of `A` to the open subvariety `V` of `B`.

## Depends on

- [Rational maps](rational-map.md)
- [Morphisms](../morphisms/morphism.md)

## Proof depends on

- [Morphisms agreeing on an open set](morphism-agreement.md)

## Sources

- [Hartshorne I.4, rational maps and the category used in Theorem 4.4 (pp. 24–26)](../../sources/hartshorne.md#i4)

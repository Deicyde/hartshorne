---
declaration: def
origin: cited
---

# Morphisms

A *morphism* `φ : X → Y` of varieties is a continuous map such that for every
open `V ⊆ Y` and every regular `f : V → k`, the composite `f ∘ φ` is regular on
`φ⁻¹(V)`. Composition of morphisms is a morphism, so varieties over `k` form a
category. An *isomorphism* is a morphism admitting a two-sided inverse morphism.

The main content is the category instance. Worth stating explicitly as part of
this node, because it is the standard trap: an isomorphism is bijective and
bicontinuous, but a bijective bicontinuous morphism need not be an isomorphism.
Hartshorne's Exercise 3.2 gives two counterexamples, `t ↦ (t², t³)` onto the cusp
`y² = x³`, and the Frobenius `t ↦ tᵖ` in characteristic `p`.

That trap has a formalization consequence: `Iso` must be defined by the existence
of an inverse morphism, never by bijectivity plus continuity, and no lemma should
be allowed to bridge the two.

## Depends on

- [Varieties](variety.md)

## Sources

- [Hartshorne I.3, definition of morphism and isomorphism, with Exercise 3.2 (pp. 15-16, 21)](../../sources/hartshorne.md#i3)

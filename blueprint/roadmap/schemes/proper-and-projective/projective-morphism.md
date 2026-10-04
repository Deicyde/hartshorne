---
article_id: af_545ab34bd95b9748d3c81bd8
declaration: def
origin: cited
source_units: [chapter-ii-section-4]
---

# Projective morphisms

A morphism `f : X ⟶ Y` is projective when there are a natural number `n`
and a closed immersion `i : X ⟶ ℙⁿ_Y` such that `f` is `i` followed by
the relative projective-space projection.

Package the witnessing dimension, closed immersion, and factorization equation
so that the property respects isomorphism of arrows. Expose constructors for
closed immersions and for the projection `ℙⁿ_Y ⟶ Y`. Mathlib has no
existing general projective-morphism predicate, so this is project API rather
than an alias.

## Depends on

- [Projective space over a scheme](projective-space-over-scheme.md)
- [Closed immersions and closed subschemes](../subschemes-and-dimension/closed-immersions.md)

## Proof depends on

- Arrow-isomorphism invariance of closed immersions.

## Sources

- [Hartshorne II.4, definition of projective morphisms](../../../sources/hartshorne-ii-4.md#projective-morphisms)

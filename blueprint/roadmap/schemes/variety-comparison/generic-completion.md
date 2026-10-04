---
article_id: af_3232a70a7349c763871b3c37
declaration: def
origin: cited
source_units: [chapter-ii-sections-1-3]
---

# The generic-completion functor

Define a functor `t : TopCat ⥤ TopCat` as follows.  On a topological space
`X`, `t(X)` is its nonempty irreducible closed subsets, with `t(Y) =
{Z | Z ⊆ Y}` closed whenever `Y ⊆ X` is closed.  For a continuous map
`f : X → Y`, send `Z` to the closure of `f(Z)`.

The unique main artifact is this functor, including its identity and
composition laws.  Supporting it, the map
`α_X : X → t(X)`, `x ↦ closure {x}`, induces an order isomorphism between the
open subsets of `X` and `t(X)`.  The article should reuse Mathlib's carrier
`IrreducibleCloseds X` but supply Hartshorne's topology and open-set
correspondence.

## Depends on

- Nothing in this roadmap.

## Sources

- [Hartshorne II.2, construction of `t(X)` in Proposition 2.6 (p. 78)](../../../sources/hartshorne-ii-2.md#schemes-over-a-base-and-proposition-26)

---
article_id: af_a0c663862a8cb83c9c2e9b1d
---

# Rational maps

A rational map is a morphism defined only on some open subset, and forgetting
which one. That sounds like a weakening and is in fact the opposite: an open
subset of a variety is dense, so a morphism on one already determines a great
deal. Hartshorne's phrasing is that algebraic geometry is more rigid here than
differential geometry or topology, and the concept of birational equivalence has
no counterpart outside it.

The rigidity is one lemma. Two morphisms of varieties that agree on a nonempty
open subset agree everywhere (Lemma 4.1). Without it "the morphism on some open
set, we do not care which" would not even be well defined, because agreeing on a
common refinement would not propagate.

From there the section is short and the payoff large. The open affine subsets of
any variety form a base for its topology (Proposition 4.3), so every local
question reduces to the affine case that §3 already settled. Dominant rational
maps `X ⇢ Y` then correspond exactly to `k`-algebra homomorphisms
`K(Y) → K(X)` (Theorem 4.4), which upgrades to an arrow-reversing equivalence
between varieties with dominant rational maps and finitely generated field
extensions of `k`. Corollary 3.8 said the coordinate ring knows an affine
variety up to isomorphism; Theorem 4.4 says the function field knows any variety
up to birational equivalence, and that is a much coarser and much more useful
classification.

Two applications close the section. Every variety of dimension `r` is birational
to a hypersurface in `ℙ^{r+1}` (Proposition 4.9), which is as much normal form
as birational geometry gives. And blowing up a point, the construction that
resolution of singularities is built from, is exhibited as a birational
morphism that is not an isomorphism.

## Scope note

Two results the running text uses are stated as exercises in earlier sections:
the projective closure of an affine variety (Ex. 2.9) and products of
quasi-projective varieties via the Segre embedding (Ex. 2.14, Ex. 3.16). They
are adopted here under the rule already applied to Exercises 2.1–2.7 — an
exercise the main text depends on is a source target, not optional practice.
See the [coverage contract](../../coverage/README.md).

## Rigidity

- [Morphisms agreeing on an open set](morphism-agreement.md)
- [Rational maps](rational-map.md)
- [Composition of dominant rational maps](rational-map-composition.md)
- [Birational maps](birational-map.md)

## Varieties are locally affine

- [The graph hypersurface has localized coordinate ring](principal-open-coordinate-ring.md)
- [The complement of a hypersurface is affine](hypersurface-complement.md)
- [Open affine sets are a base for the topology](affine-base.md)

## The function field classifies

- [Rational maps and function fields](rational-map-function-field.md)
- [The birational criterion](birational-criterion.md)

## Birational normal form

- [Separably generated field extensions](separably-generated.md)
- [The projective closure of an affine variety](projective-closure.md)
- [Every variety is birational to a hypersurface](birational-hypersurface.md)

## Products and blowing up

- [The Segre embedding](segre-embedding.md)
- [Products of varieties](product-variety.md)
- [Blowing up a point](blowing-up.md)

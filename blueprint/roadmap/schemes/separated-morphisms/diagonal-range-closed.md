---
article_id: af_211f39a4ee5bfc6bdffb1831
declaration: theorem
origin: cited
source_units: [chapter-ii-section-4]
---

# Closed range of the diagonal

For every scheme morphism `f : X ⟶ Y`, the following are equivalent:

1. `f` is separated;
2. the set-theoretic range of `pullback.diagonal f` is closed in
   `X ×[Y] X`.

The diagonal is a homeomorphism onto its range because either projection is a
left inverse. Around a point choose affine neighborhoods `U ⊆ X` and
`V ⊆ Y` with `f(U) ⊆ V`; on `U ×[V] U` the diagonal is the affine closed
immersion from Proposition 4.1. Thus its stalk maps are locally surjective,
and closedness of the range upgrades the preimmersion to a closed immersion.

## Depends on

- [Separated morphisms](separated-morphism.md)

## Proof depends on

- [Affine morphisms are separated](affine-morphism-separated.md)
- `IsClosedImmersion.iff_isPreimmersion` from
  `Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean`.
- Affine neighborhoods form a basis.

## Sources

- [Hartshorne II.4, Corollary 4.2](../../../sources/hartshorne-ii-4.md#separatedness-and-the-valuative-criterion)

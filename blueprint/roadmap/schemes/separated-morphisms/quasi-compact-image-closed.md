---
article_id: af_2578974926636e66e8b2c175
declaration: theorem
origin: cited
source_units: [chapter-ii-section-4]
---

# Closed images and specialization

If `f : X ⟶ Y` is quasi-compact, then `Set.range f` is closed if and only
if it is stable under specialization.

Only the reverse implication requires work. Reduce source and target, replace
the target by the reduced closure of the range, and localize around the chosen
specialization. Quasi-compactness gives finitely many affine source charts.
On one chart dominance gives an injective ring map; localizing above a minimal
prime produces a point over the required generalization, and stability under
specialization supplies the target point itself.

This is the source-shaped range statement. Mathlib's related theorem
`isClosedMap_iff_specializingMap` concerns images of all closed subsets, not
only the whole source, so it is proof infrastructure rather than an exact
replacement.

## Depends on

- [Quasi-compact morphisms](../first-properties/quasi-compact-morphism.md)
- [Specialization and generization](../first-properties/specialization.md)

## Proof depends on

- [The reduced induced closed subscheme](../subschemes-and-dimension/reduced-induced-closed-subscheme.md)
- Existence of minimal primes and exactness of localization.
- `isClosedMap_iff_specializingMap` from
  `Mathlib/AlgebraicGeometry/Morphisms/QuasiCompact.lean`.

## Sources

- [Hartshorne II.4, Lemma 4.5](../../../sources/hartshorne-ii-4.md#separatedness-and-the-valuative-criterion)

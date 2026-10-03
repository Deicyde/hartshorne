---
declaration: def
origin: cited
source_units: [chapter-iii-sections-8-9]
---

# A module sheaf flat over a base

For `f : X -> Y`, an `O_X`-module `F` is flat over `Y` at `x : X` when
`F_x` is flat as an `O_{Y,f(x)}`-module through the stalk map of `f`. It is
flat over `Y` when this holds at every point.

This predicate is distinct from Mathlib's `AlgebraicGeometry.Flat f`, which
is a property of the morphism and corresponds to taking `F=O_X`.

## Depends on

- [Sheaves of modules](../../../schemes/modules-and-quasicoherent/sheaves-of-modules.md)
- [Stalks and germs](../../../schemes/sheaves/stalks-and-germs.md)

## Proof depends on

- Restriction of scalars along the local-ring map on stalks.

## Sources

- [Hartshorne III.9, definition on p.254](../../../../sources/hartshorne-iii-9.md#flat-modules-and-flat-morphisms-pp253255)

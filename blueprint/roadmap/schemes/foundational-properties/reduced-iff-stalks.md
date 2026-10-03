---
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: AlgebraicGeometry.isReduced_of_isReduced_stalk
mathlib_file: Mathlib/AlgebraicGeometry/Properties.lean
---

# Reduced schemes are detected on stalks

A scheme is reduced—every ring of sections has no nonzero nilpotents—if and
only if every local ring `𝒪_{X,x}` is reduced.

The displayed Lean theorem is the local-to-global direction: a nilpotent
section has zero germ everywhere and is zero by the sheaf extensionality
principle.  The reverse implication is the exact upstream instance
`isReduced_stalk_of_isReduced`.  Together they are Exercise 2.3(a).

## Depends on

- [Schemes and affine schemes](../spectrum-and-schemes/scheme.md)

## Sources

- [Hartshorne II.2, Exercise 2.3(a), used on p. 82](../../../sources/hartshorne-ii-2.md#exercises-21-through-29)

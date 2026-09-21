---
article_id: af_3d9205412938cca078b5120b
declaration: theorem
origin: cited
source_units: [chapter-i-section-5-geometry]
mathlib: true
mathlib_declaration: IsRegularLocalRing.iff_finrank_cotangentSpace
mathlib_file: Mathlib/RingTheory/RegularLocalRing/Defs.lean
---

# Regular local rings

Let `A` be a Noetherian local ring, `𝔪` its maximal ideal, and
`κ = A/𝔪` its residue field. Hartshorne calls `A` *regular* when

`dim_κ(𝔪/𝔪²) = dim A`.

This is already the notion `IsRegularLocalRing A` in the pinned Mathlib.
Mathlib represents `𝔪/𝔪²` by `IsLocalRing.CotangentSpace A`; the class is
defined using the equivalent minimal-number-of-generators invariant
`(IsLocalRing.maximalIdeal A).spanFinrank`. The exact source-facing statement
is the verified theorem `IsRegularLocalRing.iff_finrank_cotangentSpace`, which
identifies the class with Hartshorne's equality. The same file's
`IsRegularLocalRing.of_ringEquiv` supplies the invariance under local-ring
isomorphisms needed below.

No project-specific replacement definition should be introduced: subsequent
nodes use the Mathlib class and transport its cotangent-space formulation along
the project's residue-field equivalences.

## Depends on

No project-local prerequisites.

## Sources

- [Hartshorne I.5, definition of a regular local ring (p. 32)](../../sources/hartshorne.md#i5)

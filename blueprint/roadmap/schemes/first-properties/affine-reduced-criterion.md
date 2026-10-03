---
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: AlgebraicGeometry.affine_isReduced_iff
mathlib_file: Mathlib/AlgebraicGeometry/Properties.lean
---

# Reducedness of an affine scheme

For a commutative ring `A`, `Spec A` is reduced if and only if `A` is reduced,
equivalently if and only if its nilradical is zero.

Use the global-sections isomorphism for `Spec A` together with the ring-level
nilradical criterion.

## Depends on

- [Reduced schemes](reduced-scheme.md)
- [Global sections of Spec](../spectrum-and-schemes/spec-global-sections.md)

## Proof depends on

- The ring theorem `nilradical_eq_bot_iff`.

## Sources

- [Hartshorne II.3, Example 3.0.1 (p. 82)](../../../sources/hartshorne-ii-3.md#reduced-integral-and-noetherian-schemes)


---
article_id: af_35b6ef090fc3547a937e338c
declaration: lemma
origin: cited
source_units: [chapter-ii-section-4]
mathlib: true
mathlib_declaration: AlgebraicGeometry.IsProper.eq_valuativeCriterion
mathlib_file: Mathlib/AlgebraicGeometry/ValuativeCriterion.lean
---

# Valuative criterion for properness

For every morphism `f`, properness is equivalent to the conjunction of the
unique-lift valuative criterion, quasi-compactness, quasi-separatedness, and
local finite type. Hence a finite-type morphism with Noetherian source is
proper exactly when every valuative commutative square has a unique lift, as
in Theorem 4.7.

Split unique lifting into existence and uniqueness. The former gives universal
closedness, and the latter gives separatedness. The remaining finiteness
hypotheses give precisely Mathlib's definition of properness. Conversely,
properness provides existence by closedness after base change and uniqueness
by the closed diagonal.

## Depends on

- [Proper morphisms](proper-morphism.md)
- [Valuative commutative squares](../separated-morphisms/valuative-square.md)
- [Quasi-compact morphisms](../first-properties/quasi-compact-morphism.md)
- [Morphisms of finite type](../first-properties/finite-type.md)
- [Noetherian schemes and finite affine covers](../first-properties/noetherian-scheme.md)

## Proof depends on

- [Valuative criterion for universal closedness](valuative-criterion-universally-closed.md)
- [Valuative criterion for separatedness](../separated-morphisms/valuative-criterion-separated.md)
- Noetherian sources are quasi-compact and quasi-separated.

## Sources

- [Hartshorne II.4, Theorem 4.7](../../../sources/hartshorne-ii-4.md#properness-and-the-valuative-criterion)

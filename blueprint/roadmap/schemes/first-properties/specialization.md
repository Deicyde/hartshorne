---
article_id: af_13b9595707683ca9d52c5e69
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: specializes_iff_mem_closure
mathlib_file: Mathlib/Topology/Inseparable.lean
---

# Specialization and generization

A point `x₁` specializes to `x₀` exactly when `x₀ ∈ closure {x₁}`. Closed subsets are stable under specialization, and open subsets are stable under generization.

The exact upstream main theorem is `specializes_iff_mem_closure`. The supporting
exact lemmas `IsClosed.stableUnderSpecialization` and
`IsOpen.stableUnderGeneralization` give the two stability statements.

## Depends on

- [Schemes and affine schemes](../spectrum-and-schemes/scheme.md)

## Proof depends on

- `IsClosed.stableUnderSpecialization` and
  `IsOpen.stableUnderGeneralization` from `Mathlib/Topology/Inseparable.lean`.

## Sources

- [Hartshorne II.3 (later-used-exercises)](../../../sources/hartshorne-ii-3.md#later-used-exercises)

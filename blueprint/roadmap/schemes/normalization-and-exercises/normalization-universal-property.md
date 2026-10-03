---
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-1-3]
---

# The universal property of normalization

If `Z` is normal and integral and `f : Z → X` is dominant, then `f` factors uniquely through the normalization `ν : X̃ → X`.

Dominance embeds `K(X)` into `K(Z)`. On affine opens, normality forces every element integral over the image of the target ring to land in the source section ring. Construct compatible local lifts and glue; uniqueness follows from density and separatedness of the affine charts.

## Depends on

- [Construction of the normalization](normalization-construction.md)
- [Normal schemes](normal-scheme.md)

## Proof depends on

- The universal property of integral closure and equality of morphisms on a dense open.
- [Affine opens have fraction field `K(X)`](function-field-integral-scheme.md)
- Mathlib's `normalizationDesc` and `normalization.hom_ext` as relative prior
  art; their hypotheses and orientation do not directly state this theorem.

## Sources

- [Hartshorne II.3 (later-used-exercises)](../../../sources/hartshorne-ii-3.md#later-used-exercises)

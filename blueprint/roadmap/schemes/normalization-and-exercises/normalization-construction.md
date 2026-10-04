---
article_id: af_47c3f0f84fedd5df49585e9c
declaration: def
origin: cited
source_units: [chapter-ii-sections-1-3]
---

# Construction of the normalization

For an integral scheme `X`, glue `Spec Ā` over affine opens `Spec A`, where `Ā` is the integral closure of `A` in `K(X)`, to obtain a morphism `ν : X̃ → X`.

Show integral closure commutes with the localizations representing principal opens. These canonical identifications satisfy the cocycle condition, so the affine normalizations glue together and their maps to `X` glue to `ν`.

Mathlib's `Scheme.Hom.normalization` already constructs a relative
normalization for a quasi-compact, quasi-separated morphism and identifies its
affine charts with integral closures. This leaf is the source-shaped absolute
wrapper obtained from the function-field morphism; it is not an exact upstream
declaration.

## Depends on

- [Normal schemes](normal-scheme.md)
- [The function field of an integral scheme](function-field-integral-scheme.md)
- [Gluing schemes](../spectrum-and-schemes/gluing.md)

## Proof depends on

- Integral closure commutes with localization inside a common fraction field.
- `Scheme.Hom.normalization`, `normalizationOpenCover`, and
  `normalizationObjIso` from the pinned relative-normalization API.

## Sources

- [Hartshorne II.3 (later-used-exercises)](../../../sources/hartshorne-ii-3.md#later-used-exercises)

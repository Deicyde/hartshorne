---
article_id: af_e50bd55d0e4eeadcb033ff3f
declaration: def
origin: cited
source_units: [chapter-ii-section-5]
---

# The affine tilde sheaf and localization

For a ring `A` and an `A`-module `M`, construct the `𝒪_{Spec A}`-module
`M̃` whose local sections are locally fractions.  The canonical maps exhibit

- `Γ(D(f), M̃)` as the localization `M_f`;
- the stalk `M̃_𝔭` as the localization `M_𝔭`; and
- `Γ(Spec A,M̃)` as `M`.

These universal-property formulations are Proposition 5.1.  Pinned Mathlib
implements them through `AlgebraicGeometry.tilde.toOpen`, `toStalk`, and
`isoTop`, but the localized-module facts are instances rather than one stable
named theorem, so this page records no single-result Mathlib metadata.

## Depends on

- [Sheaves of modules](sheaves-of-modules.md)
- [The stalk of Spec](../spectrum-and-schemes/spec-stalk.md)
- [Sections on a principal open](../spectrum-and-schemes/spec-basic-open-sections.md)
- [Global sections of an affine spectrum](../spectrum-and-schemes/spec-global-sections.md)

## Proof depends on

- Localization of a module at a prime and away from one element.
- Principal opens form a basis of `Spec A`.

## Sources

- [Hartshorne II.5, Proposition 5.1 on printed p. 110](../../../sources/hartshorne-ii-5.md#modules-quasi-coherence-and-exactness)

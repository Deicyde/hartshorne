---
article_id: af_02eeba4ecfe5ba1090a09b26
declaration: def
origin: cited
source_units: [chapter-ii-section-4]
statement: formalized
proof: formalized
lean: Hartshorne.projectiveSpaceOverScheme Hartshorne.projectiveSpaceOverSchemeProjection Hartshorne.projectiveSpaceOverSchemeBaseChangeIso
---

# Projective space over a scheme

For a scheme `Y`, define relative projective `n`-space by

`ℙⁿ_Y := ℙⁿ_ℤ ×[Spec ℤ] Y`,

with structure morphism the second projection. Expose the canonical base-change
isomorphism

`ℙⁿ_Y ×[Y] Y' ≅ ℙⁿ_{Y'}`

and its compatibility with projections. Use the existing scheme projective
space over a ring for `ℙⁿ_ℤ`; keep this construction distinct from the
project's Chapter-I type of classical projective points.

## Depends on

- [Projective space over a ring](../projective-spectrum/projective-space-over-ring.md)
- [The spectrum of the integers is terminal](../foundational-properties/spec-z-terminal.md)
- [Base extension](../fiber-products/base-extension.md)

## Proof depends on

- [Transitivity of base extension](../fiber-products/base-extension-transitive.md)
- Associativity and symmetry isomorphisms for categorical pullbacks.

## Sources

- [Hartshorne II.4 (projective-morphisms)](../../../sources/hartshorne-ii-4.md#projective-morphisms)

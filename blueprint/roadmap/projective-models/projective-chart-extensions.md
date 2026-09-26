---
article_id: af_07babcb2c7e4ec6fd15296d9
declaration: theorem
origin: bridged
source_units: [chapter-i-section-6-projective-model]
---

# Extensions to the projective chart closures

For the two affine models covering `C_K`, choose projective closures `Y₀`
and `Y₁`.  Their open maps extend to morphisms
`φᵢ : C_K → Yᵢ` agreeing with the original affine identifications on the
corresponding chart.  The sole main declaration is planned as
`Hartshorne.ValuationSpace.exists_two_projective_chart_extensions`.

The implementation should package the harmless coordinate reindexing needed
to feed each affine presentation to the existing projective-closure API.  That
reindexing is support code, not a second roadmap result.

## Depends on

- [A two-chart affine cover of the valuation curve](two-affine-chart-cover.md)
- [The projective closure of an affine variety](../rational-maps/projective-closure.md)
- [Extension to a projective target](projective-extension.md)

## Proof depends on

- [The charts are isomorphisms of varieties](../morphisms/projective-rings/chart-isomorphism.md)
- [Morphisms agreeing on an open set](../rational-maps/morphism-agreement.md)

## Sources

- [Hartshorne I.6, proof of Theorem 6.9 (p. 44)](../../sources/hartshorne.md#i6-projective-models)

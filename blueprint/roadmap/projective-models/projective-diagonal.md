---
article_id: af_7573872cfdef047cd2572bae
declaration: theorem
origin: bridged
source_units: [chapter-i-section-6-projective-model]
---

# The projective diagonal model

The two extended maps `φ₀` and `φ₁` define a diagonal map from `C_K`
to the Segre product `Y₀ × Y₁`.  Its image closure is an irreducible
projective variety `Y`, and the diagonal corestricts to a dense morphism
`φ : C_K → Y`.  The sole main declaration is planned as
`Hartshorne.ValuationSpace.exists_dense_projective_diagonal`.

This is Hartshorne's product-and-closure construction with the finite index
set specialized to the two normalization charts.

The main existential returns a supporting `ProjectiveDiagonalModel` package.
It retains the two chart models and closures, the chart-cover equality, their
extended morphisms together with the equations showing agreement with the
original affine-chart embeddings, the product projections, `Y` as exactly the
closure of the diagonal image, and the dense corestricted diagonal `φ`.  For
each of the two charts it also records the restricted projection identity
`πᵢ ∘ φ = Φᵢ`.  The following function-field and local-ring leaves refer
to this same package; they may not choose unrelated existential witnesses.

## Depends on

- [Extensions to the projective chart closures](projective-chart-extensions.md)
- [Products of varieties](../rational-maps/product-variety.md)
- [Projective and quasi-projective varieties](../projective-varieties/projective-variety.md)
- [Morphisms](../morphisms/morphism.md)

## Sources

- [Hartshorne I.6, construction in the proof of Theorem 6.9 (pp. 44--45)](../../sources/hartshorne.md#i6-projective-models)

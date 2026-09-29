---
article_id: af_5bd96acb0a5232df552012b0
declaration: def
origin: cited
source_units: [chapter-i-section-6-projective-model]
statement: formalized
proof: formalized
lean: Hartshorne.projectiveCurveFunctionFieldEquivalence
---

# The curve/function-field category equivalence

The contravariant function-field functor gives an equivalence

`(ProjectiveNonsingularCurveCat k)ᵒᵖ ≌ OneDimensionalFunctionFieldCat k`.

The sole main declaration is formalized as
`Hartshorne.projectiveCurveFunctionFieldEquivalence`.  It is the composite of
the opposite of the projective/quasi-projective comparison with the
quasi-projective-curve/function-field equivalence.

Contravariance is part of the type: a field homomorphism `K₂ → K₁` gives a
map `C_{K₁} → C_{K₂}`.  Its forward functor is the pullback on function
fields; no definitional choice of quasi-inverse is asserted.  Keeping the two
component equivalences separate makes each construction independently
reviewable; this leaf is their small source-facing composite.

## Depends on

- [The three curve categories](curve-categories.md)

## Proof depends on

- [Projective and quasi-projective curve categories are equivalent](projective-quasiprojective-curve-equivalence.md)
- [Quasi-projective curves and one-dimensional function fields are equivalent](quasiprojective-curve-function-field-equivalence.md)

## Sources

- [Hartshorne I.6, Corollary 6.12 and its proof (pp. 45--46)](../../sources/hartshorne.md#i6-projective-models)

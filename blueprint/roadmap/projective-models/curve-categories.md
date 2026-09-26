---
article_id: af_c7ac0a5fa52ef3a39637f1b5
declaration: def
origin: bridged
source_units: [chapter-i-section-6-projective-model]
---

# The three curve categories

Define the category of nonsingular projective curves with dominant morphisms.
The sole main declaration is planned as
`Hartshorne.ProjectiveNonsingularCurveCat`.

The same implementation leaf may provide the supporting bundled categories
of quasi-projective curves with dominant rational maps and of finitely
generated one-dimensional function fields with `k`-homomorphisms.  Objects in
the geometric categories must include actual finite quasi-projective or
projective presentations, not merely predicates detached from the existing
variety API.  Dominance is part of each morphism type and is preserved by
identity and composition.

## Depends on

- [Curves](../nonsingular-curves/curve.md)
- [Projective and quasi-projective varieties](../projective-varieties/projective-variety.md)
- [Morphisms](../morphisms/morphism.md)
- [Rational maps](../rational-maps/rational-map.md)
- [The function field of an arbitrary variety](../morphisms/function-field-abstract.md)

## Proof depends on

- [Composition of dominant rational maps](../rational-maps/rational-map-composition.md)
- [The function field is functorial for dominant morphisms](../morphisms/function-field-functorial.md)

## Sources

- [Hartshorne I.6, the three categories in Corollary 6.12 (pp. 45--46)](../../sources/hartshorne.md#i6-projective-models)

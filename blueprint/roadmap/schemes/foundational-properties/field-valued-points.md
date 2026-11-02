---
article_id: af_7e6d3d87166ea4cacb15b7ab
declaration: def
origin: cited
mathlib: true
mathlib_declaration: AlgebraicGeometry.Scheme.SpecToEquivOfField
mathlib_file: Mathlib/AlgebraicGeometry/ResidueField.lean
---

# Field-valued points of a scheme

For a scheme $X$ and a field $K$, morphisms $\operatorname{Spec} K \to X$ correspond
bijectively to pairs consisting of a point $x \in X$ and an embedding of residue
fields $\kappa (x) \to K$.

A morphism supplies its image point and a local stalk map, which factors
through the residue field.  Conversely compose $\operatorname{Spec} K \to \operatorname{Spec} \kappa (x)$ with the
canonical morphism $\operatorname{Spec} \kappa (x) \to X$.  This is Exercise 2.7.

## Depends on

- [The contravariant Spec functor](../spectrum-and-schemes/spec-functor.md)
- [Schemes and affine schemes](../spectrum-and-schemes/scheme.md)

## Sources

- [Hartshorne II.2, Exercise 2.7, used to define fibres (p. 80)](../../../sources/hartshorne-ii-2.md#exercises-21-through-29)

---
declaration: def
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: AlgebraicGeometry.Scheme.SpecToEquivOfField
mathlib_file: Mathlib/AlgebraicGeometry/ResidueField.lean
---

# Field-valued points of a scheme

For a scheme `X` and a field `K`, morphisms `Spec K → X` correspond
bijectively to pairs consisting of a point `x : X` and an embedding of residue
fields `κ(x) → K`.

A morphism supplies its image point and a local stalk map, which factors
through the residue field.  Conversely compose `Spec K → Spec κ(x)` with the
canonical morphism `Spec κ(x) → X`.  This is Exercise 2.7.

## Depends on

- [The contravariant Spec functor](../spectrum-and-schemes/spec-functor.md)
- [Schemes and affine schemes](../spectrum-and-schemes/scheme.md)

## Sources

- [Hartshorne II.2, Exercise 2.7, used to define fibres (p. 80)](../../../sources/hartshorne-ii-2.md#exercises-21-through-29)

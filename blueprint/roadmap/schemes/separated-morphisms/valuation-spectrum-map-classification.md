---
article_id: af_436941c8814fd3a1df66a43d
declaration: theorem
origin: cited
source_units: [chapter-ii-section-4]
---

# Maps from spectra of valuation rings

Let `R` be a valuation ring with fraction field `K`. A morphism
`Spec R ⟶ X` is equivalent to a generic point datum consisting of a point
`x₁ : X` and an embedding `κ(x₁) → K`, together with a specialization
`x₁ ⟿ x₀` for which `R` dominates the image in `K` of the local ring of
`x₀` on the reduced closed subscheme `closure {x₁}`.

The classification of `Spec K ⟶ X` by a point and a residue-field map is
the existing field-valued-points result and is input to this theorem, not a
second main result of the leaf.

Start with `SpecToEquivOfLocalRing`, identify the generic and closed points of
the spectrum of a valuation ring, and factor through the reduced closure
because `Spec R` is reduced. Conversely, domination gives the local map to
`R`; compose its spectrum map with the canonical map from the stalk spectrum.

## Depends on

- [Field-valued points of a scheme](../foundational-properties/field-valued-points.md)
- [Specialization and generization](../first-properties/specialization.md)
- [The reduced induced closed subscheme](../subschemes-and-dimension/reduced-induced-closed-subscheme.md)
- [The stalk of an affine scheme](../spectrum-and-schemes/spec-stalk.md)

## Proof depends on

- `SpecToEquivOfLocalRing` from `Mathlib/AlgebraicGeometry/Stalk.lean`.
- Identification of the function field of an integral reduced closure with
  the residue field of its generic point.

## Sources

- [Hartshorne II.4, Lemma 4.4](../../../sources/hartshorne-ii-4.md#separatedness-and-the-valuative-criterion)

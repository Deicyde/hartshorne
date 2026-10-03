---
declaration: def
origin: cited
source_units: [chapter-ii-sections-1-3]
---

# The partial Proj morphism of a graded map

Let `φ : S → T` be a degree-preserving homomorphism of graded rings and let

`U = {𝔭 ∈ Proj T | 𝔭 ⊉ φ(S₊)}`.

Then `U` is open and `φ` determines a natural scheme morphism
`U → Proj S`, sending `𝔭` to `φ⁻¹(𝔭)`.

Cover `U` by the opens `D₊(φ(f))` for positive-degree homogeneous `f ∈ S`.
On each chart use the induced map of degree-zero away localizations and the
standard affine correspondence, then glue.  Mathlib's existing `Proj.map`
supplies the special case in which the irrelevant-ideal hypothesis makes
`U = Proj T`; it is not the general statement of Exercise 2.14(b).

## Depends on

- [A standard Proj chart is affine](proj-basic-open.md)

## Proof depends on

- [Gluing schemes](../spectrum-and-schemes/gluing.md)

## Sources

- [Hartshorne II.2, Exercise 2.14(b), adopted for later graded functoriality (pp. 80–81)](../../../sources/hartshorne-ii-2.md#exercises-212-through-219)

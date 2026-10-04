---
article_id: af_7e7c8bfc45525013c0d6b59b
declaration: def
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: AlgebraicGeometry.Proj.toLocallyRingedSpace
mathlib_file: Mathlib/AlgebraicGeometry/ProjectiveSpectrum/StructureSheaf.lean
---

# The structure sheaf on Proj

At a relevant homogeneous prime `𝔭`, let `S_(𝔭)` be the degree-zero part of
the homogeneous localization away from `𝔭`.  Sections on an open subset are
dependent functions into these rings which locally are fractions `a/f` of
same-degree homogeneous elements.  They form a sheaf, and its stalks are local
rings, so `Proj S` is a locally ringed space.

Mathlib packages the sheaf as `Proj.structureSheaf` and the locally ringed
space as the main declaration above.

## Depends on

- [The topology on Proj](proj-topology.md)
- [Locally ringed spaces](../spectrum-and-schemes/locally-ringed-space.md)

## Sources

- [Hartshorne II.2, structure sheaf on Proj (p. 76)](../../../sources/hartshorne-ii-2.md#proj-lemma-24-and-proposition-25)

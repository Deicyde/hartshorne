---
article_id: af_f72c6f3e9d3b003757808e64
declaration: def
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: AlgebraicGeometry.Proj.affineOpenCover
mathlib_file: Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean
---

# Positive-degree basic opens form an affine cover

For every relevant homogeneous prime of `S`, some positive-degree homogeneous
element lies outside it.  Consequently the opens `D₊(f)`, for homogeneous
`f ∈ S₊`, cover `Proj S`, and every member of this cover is affine.

The unique main artifact is Mathlib's bundled `Proj.affineOpenCover`.  Coverage
is the defining relevance condition; affineness is supplied by the standard
chart isomorphism `D₊(f) ≅ Spec S_(f)`.

## Depends on

- [Proj is a scheme](proj-is-scheme.md)
- [A standard Proj chart is affine](proj-basic-open.md)

## Sources

- [Hartshorne II.2, covering and affineness clauses of Proposition 2.5(b) (p. 77)](../../../sources/hartshorne-ii-2.md#proj-lemma-24-and-proposition-25)

---
article_id: af_fb83feaf3283e2c3a9e7c4e9
declaration: structure
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: AlgebraicGeometry.LocallyRingedSpace
mathlib_file: Mathlib/Geometry/RingedSpace/LocallyRingedSpace.lean
---

# Locally ringed spaces

A locally ringed space is a topological space with a sheaf of commutative
rings whose stalks are local rings.  A morphism is a ringed-space morphism
`(f,f#)` for which every contravariant stalk map
`𝒪_{Y,f(x)} → 𝒪_{X,x}` is local.

Mathlib's `LocallyRingedSpace` and `LocallyRingedSpace.Hom` use exactly this
orientation.  The locality condition excludes Hartshorne's cautionary map from
the generic point of a DVR spectrum to its closed point.

## Depends on

- Nothing in this roadmap.

## Sources

- [Hartshorne II.2, definitions of ringed and locally ringed spaces (pp. 72–73)](../../../sources/hartshorne-ii-2.md#locally-ringed-spaces-and-proposition-23)

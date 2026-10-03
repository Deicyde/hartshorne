---
declaration: def
origin: cited
source_units: [chapter-ii-sections-1-3]
---

# Projective space over a ring

For a commutative ring `A` and a finite coordinate type with `n + 1` elements,
define the scheme projective space

`ℙⁿ_A := Proj A[x₀,…,xₙ]`

using the standard total-degree grading.  Its name must remain distinct from
the project's existing classical-point `Hartshorne.ProjectiveSpace`.

The implementation should expose the standard `D₊(xᵢ)` affine cover and the
structure morphism to `Spec A`, but the unique completion criterion for this
node is the definition of the scheme itself.

## Depends on

- [Proj is a scheme](proj-is-scheme.md)

## Sources

- [Hartshorne II.2, Example 2.5.1 (p. 77)](../../../sources/hartshorne-ii-2.md#proj-lemma-24-and-proposition-25)

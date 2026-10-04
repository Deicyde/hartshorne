---
article_id: af_922c19d6bd4da80267f81e54
declaration: definition
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: CategoryTheory.Sheaf.isColimitSheafifyCocone
mathlib_file: Mathlib/CategoryTheory/Sites/Limits.lean
---

# Colimits of sheaves are sheafified pointwise colimits

The category of sheaves of abelian groups admits coproducts and direct limits.
Given a colimit cocone of the underlying presheaves, sheafifying its cocone
point produces a colimit cocone in sheaves. Thus direct sums and direct limits
are the associated sheaves of their pointwise presheaf constructions.

This construction is exactly
`CategoryTheory.Sheaf.isColimitSheafifyCocone` in pinned Mathlib. The unique
main artifact is the colimit certificate for the sheafified cocone; existence
of the corresponding colimits is its instance-level consequence.

## Depends on

- [Sheaves of abelian groups](sheaves-of-abelian-groups.md)
- [The associated sheaf](associated-sheaf.md)

## Proof depends on

No additional project-local results.

## Sources

- [Hartshorne II.1, Exercises 1.9 and 1.10 (pp. 66–67), used on p. 109](../../../sources/hartshorne-ii-1.md#adopted-exercises-and-later-use-evidence)


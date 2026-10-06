---
article_id: af_587d2163b44f5944c3c8c7be
declaration: theorem
origin: cited
source_units: [chapter-ii-section-5]
statement: formalized
proof: formalized
lean: Hartshorne.exists_affine_open_cover_iff_forall_isAffineOpen_preimage
---

# The affine-morphism criterion

A morphism `f : X → Y` is affine when there exists an affine open cover
`{V_i}` of `Y` such that every `f⁻¹(V_i)` is affine. Exercise 5.17(a) proves
that this is equivalent to requiring `f⁻¹(V)` affine for every affine open
`V ⊆ Y`. Every affine morphism is quasi-compact and separated, and every
finite morphism is affine.

The biconditional is the unique main result; the three permanence statements
are its immediate API consequences.

## Depends on

- [Affine cover criterion](../foundational-properties/affine-cover-criterion.md)
- [Quasi-compact morphisms](../first-properties/quasi-compact-morphism.md)
- [Finite morphisms](../first-properties/finite-morphism.md)

## Proof depends on

- The existing Mathlib predicate `AlgebraicGeometry.IsAffineHom` and its
  target-locality and separatedness instances.

## Sources

- [Hartshorne II.5, Exercise 5.17(a,b) (p.128)](../../../sources/hartshorne-ii-5.md#adopted-exercises-and-later-use-evidence)

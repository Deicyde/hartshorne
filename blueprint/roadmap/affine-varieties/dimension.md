---
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.dim Hartshorne.dim_le_of_subset Hartshorne.dim_univ
---

# Dimension of a topological space and of a ring

The *dimension* of a topological space `X` is the supremum of the integers `n`
admitting a chain `Z₀ ⊊ Z₁ ⊊ … ⊊ Zₙ` of distinct irreducible closed subsets. The
dimension of an affine or quasi-affine variety is its dimension as a space. In a
ring, the *height* of a prime `𝔭` is the supremum of lengths of chains
`𝔭₀ ⊊ … ⊊ 𝔭ₙ = 𝔭`, and the *Krull dimension* is the supremum of the heights.

Both notions are already in Mathlib, as `topologicalKrullDim` and
`ringKrullDim`, valued in `WithBot ℕ∞`. This node fixes those as the project's
definitions and supplies the specialisation to varieties, so that later
statements say `topologicalKrullDim Y` rather than reintroducing chains.

Choosing `WithBot ℕ∞` rather than `ℕ` matters downstream: the empty space has
dimension `⊥` and infinite-dimensional Noetherian spaces exist, so statements
like `dim 𝔸ⁿ = n` are equalities in `WithBot ℕ∞` and need the coercion handled
explicitly.

## Depends on

- [Affine and quasi-affine varieties](affine-variety.md)

## Sources

- [Hartshorne I.1, definitions of dimension, height and Krull dimension (pp. 5-6)](../../sources/hartshorne.md#i1)

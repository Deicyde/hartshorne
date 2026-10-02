---
article_id: af_10beeea75107994712e1057d
declaration: definition
origin: cited
source_units: [chapter-i-section-7-main]
statement: formalized
proof: formalized
lean: Hartshorne.projectiveIntersectionMultiplicity
---

# Intersection multiplicity with a hypersurface

Let `Y ⊆ ℙⁿ` be a projective variety, let `H` be a hypersurface not containing
`Y`, and let `Z` be an irreducible component of `Y ∩ H` with homogeneous prime
ideal `p_Z`. Define

`i(Y,H;Z) = μ_{p_Z}(S/(I(Y)+I(H)))`.

The main artifact is the natural-valued intersection multiplicity
`Hartshorne.projectiveIntersectionMultiplicity`, together with
the theorem that the underlying `ℕ∞` module length is finite. The component
theorem identifies `p_Z` as a minimal prime of the quotient module, making the
definition an instance of graded multiplicity.

## Depends on

- [Multiplicity in a graded prime filtration](../hilbert/graded-multiplicity.md)
- [Projective intersection components on an affine chart](../dimension/projective-intersection-components.md)
- [Algebraic sets and homogeneous radical ideals](../../projective-varieties/homogeneous-ideal-correspondence.md)

## Sources

- [Hartshorne I.7, definition before Theorem 7.7 (p. 53)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)

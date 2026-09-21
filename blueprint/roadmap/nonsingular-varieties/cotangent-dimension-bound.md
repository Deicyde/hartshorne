---
article_id: af_eec06f727fc1cf5bb44d0721
declaration: theorem
origin: background
source_units: [chapter-i-section-5-geometry]
---

# The cotangent-dimension bound

If `A` is a Noetherian local ring with maximal ideal `𝔪` and residue field
`κ`, then

`dim A ≤ dim_κ(𝔪/𝔪²)`.

This is Proposition 5.2A. The pinned Mathlib has both ingredients but not this
exact cotangent-space spelling as one declaration:

- `ringKrullDim_le_spanFinrank_maximalIdeal` proves
  `ringKrullDim A ≤ 𝔪.spanFinrank`;
- `IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace` identifies
  the right side with
  `Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.CotangentSpace A)`
  for a Noetherian local ring.

The project theorem is the direct rewrite joining those results. Keeping the
wrapper explicit lets the Jacobian argument cite Hartshorne's inequality in
the same form in which it is used.

## Depends on

No project-local prerequisites.

## Sources

- [Hartshorne I.5, Proposition 5.2A (p. 33)](../../sources/hartshorne.md#i5)

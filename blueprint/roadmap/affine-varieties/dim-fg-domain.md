---
declaration: theorem
origin: background
---

# Dimension of a finitely generated domain

Let `k` be a field and `B` an integral domain that is a finitely generated
`k`-algebra. Then

- `dim B = trdeg_k K(B)`, the transcendence degree of the fraction field; and
- `height 𝔭 + dim B/𝔭 = dim B` for every prime `𝔭 ⊆ B`.

Hartshorne quotes both as Theorem 1.8A, citing Matsumura and Atiyah–Macdonald.
Everything numerical in Chapter I rests on them: `dim 𝔸ⁿ = n`, `dim Y = dim Ȳ`
for quasi-affine `Y`, the codimension-one characterisation of hypersurfaces, and
in §3 the fact that `K(Y)` has transcendence degree `dim Y`.

This is the largest identified gap in the pinned Mathlib. `ringKrullDim`,
`Algebra.trdeg` and the machinery around Noether normalisation are all present,
but the two statements above are not, in this form. Expect this node to be the
single biggest piece of the chapter, and expect it to be worth upstreaming.
Because it is quoted rather than proved in the source, its proof is not
constrained to follow Hartshorne.

## Depends on

- [Dimension of a topological space and of a ring](dimension.md)

## Sources

- [Hartshorne I.1, Theorem 1.8A (p. 6)](../../sources/hartshorne.md#i1)

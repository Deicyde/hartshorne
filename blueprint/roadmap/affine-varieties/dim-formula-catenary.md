---
declaration: theorem
origin: background
---

# The dimension formula for a finitely generated domain

Let `k` be a field and `B` an integral domain that is a finitely generated
`k`-algebra. Then `height 𝔭 + dim B/𝔭 = dim B` for every prime `𝔭 ⊆ B`.

This is the second clause of Hartshorne's Theorem 1.8A, quoted from Matsumura
and Atiyah–Macdonald and split out from
[the first](dim-fg-domain.md) because the two have nothing in common beyond
their source. The first clause is a computation of one number by two routes; this
one says every maximal chain through `𝔭` has the same length, which is a
statement about the whole poset of primes.

It is the clause the geometry needs. Proposition 1.10 (`dim Y = dim Ȳ` for
quasi-affine `Y`) is the first place it is unavoidable: the argument picks a
maximal chain, observes its bottom term is a point, and needs `dim B/𝔪_P = 0` to
convert `height 𝔪_P` into `dim B`. Proposition 1.13 uses it to turn Krull's
Hauptidealsatz from a height statement into a dimension statement.

## Status

One inequality is proved and is a separate node,
[one inequality of the dimension formula](dim-formula-inequality.md):
`height 𝔭 + dim R/𝔭 ≤ dim R`, in any commutative ring. What remains here is the
reverse, which is the whole difficulty.

## Mathlib boundary

The pinned Mathlib has no `IsCatenary` and no dimension formula, so unlike the
first clause this cannot be assembled from existing pieces. It needs the
catenary property of finitely generated algebras over a field built from
scratch, most likely by induction on the number of generators through Noether
normalisation. Expect this to be the single biggest piece of the chapter, and
expect it to be worth upstreaming.

The transcendence-degree clause is available and does not depend on this one, so
work that only needs `dim B = trdeg_k K(B)` should not be blocked behind it.

## Depends on

- [Dimension of a topological space and of a ring](dimension.md)
- [One inequality of the dimension formula](dim-formula-inequality.md)
- [Krull dimension is invariant under integral extensions](dimension-integral-extension.md)
- [A finitely generated algebra over a field has finite dimension](dim-fg-algebra-finite.md)

## Sources

- [Hartshorne I.1, Theorem 1.8A (p. 6)](../../sources/hartshorne.md#i1)

---
declaration: theorem
origin: background
lean: Hartshorne.exists_ringKrullDim_quotient_eq_trdeg Hartshorne.height_add_ringKrullDim_quotient_eq_of_trdeg
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
`height 𝔭 + dim R/𝔭 ≤ dim R`, in any commutative ring. What remains is the
reverse, which is the whole difficulty.

**The reduction to transcendence degrees is proved**
(`Hartshorne.height_add_ringKrullDim_quotient_eq_of_trdeg`). Part (a) computes
`dim B` as `trdeg_k K(B)`, and it applies verbatim to `B/𝔭`, which is again a
finitely generated domain. So the formula is equivalent to

`trdeg_k K(B) = trdeg_k K(B/𝔭) + height 𝔭`,

and that is what the remaining nodes prove. The reduction is worth isolating
because the two statements are not of the same kind: the original is about the
poset of primes and is what makes a ring catenary, while the transcendence-degree
form is a statement about field extensions, and it is the form the standard
proofs actually establish.

## The remaining decomposition

- [A height-one prime drops the transcendence degree by one](trdeg-drop-height-one.md)
  is the heart. Everything else in the formula follows from it by induction
  along a maximal chain below `𝔭`.
- It rests on [going down](going-down-integral.md) for an integral extension of
  a normal domain, and on
  [the hypersurface computation](polynomial-hypersurface-trdeg.md) in a
  polynomial ring.

## Mathlib boundary

The pinned Mathlib has no `IsCatenary` and no dimension formula. It does have
more of the surrounding machinery than expected: `Algebra.HasGoingDown` and, in
particular, `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`, which is
exactly the height comparison the argument needs.

What is missing is the *hypothesis*: the only instance of `HasGoingDown` upstream
is for flat algebras, and an integral extension is not flat. Supplying the
classical instance is therefore the one genuinely large prerequisite, and it is
a piece of commutative algebra worth upstreaming rather than a piece of
Hartshorne.

The transcendence-degree clause is available and does not depend on this one, so
work that only needs `dim B = trdeg_k K(B)` should not be blocked behind it.

## Depends on

- [Dimension of a topological space and of a ring](dimension.md)
- [One inequality of the dimension formula](dim-formula-inequality.md)
- [Krull dimension is invariant under integral extensions](dimension-integral-extension.md)
- [A finitely generated algebra over a field has finite dimension](dim-fg-algebra-finite.md)
- [A height-one prime drops the transcendence degree by one](trdeg-drop-height-one.md)
- [Dimension of a finitely generated domain](dim-fg-domain.md)

## Sources

- [Hartshorne I.1, Theorem 1.8A (p. 6)](../../sources/hartshorne.md#i1)

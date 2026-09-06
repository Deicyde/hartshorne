---
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: Hartshorne.trdeg_eq_trdeg_quotient_add_height Hartshorne.height_add_ringKrullDim_quotient_eq Hartshorne.exists_ringKrullDim_quotient_eq_trdeg Hartshorne.height_add_ringKrullDim_quotient_eq_of_trdeg Hartshorne.height_lt_height_of_lt Hartshorne.isPrime_map_quotient Hartshorne.comap_map_quotient Hartshorne.comap_lt_comap_quotient Hartshorne.eq_bot_of_comap_eq Hartshorne.height_bot_eq_zero Hartshorne.height_map_quotient_eq_one
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

## How it goes

Part (a) computes `dim B` as `trdeg_k K(B)`, and applies verbatim to `B/𝔭`,
which is again a finitely generated domain. So the formula is equivalent to

`trdeg_k K(B) = trdeg_k K(B/𝔭) + height 𝔭`,

and that is what is proved, by induction on the height. At height zero the prime
is `(0)`. At height `h + 1`, a chain realising the height supplies a prime
`𝔮 < 𝔭` of height `h` — each term of such a chain has its own index as its
height, which is a Mathlib lemma; the height-one case applied to `B/𝔮` and
`𝔭/𝔮` removes one, and the inductive hypothesis applied to `𝔮` removes the rest.

Isolating the transcendence-degree form was worth doing: the original statement
is about the poset of primes and is what makes a ring catenary, while this one
is about field extensions, and it is the form the standard proofs establish.

The pieces, all separate nodes:

- [A height-one prime drops the transcendence degree by one](trdeg-drop-height-one.md),
  the heart;
- its inputs, [the height comparison](height-comap-integral.md) for an integral
  extension of a normal domain and
  [the hypersurface computation](polynomial-hypersurface-trdeg.md);
- and the step lemma, that a consecutive pair of a chain has height one in the
  quotient, which lives here.

## Mathlib boundary

The pinned Mathlib has no `IsCatenary` and no dimension formula. It does have
more of the surrounding machinery than expected: `Algebra.HasGoingDown` and, in
particular, `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`, which is
exactly the height comparison the argument needs.

It also has the going-down instance for an integral extension of an integrally
closed domain, in `IntegralClosure/GoingDown.lean` — which an earlier survey of
this node reported as missing. That was wrong: the instance is anonymous and
sits away from the `HasGoingDown` class, and the search that produced the claim
did not reach it. Nothing about going down needs to be built.

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

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

## What is proved, and what is left

Three of the four pieces are done:

- [A height-one prime drops the transcendence degree by one](trdeg-drop-height-one.md),
  the heart of the argument;
- its two inputs, [the height comparison](height-comap-integral.md) for an
  integral extension of a normal domain, and
  [the hypersurface computation](polynomial-hypersurface-trdeg.md) in a
  polynomial ring.

What remains is the induction from height one to general height, and it needs
exactly one lemma that is not upstream:

**if `𝔮 < 𝔭` are primes with `height 𝔮 = h` and `height 𝔭 = h + 1`, then `𝔭/𝔮`
has height one in `R/𝔮`.**

The content is that nothing lies strictly between `𝔮` and `𝔭`, and that is
forced by the heights rather than assumed: an intermediate `𝔯` would have height
above `h`, and `𝔭` height above that, so at least `h + 2`. With it the induction
is mechanical — apply the height-one result to `B/𝔮`, use
`(B/𝔮)/(𝔭/𝔮) ≅ B/𝔭`, and appeal to the inductive hypothesis for `𝔮`.

An attempt at this lemma is not yet in the repository. The mathematics is three
lines; the care needed is with the correspondence between primes of `R/𝔮` and
primes of `R` above `𝔮`, and with the fact that strict monotonicity of height
lives on `Order.height` over `PrimeSpectrum` rather than on `Ideal.height`.

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

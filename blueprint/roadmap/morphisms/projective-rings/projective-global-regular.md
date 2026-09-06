---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.exists_const_eq_globalRegular Hartshorne.eval_eq_zero_of_eval_eq_zero_on_open Hartshorne.inter_inter_nonempty Hartshorne.mk_cross_eq Hartshorne.mk_X_pow_ne_zero
---

# The global regular functions of a projective variety

**Theorem 3.4(a)**: for `Y` a projective variety, `𝒪(Y) = k`.

A global regular `f` lies in every `A(Yᵢ)`, so `xᵢ^{Nᵢ} f ∈ S(Y)` for each `i`;
choosing `N ≥ Σ Nᵢ` gives `S(Y)_N · f ⊆ S(Y)_N`, iterating gives `S(Y)[f]` inside
a finitely generated `S(Y)`-module, so `f` is integral over `S(Y)`. Taking
degree-zero components of an integral equation puts the coefficients in
`S(Y)₀ = k`, and `k` is algebraically closed, so `f ∈ k`.

That `𝒪(Y) = k` is the structural reason projective varieties need sheaf
cohomology rather than global functions, and it is the motivation Hartshorne
gives for Chapters II and III.

## Status

Independent of everything the other two parts needed. The argument has no affine
analogue and no reduction to one chart: it uses the whole affine cover at once,
and the finiteness it turns on is a statement about the graded pieces of `S(Y)`
rather than about germs or fractions.

Every ingredient is proved, but they do not yet compose; see *What is left*.

**The integrality core** and the finiteness it consumes are
[their own node](stable-subspace.md): an element stabilising a nonzero
finite-dimensional subspace is integral, hence constant over an algebraically
closed field, and each graded piece of `S(Y)` is finite-dimensional.

**The common home.** A global regular function and the graded pieces of `S(Y)`
have nothing to do with each other until both sit inside `K(Y)`, so `𝒪(X)` has
to embed in `K(X)` over the abstract structure; that too is
[its own node](../global-regular-in-function-field.md), along with the
compatibilities that make readings on different charts comparable.

**The chart reading** and **the degree bound** are each
[their](chart-reading.md) [own](degree-bound.md) node: a global regular function
is a ratio of forms on each chart that meets `Y`, and once it is, a large enough
graded piece of `S(Y)` is carried into itself.

## Why the reading has to be pointwise

The first attempt at the assembly failed, and the failure is worth recording,
because it is the sort of thing Hartshorne's notation hides completely.

The degree bound needs a *single* `t ∈ Frac(S(Y))` with `xᵢ^{Nᵢ} t ∈ S(Y)` for
every chart. Phrased inside the function field, the chart reading gives, for
each `i`, an equation whose right-hand side is `Φᵢ(f)`, where
`Φᵢ : K(Y) ≅ S(Y)_((0))` is [part (c)](projective-function-field.md)'s
isomorphism — built through the chart `Uᵢ`. Different charts give different
terms, and nothing says they agree, so the equations do not combine. Hartshorne
has no such difficulty because he treats `K(Y)` and `S(Y)_((0))` as the same
field from the start; the identification is used once and never named.

Pointwise the question does not arise: the values of `f` are what they are, and
no identification is involved. So the fix was not to compare the `Φᵢ`, nor to
rebuild them chart-free, but to avoid them.

## The assembly

With the pointwise reading, the two charts are compared only once and directly.
If `f` is `gᵢ/xᵢ^{Nᵢ}` on `Uᵢ` and `g_{i₀}/x_{i₀}^{N_{i₀}}` on `U_{i₀}`, then

`g_{i₀} · xᵢ^{Nᵢ} = gᵢ · x_{i₀}^{N_{i₀}}` in `S(Y)`,

because both sides are homogeneous of the same degree and agree on
`Y ∩ Uᵢ ∩ U_{i₀}` — a nonempty open subset of an irreducible space, hence
enough. That makes `t := [g_{i₀}]/[x_{i₀}]^{N_{i₀}}` satisfy the degree bound's
hypothesis for every chart at once, and the rest follows: `t` stabilises
`S(Y)_N`, which is nonzero because `[xᵢ₀]^N ≠ 0` and finite-dimensional, so `t`
is a constant `c`; then `f = c` on `U_{i₀}` and, by the identity principle, on
`Y`.

Irreducibility is used exactly twice, both times to move a statement off a
chart onto all of `Y`: once for the cross equation, once at the end.

## Depends on

- [The ring of regular functions](../ring-of-regular-functions.md)
- [Global regular functions inside the function field](../global-regular-in-function-field.md)
- [An element stabilising a finite-dimensional subspace is integral](stable-subspace.md)
- [Reading a global regular function on a chart](chart-reading.md)
- [The degree bound](degree-bound.md)
- [Graded localization](graded-localization.md)
- [The homogeneous vanishing ideal](../../projective-varieties/homogeneous-vanishing-ideal.md)

## Proof depends on

- [The coordinate ring is the ring of regular functions](../global-regular-eq-coordinate-ring.md)
- [The charts are isomorphisms of varieties](chart-isomorphism.md)
- [Varieties are covered by affine pieces](../../projective-varieties/affine-cover.md)

## Sources

- [Hartshorne I.3, Theorem 3.4(a) (pp. 18-19)](../../../sources/hartshorne.md#i3)

---
declaration: theorem
origin: cited
lean: Hartshorne.restrictFunctionFieldEquiv Hartshorne.chartFunctionFieldEquiv Hartshorne.restrictFunctionFieldEquiv_globalToFunctionField Hartshorne.chartFunctionFieldEquiv_symm_globalToFunctionField Hartshorne.exists_coordToRational_eq_of_globalRegular Hartshorne.exists_awayToAtPrime_eq_of_globalRegular Hartshorne.mk_X_eq_zero_of_inter_eq_empty Hartshorne.exists_le_of_degree_le Hartshorne.monomial_eq_mul_X_pow Hartshorne.degree_sub_single Hartshorne.gradedImage Hartshorne.mul_mem_gradedImage
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

**The chart reading.** With those in hand, the image of a global regular
function in `K(Y)` lies in the image of `A(Yᵢ)`
(`Hartshorne.exists_coordToRational_eq_of_globalRegular Hartshorne.exists_awayToAtPrime_eq_of_globalRegular Hartshorne.mk_X_eq_zero_of_inter_eq_empty Hartshorne.exists_le_of_degree_le Hartshorne.monomial_eq_mul_X_pow Hartshorne.degree_sub_single Hartshorne.gradedImage Hartshorne.mul_mem_gradedImage`) — the sentence "`f` is
regular on `Yᵢ`, so `f ∈ A(Yᵢ)`" that Hartshorne's proof opens with. It is a
chase along the three isomorphisms identifying `K(Y)` with the affine chart's
function field, checking at each step that a global regular function stays one.
Making it possible meant naming the three components of that identification
instead of leaving it a single composite: a `let`-bound chain of `RingEquiv`s
computes on no element.

Nothing in the chase is deep, and none of it was available from parts (b) and
(c): they moved one *ring* across the chart isomorphism, while this moves an
*element* and has to know where it lands.

**`f = gᵢ/xᵢ^{Nᵢ}`.** Pushing that through `A(Yᵢ) ≅ S(Y)_(xᵢ)` and
[part (c)](projective-function-field.md) puts the image of `f` in `S(Y)_((0))`
inside the image of `S(Y)_(xᵢ)`
(`Hartshorne.exists_awayToAtPrime_eq_of_globalRegular Hartshorne.mk_X_eq_zero_of_inter_eq_empty Hartshorne.exists_le_of_degree_le Hartshorne.monomial_eq_mul_X_pow Hartshorne.degree_sub_single Hartshorne.gradedImage Hartshorne.mul_mem_gradedImage`). That is Hartshorne's
`xᵢ^{Nᵢ} f ∈ S(Y)`, with the power of `xᵢ` kept inside the graded localisation
rather than written out. It is short because every map involved commutes with
`algebraMap`, so the image of `A(Yᵢ)` is carried where it should go.

**The degree bound** (`Hartshorne.mul_mem_gradedImage`): if `xᵢ^{Nᵢ} · t` lies
in `S(Y)` for every chart meeting `Y`, then `t · S(Y)_N ⊆ S(Y)_N` inside
`Frac(S(Y))`, for any `N` at least the sum of the `Nᵢ`. This is Hartshorne's
"let `N ≥ Σ Nᵢ`", the only combinatorial step in the whole part and the only
place the cover being finite is used.

`S(Y)_N` is spanned by classes of degree-`N` monomials, so it suffices to treat
`x^α`, and there are two cases. If some `αᵢ > 0` with `Y ∩ Uᵢ` empty then `xᵢ`
vanishes on `Y`, the class of `x^α` is zero, and there is nothing to check.
Otherwise `α` is supported on the charts that do meet `Y`, and `Σ αᵢ = N ≥ Σ Nᵢ`
over those forces `αᵢ ≥ Nᵢ` for some `i`; then `x^α` absorbs the denominator and
`x^α · t = (x^α/xᵢ^{Nᵢ}) · gᵢ` has degree `(N − Nᵢ) + Nᵢ`.

## What is left

Assembling — and it does not go through yet, for a reason worth recording,
because it is the sort of thing Hartshorne's notation hides completely.

The degree bound needs a *single* `t ∈ Frac(S(Y))` with `xᵢ^{Nᵢ} t ∈ S(Y)` for
every chart. What the chart reading produces is, for each `i`, an equation whose
right-hand side is `Φᵢ(f)`, where `Φᵢ : K(Y) ≅ S(Y)_((0))` is
[part (c)](projective-function-field.md)'s isomorphism — and that isomorphism is
built through the chart `Uᵢ`. Different charts give different terms `Φᵢ(f)`, and
nothing so far says they are the same element. Until they are, the per-chart
equations cannot be combined.

Hartshorne has no such difficulty because he treats `K(Y)` and `S(Y)_((0))` as
literally the same field from the start, so the identification is used once and
never named. Formally it has to be constructed, and it was constructed one chart
at a time, which is exactly what parts (b) and (c) wanted and what part (a) does
not.

Two ways out, of which the second looks better:

- prove the `Φᵢ` agree, a cocycle condition comparing two charts; or
- build `K(Y) ≅ S(Y)_((0))` chart-free. That is available: an element of
  `S(Y)_((0))` is `[g]/[h]` with `g, h` homogeneous of the same degree, and it
  defines a rational function directly — `P ↦ g(P)/h(P)` on the open set where
  `h ≠ 0`, which is well defined because the degrees agree and regular by the
  definition of regular on a projective variety. Surjectivity is that definition
  read backwards, and injectivity is that a nonzero fraction is nonzero
  somewhere. Both directions are pointwise checks, with no chart in sight.

The second also gives a cleaner statement of part (c) than the one now proved.

After that, the assembly is as expected: feed the chart readings into the degree
bound, check that `S(Y)_N` is nonzero and finite-dimensional so the integrality
core applies, and translate back along the injection of `𝒪(Y)` into `K(Y)`.
Nonvanishing of `S(Y)_N` is short — a point of `Y` lies in some chart, so `xᵢ`
does not vanish on `Y` and `[xᵢ]^N ≠ 0`.

## Depends on

- [The ring of regular functions](../ring-of-regular-functions.md)
- [Global regular functions inside the function field](../global-regular-in-function-field.md)
- [An element stabilising a finite-dimensional subspace is integral](stable-subspace.md)
- [Graded localization](graded-localization.md)
- [The homogeneous vanishing ideal](../../projective-varieties/homogeneous-vanishing-ideal.md)

## Proof depends on

- [The coordinate ring is the ring of regular functions](../global-regular-eq-coordinate-ring.md)
- [The charts are isomorphisms of varieties](chart-isomorphism.md)
- [Varieties are covered by affine pieces](../../projective-varieties/affine-cover.md)

## Sources

- [Hartshorne I.3, Theorem 3.4(a) (pp. 18-19)](../../../sources/hartshorne.md#i3)

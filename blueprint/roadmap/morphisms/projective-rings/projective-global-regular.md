---
declaration: theorem
origin: cited
lean: Hartshorne.isIntegral_of_mul_mem Hartshorne.exists_algebraMap_eq_of_isIntegral Hartshorne.exists_algebraMap_eq_of_mul_mem Hartshorne.fg_projCoordGrading Hartshorne.finiteDimensional_projCoordGrading Hartshorne.Variety.globalRationalRep Hartshorne.Variety.globalToFunctionField Hartshorne.Variety.globalToFunctionField_injective Hartshorne.VarietyHom.globalPullback Hartshorne.VarietyHom.functionFieldHom_globalToFunctionField Hartshorne.coordToRational_eq_globalToFunctionField Hartshorne.VarietyHom.globalPullback_id Hartshorne.VarietyHom.globalPullback_comp Hartshorne.restrictFunctionFieldEquiv Hartshorne.chartFunctionFieldEquiv Hartshorne.restrictFunctionFieldEquiv_globalToFunctionField Hartshorne.chartFunctionFieldEquiv_symm_globalToFunctionField Hartshorne.exists_coordToRational_eq_of_globalRegular Hartshorne.exists_awayToAtPrime_eq_of_globalRegular Hartshorne.mk_X_eq_zero_of_inter_eq_empty Hartshorne.exists_le_of_degree_le Hartshorne.monomial_eq_mul_X_pow Hartshorne.degree_sub_single Hartshorne.gradedImage Hartshorne.mul_mem_gradedImage
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

Two of the three ingredients are proved, and they are the ones with content.

**The integrality core** (`Hartshorne.exists_algebraMap_eq_of_mul_mem`), stated
with the geometry removed: if `K` is a `k`-algebra domain, `V ⊆ K` a nonzero
finite-dimensional `k`-subspace, and `f · V ⊆ V`, then `f` is integral over `k`,
and lies in `k` when `k` is algebraically closed. What makes `f · V ⊆ V` give
integrality rather than mere algebraicity is the determinant trick, and Mathlib
supplies it as `IsIntegral.of_mem_of_fg`: it is enough that `k[f]` be a finitely
generated `k`-module, which holds because `a ↦ a · v` embeds `k[f]` into `V` for
any nonzero `v ∈ V`, injectively because `K` is a domain.

**The finiteness** (`Hartshorne.finiteDimensional_projCoordGrading`): each graded
piece of `S(Y)` is a finite-dimensional `k`-vector space, being the image of a
graded piece of the polynomial ring, which is finitely generated when there are
finitely many variables.

**The common home.** A global regular function and the graded pieces of `S(Y)`
have nothing to do with each other until both sit inside `K(Y)`, so `𝒪(X)` has
to embed in `K(X)` over the abstract structure
(`Hartshorne.Variety.globalToFunctionField`). That is free — a global regular
function is a rational function whose domain happens to be everything, and
injectivity is that the overlap of two everywhere-defined domains is
everything. Parts (b) and (c) never needed it, because they worked one chart at
a time and a chart supplies its own ambient ring.

Two compatibilities come with it, and they are what make the chart readings
comparable: the embedding commutes with pullback along a dominant morphism
(`functionFieldHom_globalToFunctionField`), and on an affine variety the two
routes from `A(Y)` into `K(Y)` — through Theorem 3.2(a) as a global regular
function, or directly as a rational function — agree
(`coordToRational_eq_globalToFunctionField`). Both are `Quotient.sound` on
representatives that are literally the same function.

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

Assembling. Every ingredient is proved; what remains is to put them together:
feed the chart readings into the degree bound to get `t · S(Y)_N ⊆ S(Y)_N`,
check that `S(Y)_N` is nonzero and finite-dimensional so that the integrality
core applies, and translate "`t` is a constant in `Frac(S(Y))`" back into
"`f ∈ k`" along the injection of `𝒪(Y)` into the function field.

Nonvanishing of `S(Y)_N` is the one thing not yet recorded, and it is short: a
point of `Y` lies in some chart, so `xᵢ` does not vanish on `Y` and `[xᵢ]^N ≠ 0`.

## Depends on

- [The ring of regular functions](../ring-of-regular-functions.md)
- [Graded localization](graded-localization.md)
- [The homogeneous vanishing ideal](../../projective-varieties/homogeneous-vanishing-ideal.md)

## Proof depends on

- [The coordinate ring is the ring of regular functions](../global-regular-eq-coordinate-ring.md)
- [The charts are isomorphisms of varieties](chart-isomorphism.md)
- [Varieties are covered by affine pieces](../../projective-varieties/affine-cover.md)

## Sources

- [Hartshorne I.3, Theorem 3.4(a) (pp. 18-19)](../../../sources/hartshorne.md#i3)

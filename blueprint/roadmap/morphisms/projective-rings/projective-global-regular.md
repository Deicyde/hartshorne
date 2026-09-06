---
declaration: theorem
origin: cited
lean: Hartshorne.isIntegral_of_mul_mem Hartshorne.exists_algebraMap_eq_of_isIntegral Hartshorne.exists_algebraMap_eq_of_mul_mem Hartshorne.fg_projCoordGrading Hartshorne.finiteDimensional_projCoordGrading Hartshorne.Variety.globalRationalRep Hartshorne.Variety.globalToFunctionField Hartshorne.Variety.globalToFunctionField_injective Hartshorne.VarietyHom.globalPullback Hartshorne.VarietyHom.functionFieldHom_globalToFunctionField Hartshorne.coordToRational_eq_globalToFunctionField
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

## What is left

Two things, and this is where (a) is genuinely harder than (b) and (c) rather
than merely different: those two travelled one chart at a time, while this one
needs every chart inside one ring at once.

- Assembling the above into the statement that the image of `f` in `S(Y)_((0))`
  lies in the image of `S(Y)_(xᵢ)` — that is, that `f = gᵢ/xᵢ^{Nᵢ}`. The pieces
  are the two compatibilities, the chart isomorphism, and
  [part (c)](projective-function-field.md), which already identifies `K(Y)` with
  `S(Y)_((0))`.
- The degree bookkeeping: choosing `N ≥ Σ Nᵢ` so that `S(Y)_N · f ⊆ S(Y)_N`.
  This is combinatorics over the finite index set, and it is the only place the
  cover being finite is used.

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

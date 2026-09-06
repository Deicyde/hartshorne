---
declaration: theorem
origin: cited
lean: Hartshorne.isIntegral_of_mul_mem Hartshorne.exists_algebraMap_eq_of_isIntegral Hartshorne.exists_algebraMap_eq_of_mul_mem Hartshorne.fg_projCoordGrading Hartshorne.finiteDimensional_projCoordGrading
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

## What is left

The plumbing, which is where this part is genuinely harder than (b) and (c)
rather than merely different. Those two travelled one chart at a time; this one
needs all the charts inside one ring at once, and that ring is `K(Y)`. Three
things are missing:

- a map `𝒪(Y) → K(Y)` for an abstract variety, so that a global regular function
  and the graded pieces of `S(Y)` live in the same place — the affine version of
  this is [the injections node](../function-field-injections.md), stated in
  affine coordinates;
- the statement that a global regular `f`, restricted to `Yᵢ` and read through
  `A(Yᵢ) ≅ S(Y)_(xᵢ)`, is `gᵢ/xᵢ^{Nᵢ}` — that is, that all the chart readings of
  `f` are the same element of `K(Y)`;
- the degree bookkeeping: choosing `N ≥ Σ Nᵢ` so that `S(Y)_N · f ⊆ S(Y)_N`,
  which is where the cover being finite is used.

The third is combinatorics over the finite index set; the first two are the same
kind of transport work that parts (b) and (c) needed, and none of it is
available from them, since neither ever had to compare different charts.

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

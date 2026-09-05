---
declaration: theorem
origin: cited
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

Not started, and independent of everything the other two parts needed. The
argument has no affine analogue and no reduction to one chart: it uses the whole
affine cover at once, and the finiteness it turns on is a statement about the
graded pieces of `S(Y)` rather than about germs or fractions.

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

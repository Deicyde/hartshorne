---
article_id: af_70d46bb56536a432530278f4
---

# Nonsingular varieties

Nonsingularity is the algebraic substitute for being a manifold. Hartshorne
first defines it for an affine variety `Y ⊆ 𝔸ⁿ` by differentiating generators
of `I(Y)`: at a point `P`, the Jacobian must have the largest rank allowed by
the dimension of `Y`. Theorem 5.1 then proves that this coordinate condition is
intrinsic. It says exactly that the local ring `𝒪_{P,Y}` is regular, meaning
that the cotangent space `𝔪_P/𝔪_P²` has dimension `dim 𝒪_{P,Y}`.

The comparison is the heart of this milestone. The derivative at `P`
identifies the cotangent space of ambient affine space with `kⁿ`; quotienting
by the equations of `Y` removes the span of their gradients. This gives

`dim_k(𝔪_P/𝔪_P²) + rank J(P) = n`,

so the Jacobian criterion follows from `dim 𝒪_{P,Y} = dim Y`.

Theorem 5.3 has two further ingredients. Proposition 5.2A bounds the dimension
of a local ring by the dimension of its cotangent space, so the Jacobian rank is
always at most `n − dim Y`; consequently singularity is detected by the
vanishing of maximal minors and is closed. Properness reduces birationally to
an irreducible hypersurface. Such a hypersurface cannot have every partial
derivative vanish: in characteristic zero this is immediate, while in
characteristic `p` it would make its defining polynomial a `p`th power over the
algebraically closed base field.

## Mathlib boundary

The pinned Mathlib already contains the exact
`IsRegularLocalRing.iff_finrank_cotangentSpace` criterion,
`MvPolynomial.pderiv`, the polynomial Kähler basis and its partial-derivative
coordinate formula, and a local Jacobian criterion for formal smoothness. It
also has `Scheme.Hom.isOpen_smoothLocus` and
`Scheme.Hom.dense_smoothLocus_of_perfectField`. It does not identify those
scheme-theoretic notions with this project's classical point-set varieties or
their germ local rings. The roadmap therefore reuses the local-algebra
primitives but follows Hartshorne's explicit Jacobian-minor and
birational-hypersurface proof for Theorem 5.3.

## Local algebra and the Jacobian criterion

- [Regular local rings](regular-local-rings.md)
- [The cotangent-dimension bound](cotangent-dimension-bound.md)
- [Local rings are unchanged on open neighbourhoods](local-ring-open-invariance.md)
- [The cotangent space of affine space](ambient-cotangent-space.md)
- [The defining ideal and the local cotangent space](defining-ideal-cotangent-sequence.md)
- [Jacobian rank is independent of generators](jacobian-rank-invariance.md)
- [Nonsingular points of an affine variety](affine-nonsingular-points.md)
- [The Jacobian criterion](jacobian-criterion.md)
- [Intrinsic nonsingularity](intrinsic-nonsingularity.md)

## The singular locus is closed

- [The Jacobian rank bound](jacobian-rank-upper-bound.md)
- [Rank-drop loci are determinantal](determinantal-rank-locus.md)
- [The affine singular locus is closed](affine-singular-locus-closed.md)
- [Closedness from affine charts](singular-locus-closed.md)

## The singular locus is proper

- [An irreducible polynomial has a nonzero partial derivative](irreducible-polynomial-nonzero-partial.md)
- [An irreducible hypersurface has a nonsingular point](hypersurface-singular-locus-proper.md)
- [The singular locus is proper and closed](singular-locus.md)

## Scope note

This chapter stops with Theorem 5.3 on printed p. 33. Completion, the Cohen
structure theorem, and analytic isomorphism are deferred to a separately
approved milestone; Theorem 5.7A and the exercises are out of scope. See the
[coverage contract](../../coverage/README.md).

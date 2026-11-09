---
article_id: af_bcf6a1198ea68985d9ce07ea
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.smoothOfRelativeDimension_iff_flat_and_fiber_dim_and_finrank Hartshorne.flat_and_fiber_dim_and_finrank_of_smoothOfRelativeDimension Hartshorne.smoothOfRelativeDimension_of_flat_of_fiber_dim_of_finrank Hartshorne.exists_finrank_fibre_pullback_snd_eq Hartshorne.finrank_tensor_kaehler_fiber AlgebraicGeometry.Scheme.smoothOfRelativeDimension_of_flat_of_smooth_fiber AlgebraicGeometry.Scheme.smoothOfRelativeDimension_of_smooth_of_finrank_fibre AlgebraicGeometry.Scheme.smoothOfRelativeDimension_iff_smooth_and_finrank_fibre
---

# Hartshorne's smoothness criterion

For a morphism $f:X\to Y$ of schemes of finite type over a field,
smoothness of relative dimension $n$ is equivalent to the
following conditions:

1. $f$ is flat;
2. every irreducible component of every scheme-theoretic fibre has dimension
   $n$; and
3. for every $x \in X$, the $k(x)$-dimension of
   $(\Omega_{X/Y})_x \otimes k(x)$ is $n$.

The fibre formulation of clause 2 is equivalent to Hartshorne's formulation
using corresponding components by III.9.6. This theorem is the sole bridge
between Hartshorne's definition and the adopted modern predicate.

## Depends on

- [Relative differentials of a smooth morphism](relative-differentials-rank-of-smooth.md)
- [The stalk criterion for flat morphisms](../../flat-families/flatness/flat-morphism-stalk-criterion.md)
- [Equidimensionality in a flat family](../../flat-families/families-hilbert/flat-equidimensional-total-space-iff-fibers.md)
- [The fibre of a morphism](../../../schemes/fiber-products/scheme-fiber.md)

## Proof depends on

- The affine-local standard-smooth characterization of smoothness.
- [Dimension of a scheme smooth over a field](smooth-over-field-component-dimension.md)
- [The differential criterion for smoothness over a field](differential-criterion-smooth-over-field.md)
- [The differential criterion for a scheme over a field](differential-criterion-smooth-scheme-over-field.md)
- [Flat morphisms with smooth fibres are smooth](flat-smooth-fibers-smooth.md)
- [Dimension after extending the ground field](../../../schemes/fiber-products/base-extension-component-dimension.md)

## Sources

- [Hartshorne III.10, definition on p.268](../../../../sources/hartshorne-iii-10.md#smoothness-and-geometric-fibres-pp268270)
- [Hartshorne III.9, Corollary 9.6](../../../../sources/hartshorne-iii-9.md#dimensions-associated-points-and-flat-limits-pp256261)

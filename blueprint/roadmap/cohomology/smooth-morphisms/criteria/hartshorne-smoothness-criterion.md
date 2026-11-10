---
article_id: af_bcf6a1198ea68985d9ce07ea
declaration: theorem
origin: bridged
statement: retracted
lean: Hartshorne.smoothOfRelativeDimension_iff_flat_and_fiber_dim_and_finrank Hartshorne.flat_and_fiber_dim_and_finrank_of_smoothOfRelativeDimension Hartshorne.smoothOfRelativeDimension_of_flat_of_fiber_dim_of_finrank Hartshorne.finrank_tensor_kaehler_fiber AlgebraicGeometry.Scheme.smoothOfRelativeDimension_of_flat_of_smooth_fiber
---

# Hartshorne's smoothness criterion

For a morphism $f:X\to Y$ of schemes of finite type over a field,
smoothness of relative dimension $n$ is equivalent to the
following conditions:

1. $f$ is flat;
2. if $X' \subseteq X$ and $Y' \subseteq Y$ are irreducible components such
   that $f(X') \subseteq Y'$, then $\dim X' = \dim Y' + n$; and
3. for every $x \in X$, the $k(x)$-dimension of
   $(\Omega_{X/Y})_x \otimes k(x)$ is $n$.

For flat $f$, condition 2 is equivalent to: every irreducible component of
every scheme-theoretic fibre has dimension $n$. A flat morphism satisfies
going-down, so it sends the generic point of an irreducible component of $X$
to the generic point of an irreducible component of $Y$; the equivalence then
follows from Proposition III.9.5 at a closed point of a fibre lying on a single
irreducible component of that fibre. This theorem is the sole bridge between
Hartshorne's definition and the adopted modern predicate.

## Depends on

- [Relative differentials of a smooth morphism](relative-differentials-rank-of-smooth.md)
- [The stalk criterion for flat morphisms](../../flat-families/flatness/flat-morphism-stalk-criterion.md)
- [The fibre of a morphism](../../../schemes/fiber-products/scheme-fiber.md)
- [Dimension of a scheme](../../../schemes/subschemes-and-dimension/scheme-dimension.md)

## Proof depends on

- The affine-local standard-smooth characterization of smoothness.
- Flat morphisms satisfy going-down.
- [The local dimension formula for a flat fibre](../../flat-families/families-hilbert/flat-fiber-local-dimension-formula.md)
- [Equidimensionality in a flat family](../../flat-families/families-hilbert/flat-equidimensional-total-space-iff-fibers.md)
- [Dimension of a scheme smooth over a field](smooth-over-field-component-dimension.md)
- [The differential criterion for smoothness over a field](differential-criterion-smooth-over-field.md)
- [The differential criterion for a scheme over a field](differential-criterion-smooth-scheme-over-field.md)
- [Flat morphisms with smooth fibres are smooth](flat-smooth-fibers-smooth.md)
- [Dimension after extending the ground field](../../../schemes/fiber-products/base-extension-component-dimension.md)
- [Differentials on affine schemes](../../../schemes/differentials/scheme-differentials/affine-relative-differentials.md)

## Sources

- [Hartshorne III.10, definition on p.268](../../../../sources/hartshorne-iii-10.md#smoothness-and-geometric-fibres-pp268270)
- [Hartshorne III.9, Proposition 9.5 and Corollary 9.6](../../../../sources/hartshorne-iii-9.md#dimensions-associated-points-and-flat-limits-pp256261)

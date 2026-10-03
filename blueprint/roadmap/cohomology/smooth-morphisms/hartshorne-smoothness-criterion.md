---
declaration: theorem
origin: bridged
source_units: [chapter-iii-section-10]
---

# Hartshorne's smoothness criterion

For a morphism `f : X -> Y` of schemes of finite type over a field, Mathlib's
predicate `SmoothOfRelativeDimension n f` is equivalent to the conjunction:

1. `f` is flat;
2. every irreducible component of every scheme-theoretic fibre has dimension
   `n`; and
3. for every `x : X`, the `k(x)`-dimension of
   `Omega[X/Y]_x tensor k(x)` is `n`.

The fibre formulation of clause 2 is equivalent to Hartshorne's formulation
using corresponding components by III.9.6. This theorem is the sole bridge
between Hartshorne's definition and the adopted modern predicate.

## Depends on

- [Relative differentials of a smooth morphism](relative-differentials-rank-of-smooth.md)
- [The stalk criterion for flat morphisms](../flat-families/flatness/flat-morphism-stalk-criterion.md)
- [Equidimensionality in a flat family](../flat-families/families-hilbert/flat-equidimensional-total-space-iff-fibers.md)
- [The fibre of a morphism](../../schemes/fiber-products/scheme-fiber.md)

## Proof depends on

- The affine-local standard-smooth characterization of `Smooth` in pinned
  Mathlib and the fibre-dimension theorem for standard-smooth algebras.
- [Dimension after extending the ground field](../../schemes/fiber-products/base-extension-component-dimension.md)

## Sources

- [Hartshorne III.10, definition on p.268](../../../sources/hartshorne-iii-10.md#smoothness-and-geometric-fibres-pp268270)
- [Hartshorne III.9, Corollary 9.6](../../../sources/hartshorne-iii-9.md#dimensions-associated-points-and-flat-limits-pp256261)

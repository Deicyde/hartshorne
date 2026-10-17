---
article_id: af_5584498281d3b787791b3dc4
declaration: theorem
origin: bridged
source_units: [chapter-iii-section-10]
---

# Projective space is smooth over an arbitrary base

For every scheme `Y`, the projection `P^n_Y → Y` is smooth of relative
dimension `n`.

This modern arbitrary-base theorem is the reusable strengthening from which
Hartshorne's fixed-field, finite-type example follows. Keeping it separate
prevents the stronger implementation statement from being attributed to a
source section whose standing convention is finite type over a field.

## Depends on

- [Affine space is smooth](affine-space-smooth.md)
- [Smooth relative-dimension calculus](../criteria/smooth-relative-dimension-calculus.md)
- [Projective space over a scheme](../../../schemes/proper-and-projective/projective-space-over-scheme.md)
- [The standard opens cover Proj](../../../schemes/projective-spectrum/proj-basic-open-cover.md)

## Proof depends on

- The coordinate opens `D₊(Xᵢ)` cover projective space, and dehomogenization
  identifies each coordinate chart with affine `n`-space over the base.
- Smoothness and relative dimension are local on the source.
- Smoothness of relative dimension `n` is stable under base change.

## Sources

- [Hartshorne III.10, Example 10.0.1 and the section's fixed-field convention](../../../../sources/hartshorne-iii-10.md#smoothness-and-geometric-fibres-pp268270)

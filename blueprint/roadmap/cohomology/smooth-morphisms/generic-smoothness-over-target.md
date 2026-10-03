---
declaration: theorem
origin: cited
source_units: [chapter-iii-section-10]
---

# Generic smoothness over the target

Let `f : X -> Y` be a morphism of varieties over an algebraically closed field
of characteristic zero, with `X` nonsingular. There is a nonempty open
`V subset Y` such that `f^-1(V) -> V` is smooth.

No dominance hypothesis is imposed. If the image of `f` is not dense, `V`
may be chosen disjoint from its closure and the restricted source is empty.

## Depends on

- [The tangent-rank image-dimension bound](tangent-rank-image-dimension.md)
- [Smoothness by tangent-map surjectivity](smooth-iff-tangent-surjective.md)
- [The dense nonsingular locus](../../schemes/differentials/scheme-differentials/dense-nonsingular-locus.md)

## Proof depends on

- Remove the image closure of the locus on which the tangent rank is less
  than `dim Y`, after replacing `Y` by its dense nonsingular open.

## Sources

- [Hartshorne III.10, Corollary 10.7, p.272](../../../sources/hartshorne-iii-10.md#characteristic-zero-generic-smoothness-pp271272)
- [Stacks Project, related dense-smooth-locus result, tag 056V](../../../sources/hartshorne-iii-10.md#characteristic-zero-generic-smoothness-pp271272)

---
article_id: af_0284303ce744725599fae034
declaration: theorem
origin: cited
source_units: [chapter-v-section-5]
---

# Negative rational curves contract projectively

Let `Y ~= P^1` be a curve on a nonsingular projective surface `X`. If
`Y^2<0`, then there is a birational morphism to a projective surface, possibly
singular, which contracts exactly `Y` to a point and is an isomorphism away
from `Y`.

## Depends on

- [Serre vanishing](../../../cohomology/projective-cohomology/serre-vanishing.md)
- [Top cohomology of twists on projective space](../../../cohomology/projective-cohomology/projective-space-top-twist-cohomology.md)
- [Generation by global sections](../../../schemes/projective-sheaves/globally-generated-module-sheaf.md)
- [Morphisms from generated invertible sheaves](../../../schemes/projective-geometry/linear-systems-ampleness/morphism-from-generated-line-bundle.md)
- [Separation of points and tangent vectors](../../../schemes/projective-geometry/linear-systems-ampleness/separates-points-tangents-iff-closed-immersion.md)

## Proof depends on

- Write `Y^2=-n`, choose a very ample `H` with `H.Y` a positive multiple
  `k*n`, and run the restriction-sequence cohomology ladder for
  `O_X(H+iY)` through `i=k`.
- The bundle `O_X(H+kY)` is globally generated, trivial on `Y`, and separates
  points and tangent vectors away from `Y`; its morphism contracts exactly
  `Y`. No regularity of the image point is asserted.

## Sources

- [Hartshorne V.5, Exercise 5.2 and Remark 5.7.2, pp.417,419](../../../../sources/hartshorne-v-5.md#exercise-disposition-printed-pp419420)

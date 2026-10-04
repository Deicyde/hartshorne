---
article_id: af_61c5c0ca06c160f3261905d3
declaration: theorem
origin: cited
source_units: [chapter-v-section-2]
---

# Curves on a quadric cone

Let `Y` be a nonsingular curve on a quadric cone `X_0` in `P^3`.

- If `deg Y = 2*a`, with `a>=1`, then `Y` is the complete intersection of
  the cone with a surface of degree `a`, and `g(Y)=(a-1)^2`.
- If `deg Y = 2*a+1`, then `g(Y)=a^2-a`.

This is the ruled-surface calculation quoted forward in Remark IV.6.4.1(d).

## Depends on

- [Blowing up the vertex of a cone gives a ruled surface](../normalization/cone-blowup-ruled-surface.md)
- [Divisor class and intersection of a section](../normalization/section-divisor-class-intersection.md)
- [The canonical divisor of a ruled surface](../normalization/ruled-surface-canonical-divisor.md)
- [Arithmetic genus and adjunction for an effective divisor](../../surface-exercises/effective-divisor-arithmetic-genus-adjunction.md)

## Proof depends on

- Resolve the quadric cone as the invariant-two ruled surface and express the
  strict transform of `Y` in the basis `C0,f`.
- Its intersection with the exceptional section gives the parity alternative;
  adjunction computes the two genus formulas. In the even case the divisor
  class is the pullback of a degree-`a` hypersurface section.

## Sources

- [Hartshorne IV.6, Remark 6.4.1(d), pp.352–353](../../../../sources/hartshorne-iv-6.md#low-degree-and-degree-nine-classifications-pp352355)
- [Hartshorne V.2, Exercise 2.9, p.384](../../../../sources/hartshorne-v-2.md#exercise-disposition-printed-pp383386)

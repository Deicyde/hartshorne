---
declaration: theorem
origin: cited
source_units: [chapter-v-section-2]
---

# Irreducible curves when the invariant is negative

Let `X` be ruled over a genus-`g` curve with `e<0`, and assume either
`char k=0` or `g<=1`. If `Y=a*C0+b*f` is irreducible and distinct from
`C0,f`, then either

- `a=1` and `b>=0`; or
- `a>=2` and `2*b>=a*e`.

No assertion with these exact bounds is made here when `char k=p>0` and
`g>=2`.

## Depends on

- [The canonical divisor of a ruled surface](../normalization/ruled-surface-canonical-divisor.md)
- [Adjunction for an effective divisor](../../surface-exercises/effective-divisor-arithmetic-genus-adjunction.md)
- [Arithmetic genus under normalization](../../../curves/riemann-roch/arithmetic-genus-normalization-formula.md)
- [Riemann–Hurwitz](../../../curves/ramification/riemann-hurwitz.md)
- [Genus is monotone under finite curve maps](../../../curves/ramification/finite-curve-map-genus-monotonicity.md)
- [Divisor class and intersection of a section](../normalization/section-divisor-class-intersection.md)

## Proof depends on

- Normalize `Y` and compare its genus with the base using separable Hurwitz
  in characteristic zero, or genus monotonicity when the base genus is zero
  or one. Adjunction then gives `2b>=ae` for `a>=2`.
- When `a=1`, the section quotient and normalizedness give `b>=0`.

## Sources

- [Hartshorne V.2, Proposition 2.21(a), pp.382–383](../../../../sources/hartshorne-v-2.md)

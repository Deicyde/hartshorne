---
article_id: af_5a51807c2b9f9a6605c9f3c0
declaration: theorem
origin: cited
source_units: [chapter-iv-section-3]
---

# Samuel's Hurwitz calculation

Let `X subset P^3` be a nonline strange curve of degree `d` and genus `g`,
with Samuel's coordinates and strange point `A`. The projection to the line at
infinity in the `xy`-plane is a separable morphism of degree `d`. At each
finite point `P_i` of `X` in the `xz`-plane its different exponent is
`v_(P_i)(y)`, and Riemann–Hurwitz gives

`2*g-2 = -2*d + sum_i v_(P_i)(y)`.

If `A` is not on `X`, this forces `(g,d)=(0,2)` and characteristic two. If
`A` is on `X`, it forces `(g,d)=(0,1)`.

## Depends on

- [Projection from a strange point is inseparable](strange-projection-inseparable.md)
- [Riemann–Hurwitz](../../ramification/riemann-hurwitz.md)
- [Length of the relative-differential stalk](../../ramification/relative-differential-stalk-length.md)
- [Genus zero characterizes the projective line](../../riemann-roch/genus-zero-iff-projective-line.md)
- [Projective intersection degree](../../../schemes/divisors/divisor-exercises/projective-intersection-degree.md)

## Proof depends on

- With `u=x-a` and `t=y/x`, the `p`th-power property gives
  `dt/du=-y*(u+a)^(-2)`.
- Intersecting with the `xz`-plane computes `sum v_P(y)` as `d`, or `d-1`
  when the strange point contributes one transverse intersection.
- Riemann–Roch on `P^1` identifies degree-one and degree-two embeddings with
  a line and a plane conic.
- For the degree-two case, the common-tangent-point condition for a smooth
  conic holds exactly in characteristic two; the Hurwitz equation alone only
  yields `(g,d)=(0,2)`.

## Sources

- [Hartshorne IV.3, numerical proof of Theorem 3.9, pp.312–313](../../../../sources/hartshorne-iv-3.md#nodal-projections-and-bad-secants-pp310314)
- [Samuel, *Lectures on Old and New Results on Algebraic Curves*](../../../../sources/hartshorne-iv-3.md#external-sources-and-blockers)

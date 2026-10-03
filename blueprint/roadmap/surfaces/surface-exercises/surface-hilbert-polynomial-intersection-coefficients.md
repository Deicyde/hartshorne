---
declaration: theorem
origin: cited
source_units: [chapter-v-section-1]
---

# Hilbert-polynomial coefficients and intersection degrees

Let `H` be a very ample divisor on a Chapter-V surface `X`, defining
`X -> P^N`, and write

`P_X(z) = (a/2)*z^2 + b*z + c`.

If `pi` is the genus of a smooth member of `|H|`, then

`a=H^2`, `b=H^2/2+1-pi`, and `c=1+p_a(X)`.

Consequently the embedded degree of `X` is `H^2`; for every curve `C` on
`X`, its degree in this embedding is `C.H`.

## Depends on

- [Surface Riemann–Roch](../numerical-positivity/surface-riemann-roch/surface-riemann-roch.md)
- [Adjunction for a smooth curve on a surface](../intersection-theory/examples-adjunction/surface-curve-adjunction.md)
- [The coherent-sheaf Hilbert polynomial](../../cohomology/projective-cohomology-exercises/coherent-sheaf-hilbert-polynomial.md)
- [Arithmetic genus and the embedded Hilbert polynomial](../../cohomology/projective-cohomology-exercises/arithmetic-genus-hilbert-compatibility.md)

## Proof depends on

- Apply surface Riemann–Roch to `zH` and use adjunction to replace `H.K`
  by `2*pi-2-H^2`.
- Restrict hyperplanes to a curve and identify divisor degree with embedded
  degree.

## Sources

- [Hartshorne V.1, Exercise 1.2, p.366](../../../sources/hartshorne-v-1.md#exercise-disposition-printed-pp366368)

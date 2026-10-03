---
declaration: theorem
origin: cited
source_units: [chapter-v-section-1]
---

# The Hodge index theorem

Let `H` be ample on a Chapter V surface. If `D` is not numerically trivial
and

`D*H=0`,

then `D^2<0`.

This algebraic proof is valid over an algebraically closed field of arbitrary
characteristic.

## Depends on

- [Numerical equivalence and the numerical divisor group](numerical-equivalence-num.md)
- [Positive square gives eventual effectivity](../surface-riemann-roch/positive-square-eventual-effectivity.md)
- [Intersection with an ample divisor is positive degree](../surface-riemann-roch/ample-intersection-degree-positive.md)

## Proof depends on

- If `D^2>0`, apply eventual effectivity to `D` after replacing the ample
  class by `D+nH`, contradicting `D*H=0`.
- If `D^2=0`, choose `E` with `D*E!=0`, replace it by an integral class
  orthogonal to `H`, and choose `n` so `(nD+E)^2>0`, reducing to the first
  case.

## Sources

- [Hartshorne V.1, Theorem 1.9, p.364](../../../../sources/hartshorne-v-1.md)
- Grothendieck, *Sur une note de Mattuck–Tate*.

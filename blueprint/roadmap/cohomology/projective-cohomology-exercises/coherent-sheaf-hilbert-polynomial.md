---
declaration: theorem
origin: cited
source_units: [chapter-iii-section-5]
not_ready: true
---

# The coherent-sheaf Hilbert polynomial

Let `X` be projective over a field, let `O_X(1)` be very ample, and let `F`
be coherent. There is a unique polynomial `P_F∈Q[z]` such that

`χ(F(n))=P_F(n)`

for every integer `n`, positive or negative. Define this polynomial to be the
Hilbert polynomial of `F` relative to `O_X(1)`.

## Depends on

- [Euler characteristic is additive](euler-characteristic-additive.md)
- [Numerical polynomials](../../intersections-projective-space/hilbert/numerical-polynomial.md)
- [Twists and graded shifts](../../schemes/projective-sheaves/proj-twist-compatibility.md)

## Proof depends on

- Induction on `dim Supp(F)` using the kernel and cokernel of a suitable map
  `F(-1)→F`, whose supports have smaller dimension.
- The finite-difference characterization of numerical polynomials.

The exercise fixes the statement but not a complete dimension-lowering proof
over every field; this node remains not ready until that proof is adopted or
written as an explicit project-authored specification.

## Sources

- [Hartshorne III, Exercise 5.2(a), p.230](../../../sources/hartshorne-iii-5.md#adopted-exercises-pp230233)

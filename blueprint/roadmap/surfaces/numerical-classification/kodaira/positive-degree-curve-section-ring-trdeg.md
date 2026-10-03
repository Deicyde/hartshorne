---
declaration: theorem
origin: bridged
source_units: [chapter-v-section-6]
---

# A positive-degree curve section ring has transcendence degree two

Let `C` be a nonsingular projective curve and let `L` be an invertible sheaf
of positive degree. Its section ring

`direct-sum_(n>=0) H^0(C,L^n)`

is a domain of transcendence degree two over the ground field.

## Depends on

- [Section rings embed in a polynomial ring over the function field](canonical-ring-function-field-embedding.md)
- [The Riemann–Roch theorem](../../../curves/riemann-roch/riemann-roch.md)
- [High-degree divisors are nonspecial](../../../curves/riemann-roch/high-degree-divisor-nonspecial.md)

## Proof depends on

- Riemann–Roch gives linear growth of the graded pieces and nonzero sections
  in all sufficiently large degrees.
- Ratios of same-degree sections recover a nonconstant element of `K(C)`;
  together with one positive-degree homogeneous element this gives the lower
  bound two, while the function-field embedding gives the upper bound.

## Sources

- [Hartshorne V.6, Kodaira dimension of curves, p.422](../../../../sources/hartshorne-v-6.md)

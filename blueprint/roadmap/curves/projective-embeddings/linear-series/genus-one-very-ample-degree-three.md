---
declaration: theorem
origin: cited
source_units: [chapter-iv-section-3]
---

# Very ample divisors on a genus-one curve

Let `X` be a Chapter IV curve of genus one. A divisor `D` is very ample if
and only if `deg D >= 3`. Every degree-three divisor has
`dim|D|=2` and embeds `X` as a nonsingular plane cubic. Conversely, a
nonsingular plane cubic has genus one.

Hartshorne's genus-one curve is not assumed to carry a chosen origin.

## Depends on

- [High-degree divisors are generated and very ample](high-degree-basepoint-free-very-ample.md)
- [A curve divisor is ample exactly when its degree is positive](curve-ample-iff-positive-degree.md)
- [The Riemann–Roch theorem](../../riemann-roch/riemann-roch.md)
- [The canonical divisor of a genus-one curve is trivial](../../riemann-roch/genus-one-canonical-trivial.md)
- [Arithmetic genus and the embedded Hilbert polynomial](../../../cohomology/projective-cohomology-exercises/arithmetic-genus-hilbert-compatibility.md)
- [The Hilbert polynomial of a hypersurface](../../../intersections-projective-space/bezout/hypersurface-hilbert-polynomial.md)

## Proof depends on

- Positive-degree divisors on a genus-one curve are nonspecial, so
  Riemann–Roch gives `dim|D|=deg D-1`.
- Degree one or two cannot give a closed immersion; degree at least three is
  covered by the high-degree criterion.

## Sources

- [Hartshorne IV.3, Example 3.3.3, p.309](../../../../sources/hartshorne-iv-3.md)

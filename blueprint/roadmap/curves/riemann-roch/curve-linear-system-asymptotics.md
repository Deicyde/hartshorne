---
declaration: theorem
origin: cited
source_units: [chapter-iv-sections-1-2]
---

# Asymptotic dimensions of complete linear systems

Let `D` be a divisor on a Chapter IV curve of genus `g`.

- If `deg D<0`, then `dim|nD|=-1` for every positive `n`.
- If `deg D=0`, then `dim|nD|=0` when `nD~0` and is `-1` otherwise.
- If `deg D>0`, then for all sufficiently large positive `n`,
  `dim|nD| = n*deg D-g`.

All displayed dimensions are integers, retaining the empty-system value
`-1`.

## Depends on

- [The Riemann–Roch theorem](riemann-roch.md)
- [A divisor with a nonzero section has nonnegative degree](nonzero-sections-nonnegative-degree.md)
- [The degree of a canonical divisor](canonical-divisor-degree.md)

## Proof depends on

- For `n*deg D>deg K`, the divisor `K-nD` has negative degree and hence no
  nonzero section.

## Sources

- [Hartshorne IV.1, Remark 1.3.2, p.296](../../../sources/hartshorne-iv-1.md#consequences-of-riemannroch-printed-pp296297)

---
declaration: theorem
origin: cited
source_units: [chapter-iv-sections-5-6]
---

# The summed Castelnuovo bound

Let `X subset P^3` be a nonplanar curve of degree `d` and genus `g`. Then
`d>=3`. Put `r=floor((d-1)/2)`. One has

`g <= r*d - r*(r+2)`.

Equivalently, if `d=2s` then `g<=(s-1)^2`, while if `d=2s+1` then
`g<=s*(s-1)`.

## Depends on

- [Growth from a general hyperplane section](castelnuovo-hyperplane-increment.md)
- [Asymptotic dimensions of complete linear systems](../../riemann-roch/curve-linear-system-asymptotics.md)

## Proof depends on

- Sum the increment estimates through `n`, then for large `n` compare with
  nonspecial Riemann–Roch: `dim|nD|=n*d-g`.

## Sources

- [Hartshorne IV.6, inequality in Theorem 6.4, pp.351–352](../../../../sources/hartshorne-iv-6.md)

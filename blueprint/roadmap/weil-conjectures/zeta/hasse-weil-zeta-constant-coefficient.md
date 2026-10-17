---
article_id: af_33b90b744269da1932fb678d
declaration: theorem
origin: bridged
source_units: [appendix-c-section-1]
statement: formalized
proof: formalized
lean: Hartshorne.hasseWeilZetaSeries_constantCoeff
---

# The Hasse–Weil zeta series has constant coefficient one

For every finite-type scheme `X` over a finite field,

`constantCoeff (Z(X,t)) = 1`.

This records as a separately checkable theorem the immediate formal-series
consequence of the defining exponential formula.

## Depends on

- [The formal Hasse–Weil zeta series](hasse-weil-zeta-formal-series.md)

## Proof depends on

- The formal exponential has constant coefficient one when its argument has
  constant coefficient zero.

## Sources

- [Consequence of Hartshorne Appendix C.1's zeta-series definition, p.450](../../../sources/hartshorne-appendix-c-1.md#point-counts-and-the-formal-zeta-series-printed-pp449450)

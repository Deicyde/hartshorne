---
article_id: af_2eb3e90cd14f3d6950a47352
declaration: theorem
origin: cited
source_units: [chapter-iv-sections-5-6]
---

# Equality forces hyperellipticity

Let `D` be an effective special divisor, linearly equivalent to neither zero
nor `K`, and

`2 * dim|D| = deg D`.

Then the curve is hyperelliptic. More precisely, the induction in Hartshorne's
proof constructs a nonzero proper common subdivisor `D'` of suitable
representatives of `|D|` and `|K-D|`, with

`2 * dim|D'| = deg D'`.

## Depends on

- [Clifford's inequality](clifford-inequality.md)
- [Dimensions are superadditive under addition of linear systems](linear-system-dimension-superadditive.md)
- [Hyperelliptic curves and degree-two linear systems](../canonical-embedding/hyperelliptic-linear-series-criterion.md)

## Proof depends on

- Construct the coefficientwise intersection `D'=D_0 intersect E` after
  choosing `E in |K-D|` and a representative `D_0 in |D|` through one point
  of `E` and one outside it.
- The exact sequence of rational-function section spaces for
  `D'`, `D_0`, `E`, and `D_0+E-D'` forces equality for `D'`; descend on degree
  to the base case `deg D'=2`.

## Sources

- [Hartshorne IV.5, equality induction in Theorem 5.4, pp.344–345](../../../../sources/hartshorne-iv-5.md)
- Saint-Donat, §1.

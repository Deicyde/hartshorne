---
declaration: theorem
origin: cited
source_units: [chapter-v-section-2]
---

# Vector bundles on curves are successive extensions of line bundles

Let `E` be a finite locally free sheaf of rank `r` on a nonsingular curve
`C`. There is a filtration by locally free subsheaves

`0=E_0 subset E_1 subset ... subset E_r=E`

such that every quotient `E_i/E_(i-1)` is invertible.

## Depends on

- [A nowhere-vanishing section of a high-rank generated bundle](../../prerequisites/globally-generated-bundle-nowhere-vanishing-section.md)
- [Serre global generation](../../../schemes/projective-sheaves/serre-global-generation.md)

## Proof depends on

- Twist by a sufficiently positive invertible sheaf, apply II Exercise 8.2
  to split off a locally free rank-one subsheaf with locally free quotient,
  and induct on the rank; tensoring back preserves the filtration.

## Sources

- [Hartshorne V.2, Exercise 2.3(a), pp.383–384](../../../../sources/hartshorne-v-2.md#exercise-disposition-printed-pp383386)

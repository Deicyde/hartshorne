---
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-1-3]
---

# The normalization is normal and integral

The normalization `X̃` of an integral scheme is a normal integral scheme.

Each affine chart is the spectrum of an integrally closed domain inside
`K(X)`, hence normal and integral. Descend these local properties through the
glued affine cover. Mathlib's relative-normalization API supplies reduced and
integral instances under source hypotheses, but normality and this absolute
specialization remain project wrappers.

## Depends on

- [Construction of the normalization](normalization-construction.md)
- [Normal schemes](normal-scheme.md)

## Proof depends on

- Locality of normality and integrality.

## Sources

- [Hartshorne II.3 (later-used-exercises)](../../../sources/hartshorne-ii-3.md#later-used-exercises)

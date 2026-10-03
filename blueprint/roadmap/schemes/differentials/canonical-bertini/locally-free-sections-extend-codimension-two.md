---
declaration: theorem
origin: bridged
source_units: [chapter-ii-section-8]
---

# Locally free sections extend across codimension two

Let `X` be a normal integral Noetherian scheme, let `U subset X` be an open
subscheme whose complement has codimension at least two, and let `E` be a
finite locally free sheaf on `X`. Restriction is an isomorphism

`Gamma(X, E) ~= Gamma(U, E|_U)`.

## Depends on

- [Normal schemes](../../normalization-and-exercises/normal-scheme.md)
- [Intersection of height-one localizations](../../divisors/weil-divisors/height-one-localization-intersection.md)
- [Locally free and invertible module sheaves](../../modules-and-quasicoherent/locally-free-and-invertible.md)

## Proof depends on

- Trivialize `E` on affine opens and apply the height-one intersection theorem
  componentwise.
- Uniqueness on overlaps follows from density.

## Sources

- [Hartshorne II.8, section-extension step in the proof of Theorem 8.19 (pp.181–182)](../../../../sources/hartshorne-ii-8.md#canonical-sheaves-and-adjunction)
- [Hartshorne II.8, the same method requested for Exercise 8.8 (p.190)](../../../../sources/hartshorne-ii-8.md#adopted-exercises-and-later-use-evidence)

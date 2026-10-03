---
declaration: theorem
origin: cited
source_units: [chapter-iv-section-4]
---

# Elliptic curves with prescribed j-invariant

Over an algebraically closed field of characteristic different from two,
every `j : k` is the `j`-invariant of an elliptic curve.

## Depends on

- [Abstract elliptic curves and Weierstrass scheme models](abstract-elliptic-weierstrass-bridge.md)
- [The j-invariant is intrinsic](elliptic-j-invariant-well-defined.md)

## Proof depends on

- Solve the degree-six Legendre equation for `lambda`; a solution cannot be
  `0` or `1`, and its Legendre cubic is nonsingular.
- `WeierstrassCurve.ofJ` and `ofJ_j` are stronger equation-level pinned prior
  art, including the excluded characteristic-two case.

## Sources

- [Hartshorne IV.4, Theorem 4.1(c), p.320](../../../../sources/hartshorne-iv-4.md)

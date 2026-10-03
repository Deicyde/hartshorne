---
declaration: theorem
origin: cited
source_units: [chapter-iv-section-4]
---

# The j-invariant classifies elliptic curves

Over an algebraically closed field of characteristic different from two, two
elliptic curves are isomorphic if and only if their `j`-invariants are equal.

## Depends on

- [The j-invariant is intrinsic](elliptic-j-invariant-well-defined.md)
- [Variable changes induce Weierstrass scheme isomorphisms](weierstrass-variable-change-scheme-iso.md)
- [Abstract elliptic curves and Weierstrass scheme models](abstract-elliptic-weierstrass-bridge.md)

## Proof depends on

- The map `lambda |-> j(lambda)` has degree six and its fibres are precisely
  the `S_3` orbits.
- Pinned Mathlib's `WeierstrassCurve.exists_variableChange_of_j_eq` supplies
  equation-level prior art after passing through the scheme bridge.

## Sources

- [Hartshorne IV.4, Theorem 4.1(b), p.320](../../../../sources/hartshorne-iv-4.md)

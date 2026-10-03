---
declaration: theorem
origin: bridged
source_units: [chapter-iii-section-10]
---

# Generic smoothness for finitely many regular components

Let `f : X -> Y` be a separated finite-type morphism over an algebraically
closed field of characteristic zero, where `X` is nonsingular with finitely many
irreducible components and `Y` is a variety. There is a nonempty open
`V subset Y` such that `f^-1(V) -> V` is smooth.

Each component of the regular Noetherian source is open, closed, and integral.
For a dominant component, shrink `Y` by generic smoothness; for a
nondominant component, remove the closure of its image. Intersecting the
finitely many resulting opens proves the assertion. This wrapper is needed
because the incidence scheme in Kleiman's proof need not be irreducible.

## Depends on

- [Generic smoothness over the target](generic-smoothness-over-target.md)
- [The dense nonsingular locus](../../schemes/differentials/scheme-differentials/dense-nonsingular-locus.md)

## Proof depends on

- The pinned Noetherian-topology API for finiteness of irreducible components
  and for regular components being pairwise disjoint, open, and closed.

## Sources

- [Hartshorne III.10, finite-component step in Theorem 10.8, pp.273–274](../../../sources/hartshorne-iii-10.md#homogeneous-spaces-kleiman-and-bertini-pp272275)

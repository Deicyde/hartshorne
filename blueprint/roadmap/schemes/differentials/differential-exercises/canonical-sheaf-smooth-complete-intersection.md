---
declaration: theorem
origin: cited
source_units: [chapter-ii-section-8]
---

# The canonical sheaf of a smooth complete intersection

Let `k` be algebraically closed, let `d_1, ..., d_r >= 1` with `r < n`, and
let `Y subset P^n_k` be a nonsingular complete intersection of hypersurfaces
of those degrees. Then

`omega_Y ~= O_Y(d_1 + ... + d_r - n - 1)`.

## Depends on

- [Global complete intersections and hypersurface intersections](global-complete-intersection-iff-hypersurface-intersection.md)
- [Determinant adjunction for a nonsingular closed subvariety](../canonical-bertini/adjunction-determinant-normal-bundle.md)
- [The canonical sheaf of projective space](../canonical-bertini/canonical-sheaf-projective-space.md)

## Proof depends on

- The conormal bundle of the complete intersection is
  `J/J^2 ~= ⊕_i O_Y(-d_i)`. Apply determinant adjunction directly to this
  bundle and the canonical sheaf of projective space; no nonsingularity of a
  chosen sequence of partial intersections is required.

## Sources

- [Hartshorne II.8, Exercise 8.4(e) (p.188)](../../../../sources/hartshorne-ii-8.md#adopted-exercises-and-later-use-evidence)

---
declaration: theorem
origin: cited
source_units: [chapter-iii-section-10]
---

# Homogeneous spaces are nonsingular

Every homogeneous variety over an algebraically closed field is nonsingular.
In particular, a group variety acting on itself by left translation is
nonsingular.

The proof transports a nonempty regular open by translation automorphisms.
Their union contains every closed point; its closed complement is empty by
the Jacobson property. This orbit-openness step does not assume transitivity
on nonclosed scheme points.

## Depends on

- [Algebraic group actions and homogeneous spaces](homogeneous-space-api.md)
- [The dense nonsingular locus](../../schemes/differentials/scheme-differentials/dense-nonsingular-locus.md)
- [Regular points and nonsingular schemes](../../schemes/differentials/scheme-differentials/regular-points-and-nonsingular-schemes.md)

## Proof depends on

- Invariance of local-ring regularity under scheme isomorphisms.
- Finite-type schemes over a field are Jacobson.
- `AlgebraicGeometry.smooth_of_grpObj` is alternative pinned prior art for the
  special case of the group acting on itself.

## Sources

- [Hartshorne III.10, Remark 10.7.1 and Examples 10.7.2–3, p.273](../../../sources/hartshorne-iii-10.md#homogeneous-spaces-kleiman-and-bertini-pp272275)

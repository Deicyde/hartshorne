---
article_id: af_9bd7ee98c8d444a53bbaf8ec
declaration: theorem
origin: bridged
source_units: [chapter-iii-section-10]
---

# The projective-linear hyperplane orbit map is open

Fix a hyperplane `H` in `P^n` over an algebraically closed field of
characteristic zero. The orbit
morphism

`PGL(n+1) -> (P^n)^dual`,  `sigma |-> sigma(H)`,

is surjective and smooth, hence open. Therefore the image of any invariantly
constructed nonempty open set of good translates contains a nonempty open set
of the hyperplane parameter space. This is the step that converts Kleiman's
open subset of the group into the usual "general hyperplane" assertion.

## Depends on

- [Projective space is homogeneous under the projective linear group](projective-space-homogeneous-under-pgl.md)
- [The homogeneous action family is smooth](homogeneous-action-family-smooth.md)

## Proof depends on

- Apply the action-family smoothness theorem to the homogeneous dual
  projective space and the nonsingular one-point source.
- Transitivity makes the orbit map surjective; smooth morphisms are open.

## Sources

- [Hartshorne III.10, Corollary 10.9, pp.274–275](../../../sources/hartshorne-iii-10.md#homogeneous-spaces-kleiman-and-bertini-pp272275)

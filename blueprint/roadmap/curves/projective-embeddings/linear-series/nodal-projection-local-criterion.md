---
declaration: theorem
origin: cited
source_units: [chapter-iv-section-3]
---

# The local criterion for a nodal plane projection

Let `X -> P^3` be an embedded Chapter IV curve, let `O` lie outside `X`, and
let `pi_O : X -> P^2` be projection from `O`. The map is birational onto its
image and the image has at most ordinary nodes as singularities if and only
if:

1. `O` lies on only finitely many secant lines;
2. `O` lies on no tangent line;
3. `O` lies on no multisecant;
4. `O` lies on no secant whose two tangent lines are coplanar.

No claim that such an `O` exists is made in this leaf.

## Depends on

- [Secant and tangent incidence for an embedded curve](secant-tangent-incidence-api.md)
- [Projection is an embedding away from secants and tangents](projection-closed-immersion-criterion.md)
- [Ordinary nodes and their two branches](../prerequisites/ordinary-node-local-criterion.md)
- [The birational criterion](../../../rational-maps/birational-criterion.md)

## Proof depends on

- Condition 1 makes the finite projection generically one-to-one and hence
  birational.
- Conditions 2–4 make every exceptional fibre consist of exactly two
  unramified branches with distinct image tangent directions, which is the
  local ordinary-node criterion.

## Sources

- [Hartshorne IV.3, Proposition 3.7, pp.310–311](../../../../sources/hartshorne-iv-3.md)

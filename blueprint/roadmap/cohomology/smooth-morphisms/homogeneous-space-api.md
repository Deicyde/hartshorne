---
article_id: af_1ef0710a237ef97d9883d6eb
declaration: structure
origin: bridged
source_units: [chapter-iii-section-10]
statement: formalized
proof: formalized
lean: Hartshorne.GroupVariety Hartshorne.AlgebraicGroupAction Hartshorne.HomogeneousSpace Hartshorne.AlgebraicGroupAction.translationIso Hartshorne.rationalPointEquivClosedPoint Hartshorne.HomogeneousSpace.transitive_closedPoints
---

# Algebraic group actions and homogeneous spaces

Over `S = Spec k`, package a group variety as an integral separated
finite-type group object `G` in `Over S`. Package an action on `X` by a
morphism `G times_S X -> X` satisfying the unit and associativity diagrams.
A homogeneous space is such an action for which `G(k)` acts transitively on
`X(k)`.

Construct translation automorphisms from `k`-point sections and prove their
compatibility with the action morphism. Over algebraically closed `k`, expose
the equivalence between `k`-points and closed points. The API uses genuine
scheme morphisms; an abstract `MulAction` is not sufficient.

## Depends on

- [Schemes over a base](../../schemes/spectrum-and-schemes/over-base.md)
- [Schemes have fibre products](../../schemes/fiber-products/schemes-have-fiber-products.md)
- [Closed points are dense](../../schemes/first-properties/closed-points-dense.md)

## Proof depends on

- Mathlib's `GrpObj (Over S)` and finite-product infrastructure.
- The scheme-point/closed-point comparison over an algebraically closed field.

## Sources

- [Hartshorne III.10, group actions and homogeneous spaces, pp.272–273](../../../sources/hartshorne-iii-10.md#homogeneous-spaces-kleiman-and-bertini-pp272275)

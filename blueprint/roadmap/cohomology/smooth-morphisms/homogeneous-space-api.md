---
article_id: af_1ef0710a237ef97d9883d6eb
declaration: structure
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.GroupVariety Hartshorne.AlgebraicGroupAction Hartshorne.HomogeneousSpace
---

# Algebraic group actions and homogeneous spaces

Over $S=\operatorname{Spec}k$, a group variety is an integral separated
group scheme $G$ of finite type over $S$. An action on $X$ is a morphism
$G\times_S X\to X$ satisfying the unit and associativity identities.
A homogeneous space is such an action for which $G(k)$ acts transitively
on $X(k)$.

Rational points of the group give translation automorphisms,
compatible with the scheme action. Over an algebraically closed
field $k$, $k$-rational points correspond to closed points.

## Depends on

- [Schemes over a base](../../schemes/spectrum-and-schemes/over-base.md)
- [Schemes have fibre products](../../schemes/fiber-products/schemes-have-fiber-products.md)
- [Closed points are dense](../../schemes/first-properties/closed-points-dense.md)

## Proof depends on

- Group objects and their actions in the category of schemes over the base.
- The scheme-point/closed-point comparison over an algebraically closed field.

## Sources

- [Hartshorne III.10, group actions and homogeneous spaces, pp.272–273](../../../sources/hartshorne-iii-10.md#homogeneous-spaces-kleiman-and-bertini-pp272275)

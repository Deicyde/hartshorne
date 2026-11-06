---
article_id: af_9a85f92e6194c64e719a9fdd
declaration: definition
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.projectiveIntersectionDivisor Hartshorne.IsProjectiveHypersurfaceLocalEquation Hartshorne.exists_projectiveHypersurfaceLocalEquation Hartshorne.projectiveIntersectionDivisor_apply_eq_ord Hartshorne.projectiveIntersectionDivisor_apply_eq_zero_of_notMem Hartshorne.ambientDivisorsNotContaining Hartshorne.projectiveIntersectionDivisorHom Hartshorne.projectiveIntersectionDivisorHom_of_primeDivisor Hartshorne.projectiveHypersurfacePrimeDivisor Hartshorne.exists_projectivePrimeDivisor_equation
---

# Ambient hypersurfaces cut divisors

Let $k$ be algebraically closed, let $X \subseteq \mathbb{P}^n_k$ be a closed variety
nonsingular in codimension one, and let $V \subseteq \mathbb{P}^n_k$ be an irreducible
hypersurface not containing $X$. For every codimension-one component $Y_i$ of
$V \cap X$, use a local equation of $V$ to define its multiplicity
$\operatorname{ord} _{Y_i}(f|_X)$, and define the Weil divisor $V\cdot X$ as their weighted sum.

Prove independence of all local equations and extend linearly to ambient
divisors none of whose components contain $X$. This is precisely Exercise
6.2(a); descent to class groups from part (b) is not part of this node.

## Depends on

- [The Weil divisor group](../weil-divisors/weil-divisor-group.md)
- [Principal divisors have finite support](../weil-divisors/principal-divisor-finite-support.md)
- [Projective varieties](../../../projective-varieties/projective-variety.md)
- [Proper hypersurface sections are equidimensional](../../../intersections-projective-space/bezout/hypersurface-section-components-equidimensional.md)

## Proof depends on

- Two local equations for a hypersurface differ by a regular unit.

## Sources

- [Hartshorne II.6, Exercise 6.2(a) on printed p.146](../../../../sources/hartshorne-ii-6.md#adopted-exercises-and-later-use-evidence)

---
article_id: af_84a1fe08857c7719e03e20fc
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.relativeSegre_eq_quadricSurfaceι Hartshorne.quadricSurfaceIsoSegreSource Hartshorne.quadricSurfaceι Hartshorne.ker_quadricCoordinateAlgHom Hartshorne.map_quadricCoordinateAlgHom_homogeneousSubmodule Hartshorne.quadricQuotientEquiv Hartshorne.projectiveSpaceOverSpecIso Hartshorne.projQuadricQuotientIso_hom_comp_quadricSurfaceι Hartshorne.projQuadricQuotientIso Hartshorne.ker_quadricSurfaceι
---

# The split quadric surface is $\mathbb{P}^1 \times \mathbb{P}^1$

Let $k$ be a field and let $x,y,z,w$ be the homogeneous coordinates of
$\mathbb{P}^3_k$. The Segre morphism

$\psi : \mathbb{P}^1_k \times_k \mathbb{P}^1_k \longrightarrow \mathbb{P}^3_k$, $([s_0 : s_1],[u_0 : u_1]) \mapsto [s_0u_0 : s_1u_1 : s_0u_1 : s_1u_0]$,

that is, the relative Segre embedding with $r = s = 1$ over $\operatorname{Spec} k$
with its coordinates ordered as $x = z_{00}$, $y = z_{11}$, $z = z_{01}$,
$w = z_{10}$, is a closed immersion whose image is the quadric
$Q = V(xy - zw) = \operatorname{Proj} k[x,y,z,w]/(xy - zw)$: $\psi$ is an
isomorphism $\mathbb{P}^1_k \times_k \mathbb{P}^1_k \cong Q$ followed by the closed
immersion of $Q$ in $\mathbb{P}^3_k$. The homogeneous coordinate ring of $Q$ is the
Segre ring: $x,y,z,w \mapsto s_0u_0, s_1u_1, s_0u_1, s_1u_0$ induces an
isomorphism of graded $k$-algebras from $k[x,y,z,w]/(xy - zw)$ onto the span in
$k[s_0,s_1,u_0,u_1]$ of the monomials of bidegree $(d,d)$, $d \ge 0$, graded by
$d$.

The identification of $Q$ with $\mathbb{P}^1_k \times_k \mathbb{P}^1_k$ is the unique main
result; the coordinate-ring isomorphism is its algebraic interface, and it lets
$Q$ be modelled as $\operatorname{Proj}$ of the Segre ring.

Example II.6.6.1 works with $Q$ through this identification. Hartshorne cites
Exercise I.2.15 for this identification; that exercise is not in the project's
source table and works over an algebraically closed field. The scheme statement
over an arbitrary field recorded here is a project bridge.

## Proof

*The coordinate ring.* Every monomial of bidegree $(d,d)$ is a product of $d$
monomials $s_iu_j$, so the map is surjective in every degree, and it kills
$xy - zw$. Since $xy - zw$ is a nonzero form of degree two in a domain, the
degree-$d$ part of $k[x,y,z,w]/(xy - zw)$ has dimension
$\binom{d+3}{3} - \binom{d+1}{3} = (d+1)^2$, which is the number of monomials of
bidegree $(d,d)$. A surjection of finite-dimensional spaces of equal dimension
is injective.

*The closed immersion.* The graded surjection $k[x,y,z,w] \to k[x,y,z,w]/(xy - zw)$
gives the closed immersion $Q \to \mathbb{P}^3_k$. Compare it with $\psi$ on the four
standard charts. On $D_+(x)$, the relative Segre chart is cut out by the
$2 \times 2$ minors of $(z_{ij})$ with $z_{00} = 1$, which reduce to the single
equation $z_{11} = z_{01}z_{10}$, that is, $y/x = (z/x)(w/x)$: the chart of $Q$.
The charts $D_+(y)$, $D_+(z)$, $D_+(w)$ are symmetric. The two closed subschemes of
$\mathbb{P}^3_k$ therefore agree chart by chart, and $\psi$ factors through an
isomorphism onto $Q$. Equivalently, on the chart $D_+(s_iu_j)$ of $\operatorname{Proj}$ of the
Segre ring the degree-zero ring is the polynomial ring in the two ratios
$s_{i'}/s_i$ and $u_{j'}/u_j$, which is the coordinate ring of the chart
$D_+(s_i) \times D_+(u_j)$ of $\mathbb{P}^1_k \times_k \mathbb{P}^1_k$.

## Depends on

- [The relative Segre embedding](../../proper-and-projective/relative-segre-closed-immersion.md)
- [Projective space over a ring](../../projective-spectrum/projective-space-over-ring.md)
- [A graded quotient induces a closed immersion of Proj](../../normalization-and-exercises/proj-surjection-closed-immersion.md)

## Proof depends on

- [A standard Proj chart is affine](../../projective-spectrum/proj-basic-open.md)
- The degree-$d$ parts of $k[x,y,z,w]/(xy - zw)$ and of the Segre ring both
  have dimension $(d+1)^2$.
- Projective space over $\operatorname{Spec} k$, formed by base change from
  $\mathbb{P}^n_{\mathbb{Z}}$, is $\operatorname{Proj} k[x_0,\ldots,x_n]$.

## Informally uses

- [The Segre embedding](../../../rational-maps/segre-embedding.md)

## Sources

- [Hartshorne II.6, setup of Example 6.6.1 on printed p.135](../../../../sources/hartshorne-ii-6.md#weil-divisors-and-class-groups)

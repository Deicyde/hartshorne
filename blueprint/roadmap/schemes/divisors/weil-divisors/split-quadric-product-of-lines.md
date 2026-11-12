---
article_id: af_84a1fe08857c7719e03e20fc
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.relativeSegre_eq_quadricSurfaceι Hartshorne.quadricSurfaceIsoSegreSource Hartshorne.quadricSurfaceι Hartshorne.ker_quadricCoordinateAlgHom Hartshorne.map_quadricCoordinateAlgHom_homogeneousSubmodule Hartshorne.quadricQuotientEquiv Hartshorne.projQuadricQuotientIso_hom_comp_quadricSurfaceι Hartshorne.projQuadricQuotientIso Hartshorne.ker_quadricSurfaceι Hartshorne.quadricSurfaceι_isClosedImmersion Hartshorne.QuadricRing Hartshorne.quadricGrading Hartshorne.quadricSurface Hartshorne.quadricIdeal Hartshorne.quadricQuotientHom
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

The coordinate-ring isomorphism lets $Q$ be modelled as $\operatorname{Proj}$ of
the Segre ring.

Example II.6.6.1 works with $Q$ through this identification. Hartshorne cites
Exercise I.2.15 for this identification; that exercise is not in the project's
source table and works over an algebraically closed field. The scheme statement
over an arbitrary field recorded here is a project bridge.

## Proof

*The coordinate ring.* Write $\varphi$ for the map
$k[x,y,z,w] \to k[s_0,s_1,u_0,u_1]$, $x,y,z,w \mapsto s_0u_0, s_1u_1, s_0u_1, s_1u_0$.
Every monomial of bidegree $(d,d)$ is a product of $d$ monomials $s_iu_j$, so
$\varphi$ maps the degree-$d$ part of $k[x,y,z,w]$ onto the degree-$d$ part of the
Segre ring, and it kills $xy - zw$. The kernel is computed with a normal form.
Modulo $xy - zw$, every monomial $x^ay^bz^cw^e$ is congruent to one not divisible
by $xy$: replace $(xy)^{\min(a,b)}$ by $(zw)^{\min(a,b)}$. A monomial not divisible
by $xy$ is determined by its image under $\varphi$, and every monomial
$s^{e}u^{g}$ of bidegree $(d,d)$ is such an image. Sending each monomial
$s^{e}u^{g}$ of the Segre ring to the normal-form monomial with that image gives
an additive map $\sigma$ from the Segre ring to $k[x,y,z,w]$ with
$\sigma(\varphi(P)) \equiv P \pmod{xy - zw}$ for every polynomial $P$. Hence
$\varphi(P) = 0$ forces $P \in (xy - zw)$, so the kernel of $\varphi$ is
$(xy - zw)$ and $\varphi$ induces the graded isomorphism of the statement.

*The closed immersion.* The graded surjection from $k[x,y,z,w]$ onto the Segre
ring gives a closed immersion of $\operatorname{Proj}$ of the Segre ring into
$\mathbb{P}^3_k$; by the coordinate-ring isomorphism its ideal is $(xy - zw)$, so
its image is $Q$. To compare it with $\psi$, build morphisms in both directions
chart by chart and glue. On the chart $D_+(s_iu_j)$ of $Q$, map to the chart
$D_+(z_{ij})$ of $\mathbb{P}^3_k$ and then to $\mathbb{P}^1_k \times_k \mathbb{P}^1_k$
by the ratios $z_{kj}/z_{ij}$ and $z_{il}/z_{ij}$; this is compatible with $\psi$
because $(z_{kj}/z_{ij})(z_{il}/z_{ij}) = z_{kl}/z_{ij}$ on $Q$. Conversely, on the
chart $D_+(s_i) \times D_+(u_j)$ of $\mathbb{P}^1_k \times_k \mathbb{P}^1_k$, map to
$D_+(s_iu_j)$ by sending a monomial $s^{e}u^{g}$ of bidegree $(d,d)$ to
$\prod_a (s_a/s_i)^{e_a} \prod_b (u_b/u_j)^{g_b}$. The first morphism followed by
$\psi$ is the closed immersion of $Q$, and the second followed by the closed
immersion of $Q$ is $\psi$. Since both maps to $\mathbb{P}^3_k$ are closed
immersions, hence monomorphisms, the two morphisms are inverse isomorphisms, and
$\psi$ is the isomorphism $\mathbb{P}^1_k \times_k \mathbb{P}^1_k \cong Q$ followed by
the closed immersion of $Q$.

## Depends on

- [The relative Segre embedding](../../proper-and-projective/relative-segre-closed-immersion.md)
- [Projective space over a ring](../../projective-spectrum/projective-space-over-ring.md)
- [A graded quotient induces a closed immersion of Proj](../../normalization-and-exercises/proj-surjection-closed-immersion.md)
- [Homogeneous ideals and truncation define the same Proj subscheme](../../normalization-and-exercises/proj-closed-subscheme-truncation.md)

## Proof depends on

- [A standard Proj chart is affine](../../projective-spectrum/proj-basic-open.md)
- [Degree-one-generated Proj is projective](../../proper-and-projective/generated-proj-projective.md)
- Modulo $xy - zw$, every monomial in $x,y,z,w$ is congruent to one not
  divisible by $xy$.
- Projective space over $\operatorname{Spec} k$, formed by base change from
  $\mathbb{P}^n_{\mathbb{Z}}$, is $\operatorname{Proj} k[x_0,\ldots,x_n]$.

## Informally uses

- [The Segre embedding](../../../rational-maps/segre-embedding.md)

## Sources

- [Hartshorne II.6, setup of Example 6.6.1 on printed p.135](../../../../sources/hartshorne-ii-6.md#weil-divisors-and-class-groups)

---
article_id: af_71347b8169aa158ac22ab154
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.ProjTwistMap.twistRestrictIso Hartshorne.ProjTwistMap.isIso_twistRestrictHom Hartshorne.ProjTwistMap.twistRestrictIso_comp Hartshorne.ProjTwistMap.twistRestrictIso_id Hartshorne.ProjTwistMap.exists_isLocalizationAway_comp Hartshorne.isOpenImmersion_projMap Hartshorne.range_projMap Hartshorne.irrelevant_eq_map_of_isLocalizationAway Hartshorne.ProjTwistMap.twistRestrictHom_app_apply Hartshorne.ProjTwistMap.twistFiber_mk
---

# Twisting sheaves under localization in degree zero

Let $A$ be a graded ring, let $s \in A_0$ be homogeneous of degree zero, and let
$B = A[1/s]$ with the grading $B_d = \{a/s^k \mid a \in A_d,\ k \ge 0\}$. The localization map
$A \to B$ preserves degrees and $B_+ = A_+ B$, so it induces a morphism
$j : \operatorname{Proj} B \to \operatorname{Proj} A$, $\mathfrak{q} \mapsto$ the inverse image
of $\mathfrak{q}$ in $A$. This morphism is an open immersion onto the open set of homogeneous
primes not containing $s$. For every $n \in \mathbb{Z}$ there is an isomorphism of
$\mathcal{O}_{\operatorname{Proj} B}$-modules

$\mathcal{O}_{\operatorname{Proj} A}(n)|_{\operatorname{Proj} B} \cong \mathcal{O}_{\operatorname{Proj} B}(n)$,

where the left side is the restriction along $j$. At a point $\mathfrak{q}$ with image
$\mathfrak{p}$ it sends a germ $m/t$ to $m/t$, where $m \in A$ is homogeneous, $t \notin \mathfrak{p}$
is homogeneous, and $\deg m = n + \deg t$.

These isomorphisms are compatible with composites. If $t \in B_0$ and $C = B[1/t]$, then $C$
is again the localization of $A$ at an element of degree zero. The isomorphism for $A \to C$ is
the restriction to $\operatorname{Proj} C$ of the isomorphism for $A \to B$, followed by the
isomorphism for $B \to C$. Here restriction along the composite open immersion is identified
with restriction in two steps. For $s = 1$ and $B = A$, so that $j$ is the identity, the isomorphism is the identity.

That $j$ is an open immersion onto that open set is part of the construction of relative
Proj, which glues affine Proj schemes along such localizations. No generation hypothesis on $A$
is needed. The map $m/t \mapsto m/t$ is defined for any
degree-preserving map of graded rings and is linear over the corresponding map of local rings.
For a localization at an element of degree zero it is bijective on every stalk. The fiber maps
are functorial, which gives the compatibility with composites. When $A$ and $B$ are generated in
degree one, it is an instance of
[Pullback of twisting sheaves](../../projective-sheaves/proj-twist-pullback.md) for the open
immersion $j$. Gluing the twisting sheaves of the affine pieces of a relative Proj uses exactly
this compatibility with composites.

## Depends on

- [Twisting sheaves are invertible](../../projective-sheaves/proj-twisting-sheaf.md)
- [The partial Proj morphism of a graded map](../../projective-spectrum/proj-partial-map.md)

## Proof depends on

- [Relative Proj](relative-proj.md)

## Sources

- [Hartshorne II.7, relative Proj construction (p. 160), which cites Proposition 5.12(c) for the compatibility of the sheaves O(1); dropping the generation hypothesis and the compatibility with composites are project additions](../../../../sources/hartshorne-ii-7.md#relative-proj-and-projective-bundles)
- [Hartshorne II.5, Proposition 5.12(c), p.117](../../../../sources/hartshorne-ii-5.md#graded-modules-twists-and-reconstruction-on-proj)
- [Stacks Project, relative Proj, tag 01NM](../../../../sources/hartshorne-ii-7.md#adopted-auxiliary-proof-sources)

---
article_id: af_fab4230d466fcd773bbece40
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: AlgebraicGeometry.Scheme.etaleRootsOfUnitySheaf AlgebraicGeometry.Scheme.etaleRootsOfUnitySheaf_obj_obj AlgebraicGeometry.Scheme.rootsOfUnityPresheafRepresentableIso AlgebraicGeometry.Scheme.isSheaf_fpqcTopology_rootsOfUnityPresheaf AlgebraicGeometry.Scheme.isSheaf_etaleTopology_rootsOfUnityPresheaf AlgebraicGeometry.Scheme.etaleRootsOfUnitySheafIncl AlgebraicGeometry.Scheme.etaleRootsOfUnitySheafIncl_app AlgebraicGeometry.Scheme.etaleRootsOfUnitySheafPow AlgebraicGeometry.Scheme.etaleRootsOfUnitySheafPow_app
---

# The sheaf of roots of unity on the small étale site

Let $X$ be a scheme and $n\ge 1$ an integer.  For a scheme $U$ étale over $X$, put

$\mu_n(U)=\{\zeta\in\Gamma(U,\mathcal O_U) : \zeta^n=1\}$,

the group, under multiplication, of $n$-th roots of unity in $\Gamma(U,\mathcal O_U)$.  Each
such $\zeta$ is a unit.  A morphism $V\to U$ of étale $X$-schemes acts by pulling back
functions.  Then $\mu_n$ is a sheaf of abelian groups on the small étale site of $X$.

Indeed, the functor $U\mapsto\mu_n(\Gamma(U,\mathcal O_U))$ on all schemes is represented by
$\operatorname{Spec}\mathbb Z[t]/(t^n-1)$, the spectrum of the group ring $\mathbb Z[\mathbb Z/n]$: a morphism
$U\to\operatorname{Spec}\mathbb Z[t]/(t^n-1)$ is the same as the root of unity in
$\Gamma(U,\mathcal O_U)$ to which it pulls back $t$.  It is therefore a sheaf for the fpqc
topology, hence for the étale topology, and $\mu_n$ is its restriction to schemes étale over
$X$.

For $m\mid n$, the inclusion $\mu_m\subseteq\mu_n$ and the power map
$\mu_n\to\mu_m$, $\zeta\mapsto\zeta^{n/m}$, are morphisms of sheaves.

## Depends on

- [The small étale site](small-etale-site.md)

## Proof depends on

- Representable functors on schemes are sheaves for the fpqc topology (the fpqc topology is
  subcanonical).
- Every étale covering family is an fpqc covering family.
- The forgetful functor from the small étale site of $X$ to all schemes is continuous for the
  étale topology, so it restricts étale sheaves on schemes to sheaves on the small étale site.

## Sources

- [Hartshorne Appendix C §3, suppressed twist in properties 3.4 and 3.8, pp.453–454](../../../../sources/hartshorne-appendix-c-3.md#properties-31-through-35-printed-p453)
- Milne, *Étale Cohomology*, Chapter II (examples of étale sheaves); SGA 4½ (Tate twists).

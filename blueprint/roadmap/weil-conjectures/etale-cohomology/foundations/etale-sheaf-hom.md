---
article_id: af_beb483418f9bd16369fdfdc9
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: AlgebraicGeometry.Scheme.etaleSheafHom AlgebraicGeometry.Scheme.etaleSheafHom_obj_obj AlgebraicGeometry.Scheme.etaleSheafHom_map_apply AlgebraicGeometry.Scheme.isSheaf_etaleHomPresheaf AlgebraicGeometry.Scheme.small_etaleHomOver AlgebraicGeometry.Scheme.EtaleHomOver AlgebraicGeometry.Scheme.etaleHomOverRestrict
---

# The internal Hom of abelian étale sheaves

Let $X$ be a scheme and let $F$ and $G$ be abelian sheaves on its small étale site.  For a
scheme $U$ étale over $X$, the étale $X$-schemes over $U$ form the small étale site of $U$;
write $F|_U$ and $G|_U$ for the restrictions of $F$ and $G$ to it.  Put

$\mathcal{H}om(F,G)(U)=\operatorname{Hom}(F|_U,G|_U)$,

the group of morphisms of abelian sheaves under pointwise addition.  A morphism $V\to U$ of
étale $X$-schemes acts by restricting a morphism along it.  This presheaf of abelian groups is
a sheaf on the small étale site of $X$, the internal Hom sheaf $\mathcal{H}om(F,G)$.

Each $\operatorname{Hom}(F|_U,G|_U)$ is a set, although the small étale site of $U$ is not
small: a morphism $F|_U\to G|_U$ is determined by its components at affine schemes étale over
$U$, and these form an essentially small category.

## Depends on

- [The small étale site](small-etale-site.md)

## Proof depends on

- Morphisms of sheaves glue along covering families: the presheaf of local morphisms between
  two sheaves on a site, with $G$ a sheaf, is a sheaf of sets.
- Every scheme étale over $U$ is covered by affine schemes étale over $U$, and a morphism into a
  sheaf is determined by its restrictions to a covering family.

## Informally uses

- [The sheaf of local morphisms](../../../schemes/sheaf-functors/sheaf-hom.md), the same
  construction for abelian sheaves on a topological space.

## Sources

- [Hartshorne Appendix C §3, suppressed twist in properties 3.4 and 3.8, pp.453–454](../../../../sources/hartshorne-appendix-c-3.md#properties-31-through-35-printed-p453)
- SGA 4, Exposé IV (operations on sheaves); Milne, *Étale Cohomology*, Chapter II.

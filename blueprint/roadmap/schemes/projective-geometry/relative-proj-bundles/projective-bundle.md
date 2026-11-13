---
article_id: af_c05e78621794d3fff81b5c5a
declaration: def
origin: cited
lean: AlgebraicGeometry.Scheme.Modules.symmetricRelativeProjData AlgebraicGeometry.Scheme.Modules.projectiveBundle AlgebraicGeometry.Scheme.Modules.projectiveBundleProj AlgebraicGeometry.Scheme.Modules.projectiveBundleTwistingSheaf AlgebraicGeometry.Scheme.Modules.nonempty_projectiveBundle_iso_twist_of_restrict_iso_free
statement: formalized
proof: formalized
---

# Projective bundles

Let $X$ be Noetherian and $E$ finite locally free. Define
$P(E) = \operatorname{Proj} _X \operatorname{Sym} (E)$ using the quotient convention. If $E$ is free of rank
$n + 1$ on $U$, identify $P(E)|_U$ with $\mathbb{P}^n_U$, compatibly with the projection
and $\mathcal{O}(1)$. Hartshorne's note on p.162 gives only the isomorphism with
$\mathbb{P}^n_U$; the compatibility with $\mathcal{O}(1)$ is added here, the nearest
printed statement being Example 7.8.7 (p.161).

## Depends on

- [Relative Proj](relative-proj.md)
- [The relative twisting sheaf](relative-proj-twisting-sheaf.md)
- [The graded symmetric-algebra sheaf](graded-symmetric-algebra-sheaf.md)
- [Projective space over a scheme](../../proper-and-projective/projective-space-over-scheme.md)
- [Relative twisting sheaves and very ampleness](../../projective-sheaves/relative-twisting-and-very-ample.md)

## Proof depends on

- [Morphisms from generated invertible sheaves](../linear-systems-ampleness/morphism-from-generated-line-bundle.md)
- [Generation by global sections](../../projective-sheaves/globally-generated-module-sheaf.md)

## Sources

- [Hartshorne II.7, projective-bundle definition (p.162) and Exercise 7.10(b) (p.170)](../../../../sources/hartshorne-ii-7.md#relative-proj-and-projective-bundles)
- [Stacks Project, projective bundles, tag 01OA](../../../../sources/hartshorne-ii-7.md#adopted-auxiliary-proof-sources)

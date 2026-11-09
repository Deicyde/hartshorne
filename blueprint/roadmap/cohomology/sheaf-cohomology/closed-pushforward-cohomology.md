---
article_id: af_7c9c3c7ed2d4d570c9c104cc
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.closedPushforwardCohomologyIso Hartshorne.closedPushforwardCohomologyIso_naturality Hartshorne.closedPushforwardCohomologyIso_zero Hartshorne.closedPushforward_map_exact Hartshorne.isZero_abelianHigherDirectImage_closedSubspaceInclusion
---

# Closed pushforward preserves cohomology

For a closed inclusion $i : Y \hookrightarrow X$ and an abelian sheaf $F$ on $Y$, there
are natural isomorphisms

$H^{n}(Y,F) \cong H^{n}(X,i_*F)$

for every $n$. The comparison is induced by equality of global sections and is
computed using pushforward of a flasque resolution.

## Depends on

- [Closed extension by zero](../../schemes/sheaf-functors/closed-extension-by-zero.md)
- [Direct image of a sheaf](../../schemes/sheaf-functors/direct-image.md)
- [Sheaf cohomology](sheaf-cohomology.md)

## Proof depends on

- [Flasque closure in short exact sequences](flasque-short-exact-closure.md)
- [Flasque sheaves are acyclic](flasque-sheaf-acyclic.md)
- [Acyclic resolutions compute derived functors](../derived-functors/acyclic-resolution-comparison.md)

## Sources

- [Hartshorne III.2, Lemma 2.10, printed pp. 209–210](../../../sources/hartshorne-iii-1-2.md#filtered-colimits-and-closed-support-printed-pp-208210)

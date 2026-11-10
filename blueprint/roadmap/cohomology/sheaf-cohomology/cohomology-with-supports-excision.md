---
article_id: af_44adccb6cea98fcc33a4f6ee
declaration: isomorphism
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.cohomologyWithSupportsExcisionIso Hartshorne.cohomologyWithSupportsExcisionIso_hom Hartshorne.supportedSectionsRestrict Hartshorne.supportedSectionsRestrict_isIso
---

# Excision for cohomology with supports

Let $Y \subseteq X$ be closed and let $V \subseteq X$ be an open neighbourhood of $Y$.
Restriction induces natural isomorphisms

$H_Y^{n}(X,F) \cong H_Y^{n}(V,F|_V)$

for every abelian sheaf $F$ and every $n$.

## Depends on

- [The localization sequence for cohomology with supports](cohomology-with-supports.md)
- [Restriction preserves stalks](../../schemes/sheaf-functors/restriction-stalk.md)

## Proof depends on

- [Acyclic resolutions compute derived functors](../derived-functors/acyclic-resolution-comparison.md)

## Sources

- [Hartshorne III.2, Exercise 2.3(f), printed p. 212](../../../sources/hartshorne-iii-1-2.md#adopted-exercises-printed-pp-212213)

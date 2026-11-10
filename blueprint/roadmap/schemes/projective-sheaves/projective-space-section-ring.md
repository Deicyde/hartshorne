---
article_id: af_5dbe2fc522ca43b05f3a1f6b
declaration: isomorphism
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.ProjectiveSpaceSectionRing.sectionRingMap Hartshorne.ProjectiveSpaceSectionRing.sectionRingMap_of_mem Hartshorne.ProjectiveSpaceSectionRing.sectionRingMap_bijective Hartshorne.ProjectiveSpaceSectionRing.sectionRingEquiv Hartshorne.ProjectiveSpaceSectionRing.mulTwistGlobal Hartshorne.ProjectiveSpaceSectionRing.sectionRingMap_mul Hartshorne.ProjectiveSpaceSectionRing.twistValue_mulTwistGlobal
---

# The section ring of projective space

Let $S = A[x_{0},\ldots ,x_{r}]$ with $r \ge 1$ and $X = \operatorname{Proj} S$. The natural graded
ring homomorphism

$S \to \Gamma _*(\mathcal{O}_X)$

is an isomorphism.

## Depends on

- [The graded global-sections module](graded-global-sections-module.md)

## Proof depends on

- [The standard opens cover Proj](../projective-spectrum/proj-basic-open-cover.md)
- Injectivity of the coordinate localizations and computation of their
  intersection inside $S[x_{0}^{-1}\ldots x_{r}^{-1}]$.

## Sources

- [Hartshorne II.5, Proposition 5.13 (p.118)](../../../sources/hartshorne-ii-5.md#graded-modules-twists-and-reconstruction-on-proj)

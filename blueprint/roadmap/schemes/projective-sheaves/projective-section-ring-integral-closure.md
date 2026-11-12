---
article_id: af_126b2677e599617eaf60af08
declaration: theorem
origin: cited
lean: Hartshorne.ProjectiveSectionRing.projectiveSectionRing_isIntegralClosure Hartshorne.ProjectiveSectionRing.sectionRing_isIntegralClosure Hartshorne.ProjectiveSectionRing.sectionRingToFraction Hartshorne.ProjectiveSectionRing.sectionToFraction Hartshorne.ProjectiveSectionRing.sectionMul Hartshorne.ProjectiveSectionRing.sectionToFraction_sectionMul Hartshorne.ProjectiveSectionRing.unitSection Hartshorne.ProjectiveSectionRing.sectionToFraction_mulGlobal_unitSection Hartshorne.ProjectiveSectionRing.isDomain_of_isIntegral Hartshorne.ProjectiveSectionRing.isIntegral_of_connectedSpace
---

# The projective section ring is the integral closure

Let $k$ be algebraically closed and let $X \subseteq \mathbb{P}^r_{k}$ be connected and normal.
Its homogeneous coordinate ring $S$ is a domain, and the nonnegative section
ring

$S'=\bigoplus_{n\ge0}\Gamma(X,\mathcal{O}_X(n))$

is the integral closure of $S$ in its fraction field.

This is Exercise 5.14(a). The proof uses the integrality of $X$ and the fact
that the sheaf of graded section rings has integrally closed stalks.

The proof does not use that $k$ is algebraically closed; the hypothesis is kept because it is
Hartshorne's setting.

## Depends on

- [The graded global-sections module](graded-global-sections-module.md)
- [Normal schemes](../normalization-and-exercises/normal-scheme.md)
- [The section ring of projective space](projective-space-section-ring.md)

## Proof depends on

- [Homogeneous ideals and truncation define the same Proj subscheme](../normalization-and-exercises/proj-closed-subscheme-truncation.md)
- [A graded quotient induces a closed immersion of Proj](../normalization-and-exercises/proj-surjection-closed-immersion.md)
- [Regular points and nonsingular schemes](../differentials/scheme-differentials/regular-points-and-nonsingular-schemes.md)
- [The projective-space case of Bertini](../differentials/canonical-bertini/bertini-projective-space-case.md)

## Sources

- [Hartshorne II.5, Exercise 5.14(a) (p.126)](../../../sources/hartshorne-ii-5.md#adopted-exercises-and-later-use-evidence)

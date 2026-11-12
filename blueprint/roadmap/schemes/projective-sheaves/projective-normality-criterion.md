---
article_id: af_d0eb9f3cd8aa2aeb54f741fb
declaration: theorem
origin: cited
lean: Hartshorne.ProjectiveNormality.isProjectivelyNormal_iff Hartshorne.ProjectiveNormality.IsProjectivelyNormal Hartshorne.ProjectiveNormality.restrictTwist Hartshorne.ProjectiveNormality.isDomain_and_isIntegrallyClosed_iff
---

# The projective-normality criterion

Let $k$ be algebraically closed. A connected closed subscheme $X \subseteq \mathbb{P}^r_{k}$ is
projectively normal if and only if $X$ is normal and, for every $n \ge 0$, the
restriction map

$\Gamma (\mathbb{P}^r_{k},\mathcal{O}(n)) \to \Gamma (X,\mathcal{O}_X(n))$

is surjective.

Here the homogeneous coordinate ring of $X$ is $S(X)=k[x_{0},\ldots ,x_{r}]/I$ with
$I=\Gamma _*(\mathcal{I}_X)$, and $X$ is projectively normal if $S(X)$ is an integrally closed
domain.

## Depends on

- [Normal schemes](../normalization-and-exercises/normal-scheme.md)
- [Homogeneous ideals define projective closed subschemes](projective-closed-subscheme-homogeneous-ideal.md)
- [Twisting sheaves under localization in degree zero](../projective-geometry/relative-proj-bundles/proj-twist-localization.md)

## Proof depends on

- [The projective section ring is the integral closure](projective-section-ring-integral-closure.md)
- [The section ring of projective space](projective-space-section-ring.md)
- [Saturation of projective ideals](projective-ideal-saturation.md)

## Sources

- [Hartshorne II.5, Exercise 5.14(d) (p.126)](../../../sources/hartshorne-ii-5.md#adopted-exercises-and-later-use-evidence)

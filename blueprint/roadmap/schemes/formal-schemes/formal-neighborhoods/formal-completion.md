---
article_id: af_2d321ba1dda8b1030bb0580d
declaration: def
origin: cited
lean: Hartshorne.QuasicoherentIdealSubsheaf.formalCompletion Hartshorne.QuasicoherentIdealSubsheaf.formalCompletionSheaf Hartshorne.QuasicoherentIdealSubsheaf.formalCompletionDiagram Hartshorne.QuasicoherentIdealSubsheaf.isLocalRing_stalk_formalCompletionSheaf Hartshorne.QuasicoherentIdealSubsheaf.isUnit_formalCompletionSheaf_iff
---

# Formal completion as a locally ringed space

For $X$, $Y$, and $I$ as in the infinitesimal-neighbourhood construction,
define the formal completion $\widehat{X}_Y$ to have topological space $|Y|$ and
structure sheaf

$\mathcal{O}_{\widehat{X}_Y} = \varprojlim_{n \ge 1} (\mathcal{O}_X / I^{n})|_{|Y|}$.

Equip every stalk with its induced local-ring structure, making $\widehat{X}_Y$ a
locally ringed space. This is Hartshorne's plain ring-valued construction: no
topology is added to section rings.
The construction does not use that $X$ is Noetherian; the hypothesis is kept because it is Hartshorne's setting for formal completions.

## Depends on

- [Infinitesimal neighbourhoods](infinitesimal-neighborhoods.md)
- [Locally ringed spaces](../../spectrum-and-schemes/locally-ringed-space.md)
- [Limits of sheaves are computed pointwise](../../sheaves/limits-of-sheaves.md)

## Proof depends on

- A compatible inverse limit of local quotient rings is local.
- The correspondence between module ideal sheaves and compatible affine ideals, before taking powers and quotients.

## Sources

- [Hartshorne II.9, formal-completion definition (p.194)](../../../../sources/hartshorne-ii-9.md#formal-completions-and-formal-schemes)

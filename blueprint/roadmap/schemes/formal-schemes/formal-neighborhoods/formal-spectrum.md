---
article_id: af_161869b17d76a0768818f127
declaration: def
origin: bridged
lean: Hartshorne.Spf Hartshorne.IsAffineNoetherianFormalScheme Hartshorne.specIdealSubsheaf Hartshorne.range_specIdealSubsheaf_infinitesimalNeighborhoodι Hartshorne.spfHomeomorph
statement: formalized
proof: formalized
---

# Affine formal schemes

For a Noetherian ring $A$ and an ideal $I$, write $\operatorname{Spf}_I(A)$ for the completion of
$\operatorname{Spec} A$ along $V(I)$. An affine Noetherian formal scheme is one isomorphic to some
$\operatorname{Spf}_I(A)$; this is Hartshorne's definition (p.195): "a formal scheme obtained by
completing a single affine noetherian scheme along a closed subscheme".

The construction does not use that $A$ is Noetherian; the hypothesis is kept because it is
Hartshorne's setting for formal schemes.

## Depends on

- [Formal completion as a locally ringed space](formal-completion.md)
- [Affine closed subschemes](../../subschemes-and-dimension/affine-closed-subschemes.md)

## Proof depends on

No additional project-local results.

## Sources

- [Hartshorne II.9, affine formal schemes (p.195)](../../../../sources/hartshorne-ii-9.md#formal-completions-and-formal-schemes)
- [Project notation and EGA comparison policy](../../../../sources/hartshorne-ii-9.md#formal-completions-and-formal-schemes)
- Stacks Project, tag 0AHY, for the topological-ring formal spectrum.

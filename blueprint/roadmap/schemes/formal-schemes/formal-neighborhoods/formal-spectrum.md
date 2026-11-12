---
article_id: af_161869b17d76a0768818f127
declaration: def
origin: bridged
lean: Hartshorne.Spf Hartshorne.IsAffineNoetherianFormalScheme Hartshorne.specIdealSubsheaf Hartshorne.range_specIdealSubsheaf_infinitesimalNeighborhoodι Hartshorne.spfHomeomorph
statement: formalized
proof: formalized
---

# The project formal-spectrum bridge

For a Noetherian ring $A$ and ideal $I$, define project notation

$\operatorname{Spf}_I(A)=\widehat{\operatorname{Spec}A}_{V(I)}$.

The construction does not use that $A$ is Noetherian; the hypothesis is kept because it is Hartshorne's setting for formal schemes.

An affine Noetherian formal scheme is one isomorphic to such an object. This
is a representation bridge for Hartshorne's affine-completion definition;
Hartshorne does not introduce the notation $\operatorname{Spf}$, and this node asserts no
continuous-ring classification of morphisms.

## Depends on

- [Formal completion as a locally ringed space](formal-completion.md)
- [Affine closed subschemes](../../subschemes-and-dimension/affine-closed-subschemes.md)

## Proof depends on

No additional project-local results.

## Sources

- [Hartshorne II.9, affine formal schemes (p.195)](../../../../sources/hartshorne-ii-9.md#formal-completions-and-formal-schemes)
- [Project notation and EGA comparison policy](../../../../sources/hartshorne-ii-9.md#formal-completions-and-formal-schemes)
- Stacks Project, tag 0AHY, for the topological-ring formal spectrum.

---
article_id: af_0054399084d8fcffca7fc1f8
declaration: def
origin: cited
lean: Hartshorne.infinitesimalNeighborhood Hartshorne.infinitesimalNeighborhoodι Hartshorne.QuasicoherentIdealSubsheaf.pow Hartshorne.QuasicoherentIdealSubsheaf.ideal_pow Hartshorne.quasicoherentIdealSubsheafEquiv_pow Hartshorne.ker_infinitesimalNeighborhoodι Hartshorne.quasicoherentIdealSubsheafEquiv_symm_ker_infinitesimalNeighborhoodι Hartshorne.infinitesimalNeighborhoodZeroIso Hartshorne.infinitesimalNeighborhoodZeroIso_hom_comp
statement: formalized
proof: formalized
---

# Infinitesimal neighbourhoods

Let $X$ be a Noetherian scheme and let $Y \hookrightarrow X$ be a closed subscheme with
module ideal sheaf $I \hookrightarrow \mathcal{O}_X$. For nonnegative integer $n$, define the $n$th infinitesimal
neighbourhood $Y n$ to be the closed subscheme cut out by $I^{n+1}$.
In particular $Y 0 = Y$; there is no artificial quotient by $I^0$.
The construction itself does not use that $X$ is Noetherian; the hypothesis is kept because it is Hartshorne's setting for formal completions.

The powers are taken in the ideal sheaf. On affine opens, this
agrees with taking powers of the corresponding ideals.

## Depends on

- [Module ideal sheaves and ideal data](../../coherent-sheaves/module-ideal-sheaf-data.md)
- [Closed subschemes and ideal data](../../coherent-sheaves/closed-subschemes-ideal-data.md)

## Proof depends on

- Powers of quasi-coherent ideal subsheaves remain quasi-coherent.
- [Noetherian schemes and finite affine covers](../../first-properties/noetherian-scheme.md)

## Sources

- [Hartshorne II.9, introductory formal-neighbourhood discussion (p.190)](../../../../sources/hartshorne-ii-9.md#formal-completions-and-formal-schemes)

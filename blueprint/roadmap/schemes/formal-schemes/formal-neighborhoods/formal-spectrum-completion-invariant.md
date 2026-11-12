---
article_id: af_002135c46b13e5a861f9ddf7
declaration: theorem
origin: bridged
lean: Hartshorne.spf_completion_invariant Hartshorne.spfCompletionIso Hartshorne.spec_map_algebraMap_spfCompletionIso_hom_base Hartshorne.spfCompletionIso_hom_c_app_π Hartshorne.spfCompletionNeighborhoodIso Hartshorne.QuasicoherentIdealSubsheaf.formalCompletionIsoOfNeighborhoodIso
statement: formalized
proof: formalized
---

# Formal spectrum is invariant under adic completion

For Noetherian $A$ and ideal $I$, let $\widehat{A}$ be the $I$-adic completion and
let $\widehat{I} = I \widehat{A}$. Assume the usual topological formal spectrum of the
$\widehat{I}$-adic ring $\widehat{A}$ is formed from the open-prime space and the limit of
the sheaves of its discrete quotients. After forgetting the topology on
sections, construct a canonical locally ringed-space isomorphism

$\operatorname{Spf} _I(A) \cong \operatorname{Spf} _{\widehat{I}} (\widehat{A} )$.

This is an explicitly project-authored comparison justifying project $\operatorname{Spf}$
notation. Its assumptions include the open-prime/$V(I)$ homeomorphism and the
ordinary ring-valued forgetful comparison for the limit structure sheaf. It
does not identify Hartshorne's morphisms with continuous ring homomorphisms.

## Depends on

- [Affine formal schemes](formal-spectrum.md)
- [Adic completion of rings and modules](../adic-completion/adic-completion.md)
- [Noetherianity of adic completion](../adic-completion/adic-completion-noetherian.md)

## Proof depends on

- The compatible isomorphisms
  $\widehat{A} / \widehat{I} ^{n+1} \cong A / I^{n+1}$ induce an isomorphism of limit sheaves.
- [Quotients of an adic completion](../adic-completion/adic-completion-quotients.md)
- The EGA $\operatorname{Spf}$ construction and the forgetful functor from topological-ring
  sheaves are comparison inputs, not Hartshorne definitions.

## Sources

- [Hartshorne II.9, replacement by the complete affine ring in Proposition 9.6 (pp.197–198)](../../../../sources/hartshorne-ii-9.md#coherent-modules-on-formal-schemes)
- [Project-authored bridge assumptions](../../../../sources/hartshorne-ii-9.md#formal-completions-and-formal-schemes)
- Stacks Project, tag 0AHY, for comparison context.

---
article_id: af_5056302c864b51fad9cd4e29
declaration: theorem
origin: cited
lean: Hartshorne.affineFormalThickenings Hartshorne.QuasicoherentIdealSubsheaf.formalCompletionIdeal Hartshorne.QuasicoherentIdealSubsheaf.formalCompletionIdealPow Hartshorne.QuasicoherentIdealSubsheaf.formalCompletionQuotient Hartshorne.QuasicoherentIdealSubsheaf.formalCompletionQuotientIso Hartshorne.QuasicoherentIdealSubsheaf.mem_formalCompletionIdealPow_iff Hartshorne.QuasicoherentIdealSubsheaf.isLocallySurjective_formalCompletionπ Hartshorne.QuasicoherentIdealSubsheaf.formalCompletionAffineSectionsIso_formalCompletionIdeal_eq_range Hartshorne.sheafIdealPow Hartshorne.idealQuotientSheaf Hartshorne.idealQuotientSheafIso Hartshorne.specIdealSubsheafNeighborhoodIso
statement: formalized
proof: formalized
---

# Thickenings of an affine formal scheme

Let $\widehat{X} = \operatorname{Spf} _I(A)$ and let $J$ be the completion of the affine ideal sheaf
associated to $I$. Then $J$ is an ideal subsheaf of $\mathcal{O}_{\widehat{X}}$, and for every
nonnegative integer $n$ there is an isomorphism of sheaves on $V(I)$

$\mathcal{O}_{\widehat{X}} / J^{n+1} \cong \widetilde{A/I^{n+1}}$.

## Depends on

- [The project formal-spectrum bridge](formal-spectrum.md)
- [Module ideal sheaves and ideal data](../../coherent-sheaves/module-ideal-sheaf-data.md)

## Proof depends on

- [Exactness of the tilde functor](../../modules-and-quasicoherent/affine-tilde/tilde-exactness.md)
- [Quotients of an adic completion](../adic-completion/adic-completion-quotients.md)
- [Completed ideals and their powers](../adic-completion/completed-ideal-powers.md)
- [The affine section comparison on a basis of affine opens](formal-completion-affine-sections.md)

## Sources

- [Hartshorne II.9, Proposition 9.4(a) (pp.195–196)](../../../../sources/hartshorne-ii-9.md#affine-formal-schemes-and-ideals-of-definition)

---
article_id: af_5e11f59764aa47dd15042c9a
declaration: theorem
origin: cited
lean: Hartshorne.QuasicoherentIdealSubsheaf.formalCompletionBotIso Hartshorne.QuasicoherentIdealSubsheaf.formalCompletionBotIso_hom_toPresheafedSpace Hartshorne.QuasicoherentIdealSubsheaf.formalCompletionCanonicalHom Hartshorne.QuasicoherentIdealSubsheaf.instBot Hartshorne.QuasicoherentIdealSubsheaf.ideal_bot Hartshorne.isNoetherianFormalScheme_toLocallyRingedSpace Hartshorne.NoetherianFormalScheme.ofScheme Hartshorne.NoetherianFormalScheme.toNoetherianFormalSchemeBotIso Hartshorne.NoetherianFormalScheme.fromNoetherianScheme Hartshorne.NoetherianFormalScheme.fullyFaithfulFromNoetherianScheme
statement: formalized
proof: formalized
---

# Schemes as formal schemes

If a Noetherian scheme $X$ is completed along the closed subscheme $Y = X$,
then the canonical map identifies its completion with $X$ as a locally ringed
space. Consequently the category of Noetherian formal schemes includes all
Noetherian schemes. The inclusion is full, because morphisms of schemes (p.74)
and morphisms of Noetherian formal schemes (p.194) are both defined as
morphisms of locally ringed spaces.

## Depends on

- [Scheme completions are formal schemes](completion-is-formal-scheme.md)

## Proof depends on

- The defining ideal is zero and every shifted quotient by $0^{n+1}$ is
  canonically the original structure sheaf.

## Sources

- [Hartshorne II.9, Example 9.3.3 (p.195)](../../../../sources/hartshorne-ii-9.md#formal-completions-and-formal-schemes)

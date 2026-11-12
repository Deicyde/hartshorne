---
article_id: af_5b5223e84c6437d42d3f2ba4
declaration: theorem
origin: cited
lean: Hartshorne.formalCompletion_closedPoint_iso Hartshorne.formalCompletionClosedPointIso Hartshorne.closedPointIdealSubsheaf Hartshorne.onePointLocallyRingedSpace Hartshorne.formalCompletionClosedPointSectionsEquiv Hartshorne.adicCompletionLocalizationEquiv
statement: formalized
proof: formalized
---

# Completion at a closed point

Let $P$ be a closed point of a Noetherian scheme $X$. The completion of $X$
along $P$ is isomorphic to the one-point locally ringed space whose structure
ring is the completion of the local ring $\mathcal{O}_{(X,P)}$ at its maximal ideal.

The classification of its coherent modules by finite completed-local-ring
modules is supplied later by the affine formal module equivalence.

## Depends on

- [Formal completion as a locally ringed space](formal-completion.md)
- [Adic completion of rings and modules](../adic-completion/adic-completion.md)

## Proof depends on

- Affine localization near $P$ and invariance of completion under replacing
  the affine ring by its local ring at the corresponding maximal ideal.
- [Affine sections of a formal completion](formal-completion-affine-sections.md)
- [Affine formal schemes](formal-spectrum.md)

## Sources

- [Hartshorne II.9, Example 9.3.4 (p.195)](../../../../sources/hartshorne-ii-9.md#formal-completions-and-formal-schemes)

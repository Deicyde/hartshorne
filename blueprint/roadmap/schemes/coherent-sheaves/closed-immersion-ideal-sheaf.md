---
article_id: af_7b82f963dca3fff196678fde
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.isQuasicoherent_closedImmersionIdealSheaf Hartshorne.isCoherent_closedImmersionIdealSheaf Hartshorne.closedImmersionIdealSheaf Hartshorne.closedImmersionIdealSheafι Hartshorne.structureSheafToPushforward
---

# Ideal sheaves of closed immersions

Let $i : Y \to X$ be a closed immersion and define its module ideal sheaf by

$I_Y = \ker (\mathcal{O}_X \to i_*\mathcal{O}_Y)$.

Then $I_Y$ is a quasi-coherent ideal subsheaf of $\mathcal{O}_X$. If $X$ is
Noetherian, $I_Y$ is coherent.

This is the forward direction of Hartshorne's Proposition II.5.9.
The ideal sheaf is a subsheaf of the structure sheaf, with compatible
module operations.

## Depends on

- [Sheaves of modules](../modules-and-quasicoherent/sheaves-of-modules.md)
- [Quasi-coherence by local presentations](../modules-and-quasicoherent/quasicoherent-local-presentations.md)
- [The affine-local criterion for coherence](../modules-and-quasicoherent/coherent-affine-local-criterion.md)
- [Closed immersions](../subschemes-and-dimension/closed-immersions.md)
- [Noetherian schemes and finite affine covers](../first-properties/noetherian-scheme.md)

## Proof depends on

- [Pushforward preserves quasi-coherence under Hartshorne's hypotheses](../modules-and-quasicoherent/qcqs-pushforward-quasicoherent.md)
- [Abelian closure of quasi-coherent sheaves](../modules-and-quasicoherent/quasicoherent-abelian-closure.md)
- Ideals in a Noetherian ring are finitely generated.

## Sources

- [Hartshorne II.5, forward direction of Proposition 5.9 (pp.115–116)](../../../sources/hartshorne-ii-5.md#ideal-sheaves-and-closed-subschemes)

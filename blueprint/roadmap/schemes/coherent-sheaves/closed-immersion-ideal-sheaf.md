---
article_id: af_7b82f963dca3fff196678fde
declaration: theorem
origin: cited
source_units: [chapter-ii-section-5]
---

# Ideal sheaves of closed immersions

Let `i : Y → X` be a closed immersion and define its module ideal sheaf by

`I_Y = ker(O_X → i_*O_Y)`.

Then `I_Y` is a quasi-coherent ideal subsheaf of `O_X`. If `X` is
Noetherian, `I_Y` is coherent.

This is the forward direction of Proposition 5.9. It remains a statement
about an actual subobject of `X.Modules`; the comparison with Mathlib's
affine-open `IdealSheafData` is the next, separate representation bridge.

## Depends on

- [Sheaves of modules](../modules-and-quasicoherent/sheaves-of-modules.md)
- [Quasi-coherence by local presentations](../modules-and-quasicoherent/quasicoherent-local-presentations.md)
- [The affine-local criterion for coherence](../modules-and-quasicoherent/coherent-affine-local-criterion.md)
- [Closed immersions](../subschemes-and-dimension/closed-immersions.md)

## Proof depends on

- [Pushforward preserves quasi-coherence under Hartshorne's hypotheses](../modules-and-quasicoherent/qcqs-pushforward-quasicoherent.md)
- [Abelian closure of quasi-coherent sheaves](../modules-and-quasicoherent/quasicoherent-abelian-closure.md)
- Ideals in a Noetherian ring are finitely generated.

## Sources

- [Hartshorne II.5, forward direction of Proposition 5.9 (pp.115–116)](../../../sources/hartshorne-ii-5.md#ideal-sheaves-and-closed-subschemes)

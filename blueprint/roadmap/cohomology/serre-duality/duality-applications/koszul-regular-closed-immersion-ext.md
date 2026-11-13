---
article_id: af_f04792053490cdb3cfea1350
declaration: isomorphism
origin: cited
lean: Hartshorne.IsKoszulRegularImmersion.exists_isKoszulRegular_sections Hartshorne.IsKoszulRegularImmersion.isZero_sheafExt Hartshorne.KoszulTarget.sheafExtIsoDualTensor
---

# Sheaf Ext for a Koszul-regular immersion

Let $i:X\longrightarrow Y$ be a codimension-$r$ Koszul-regular closed immersion with
ideal sheaf $I$, and let $M$ be a finite locally free $\mathcal{O}_Y$-module. Then the
defining regular sequence is also $M$-regular, the lower sheaf Exts vanish,
and the top sheaf Ext has a basis-independent isomorphism

$\mathcal{E}xt^{r}_Y(i_*\mathcal{O}_X,M) \simeq M|_X \otimes (\bigwedge ^{r}(I/I^{2}))^{\vee}$.

The determinant dual is essential: it records the transformation of the top
Koszul basis under a change of local generators.

## Depends on

- [A regular sequence gives a Koszul resolution](regular-sequence-koszul-resolution.md)
- [Normal and conormal sheaves](../../../schemes/differentials/canonical-bertini/normal-conormal-sheaves.md)
- [The perfect exterior-power pairing](../../../schemes/module-exercises/exterior-perfect-pairing.md)
- [Sheaf Ext](../../ext-groups/sheaf-ext/sheaf-ext.md)
- [Locally free resolutions compute sheaf Ext](../../ext-groups/sheaf-ext/locally-free-resolution-sheaf-ext.md)
- [Locally free and invertible module sheaves](../../../schemes/modules-and-quasicoherent/locally-free-and-invertible.md)

## Proof depends on

- Sheafification of local Koszul resolutions.
- Gluing the local top-Ext calculations using the determinant transition law.

## Sources

- [Hartshorne III.7, proof of Theorem 7.11, pp.245–246](../../../../sources/hartshorne-iii-7.md#koszul-calculation-and-the-canonical-sheaf-pp245247)
- [Stacks Project, Lemma 48.15.5, tag 0BQZ](https://stacks.math.columbia.edu/tag/0BQZ)
- [Stacks Project, Lemma 48.15.6, tag 0BR0](https://stacks.math.columbia.edu/tag/0BR0)

---
article_id: af_3aee8376bb8ad4560fb74e3e
declaration: isomorphism
lean: Hartshorne.moduleSectionsIso
statement: formalized
proof: formalized
origin: cited
---

# Sections of module sheaves are representable

Let $(X,\mathcal{O}_X)$ be a ringed space and $j : U \hookrightarrow X$ an open inclusion. Write
$\mathcal{O}_U$ for $j_!(\mathcal{O}_X|_U)$, regarded as an $\mathcal{O}_X$-module. For every
$\mathcal{O}_X$-module sheaf $F$, evaluation at $1$ gives a natural additive
isomorphism

$\operatorname{Hom} _{\mathcal{O}_X}(\mathcal{O}_U,F) \cong F(U)$.

This isomorphism is used to translate injectivity into surjectivity of
restriction maps.

## Depends on

- [Sheaves of modules](../../schemes/modules-and-quasicoherent/sheaves-of-modules.md)
- [Open extension by zero](../../schemes/sheaf-functors/open-extension-by-zero.md)

## Sources

- [Hartshorne III.2, proof of Lemma 2.4, printed p. 207](../../../sources/hartshorne-iii-1-2.md#enough-injectives-and-cohomology-printed-pp-206208)

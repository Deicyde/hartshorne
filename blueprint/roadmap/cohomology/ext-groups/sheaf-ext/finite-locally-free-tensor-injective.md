---
article_id: af_6404489b1b1d9aa0e33d8b68
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.moduleSheafTensor_injective
---

# Tensoring an injective by a finite locally free sheaf

If $L$ is a finite-rank locally free $\mathcal{O}_X$-module and $J$ is injective in
the category of $\mathcal{O}_X$-modules, then $L \otimes J$ is injective.

## Depends on

- [Tensor products of module sheaves](../../../schemes/modules-and-quasicoherent/module-tensor-product.md)
- [Duality for finite locally free sheaves](../../../schemes/modules-and-quasicoherent/finite-locally-free-duality.md)

## Proof depends on

- Exactness of tensoring by $L^{\vee}$.
- The natural adjunction $\operatorname{Hom} (-,L\otimes J) \cong \operatorname{Hom} (-\otimes L^{\vee} ,J)$.

## Sources

- [Hartshorne III.6, Lemma 6.6, printed p.235](../../../../sources/hartshorne-iii-6.md#exact-sequences-and-locally-free-resolutions-printed-pp234235)

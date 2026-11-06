---
article_id: af_1a74e5d0667c096b8cd95fd1
declaration: definition
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.moduleSheafTensor Hartshorne.ModuleSheafBilinear Hartshorne.moduleSheafTensorBilinear Hartshorne.moduleSheafTensorHomEquiv Hartshorne.moduleSheafTensorHomEquiv_apply Hartshorne.moduleSheafTensorHomEquiv_comp Hartshorne.moduleSheafTensor_universal Hartshorne.moduleSheafTensorStalkIso Hartshorne.moduleSheafTensorStalkIso_germ
---

# Tensor products of module sheaves

For two $\mathcal{O} _X$-modules $F$ and $G$, construct $F\otimes_{\mathcal{O}_X}G$ by sheafifying
the presheaf $U\longmapsto F(U)\otimes_{\mathcal{O}_X(U)}G(U)$.  Prove its balanced universal
property and the canonical stalk isomorphism
$(F\otimes G)_x\cong F_x\otimes_{\mathcal{O}_{X,x}}G_x$.

## Depends on

- [Sheaves of modules](sheaves-of-modules.md)
- [The associated sheaf](../sheaves/associated-sheaf.md)

## Proof depends on

- [Sheafification preserves stalks](../sheaves/associated-sheaf-stalks.md)
- Tensor products commute with filtered colimits of modules.

## Sources

- [Hartshorne II.5, tensor product definition on printed p. 109](../../../sources/hartshorne-ii-5.md#modules-quasi-coherence-and-exactness)

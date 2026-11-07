---
article_id: af_8d2be8c21fece52c1133a2ff
declaration: definition
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.Ringed.Pic Hartshorne.Ringed.Pic.mk Hartshorne.Ringed.Pic.mk_eq_mk_iff Hartshorne.Ringed.Pic.instCommGroup Hartshorne.Ringed.Pic.mk_mul_mk Hartshorne.Ringed.Pic.one_eq_mk Hartshorne.Ringed.Pic.inv_mk Hartshorne.Ringed.isInvertible_moduleSheafTensor Hartshorne.Ringed.moduleSheafDualEval Hartshorne.Ringed.moduleSheafDualEval_isIso Hartshorne.Ringed.moduleSheafDualEvalIso Hartshorne.Ringed.isInvertible_moduleSheafDual Hartshorne.Ringed.structureModule_isInvertible
---

# The Picard group of a ringed space

For a ringed space $X$, define $\operatorname{Pic} X$ to be the group of isomorphism classes
of invertible $\mathcal{O}_X$-modules. Multiplication is tensor product, the identity is
$\mathcal{O}_X$, and inversion is the dual $\operatorname{Hom} (L,\mathcal{O}_X)$.

Prove Proposition 6.12: tensor products of invertible sheaves are invertible,
and evaluation identifies an invertible sheaf tensored with its dual with the
structure sheaf.

## Depends on

- [Locally free and invertible module sheaves](../../modules-and-quasicoherent/locally-free-and-invertible.md)
- [Tensor products of module sheaves](../../modules-and-quasicoherent/module-tensor-product.md)
- [Duality for finite locally free sheaves](../../modules-and-quasicoherent/finite-locally-free-duality.md)

## Sources

- [Hartshorne II.6, Proposition 6.12 and Picard-group definition on printed p.143](../../../../sources/hartshorne-ii-6.md#cartier-divisors-and-invertible-sheaves)

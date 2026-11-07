---
article_id: af_6419a3b53adfd67b778e0e9d
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: AlgebraicGeometry.Scheme.CartierDivisor.mulTotalQuotient AlgebraicGeometry.Scheme.CartierDivisor.tensorIso AlgebraicGeometry.Scheme.CartierDivisor.tensorIso_hom_comp_sheafι AlgebraicGeometry.Scheme.CartierDivisor.negToDual AlgebraicGeometry.Scheme.CartierDivisor.negIsoDual AlgebraicGeometry.Scheme.CartierDivisor.toK_dualEval_negToDual AlgebraicGeometry.Scheme.CartierDivisor.subIsoTensorDual AlgebraicGeometry.Scheme.CartierDivisor.subIsoTensorDual_inv_comp_sheafι AlgebraicGeometry.Scheme.CartierDivisor.subIsoTensorDual_inv_tmul
---

# Arithmetic of associated divisor sheaves

For Cartier divisors $D_1,D_2$, prove

$\mathcal{O}_X(D_1-D_2) \cong \mathcal{O}_X(D_1) \otimes \mathcal{O}_X(D_2)^{-1}$

compatibly with the embedded-submodule product inside $K_X$. This is
Proposition 6.13(b); its unique completion criterion is compatibility of
divisor subtraction with tensor product and duality.

## Depends on

- [The invertible sheaf associated to a Cartier divisor](cartier-divisor-associated-sheaf.md)
- [Tensor products of module sheaves](../../modules-and-quasicoherent/module-tensor-product.md)
- [Duality for finite locally free sheaves](../../modules-and-quasicoherent/finite-locally-free-duality.md)

## Proof depends on

- Tensor products and duals of invertible sheaves.

## Sources

- [Hartshorne II.6, Proposition 6.13(b) on printed p.144](../../../../sources/hartshorne-ii-6.md#cartier-divisors-and-invertible-sheaves)

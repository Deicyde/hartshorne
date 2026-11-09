---
article_id: af_02e151839e4bfd37f77bdaf5
declaration: isomorphism
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.affineTildeTensorIso Hartshorne.affineTildeTensorIso_hom_naturality Hartshorne.tildeCoreMonoidal Hartshorne.tildeFunctorMonoidal Hartshorne.tilde_δ_eq
---

# Tilde commutes with tensor products

For $A$-modules $M$ and $N$, construct the natural isomorphism

$\widetilde{M\otimes_A N}\cong\widetilde{M}\otimes_{\mathcal{O}_{\operatorname{Spec}A}}\widetilde{N}$.

This is Proposition 5.2(b).  It is independent of preservation of direct sums
and has the single completion criterion that the tilde functor is strong
monoidal for the module tensor product.

## Depends on

- [Tensor products of module sheaves](../module-tensor-product.md)
- [The monoidal category of sheaves of modules](../module-sheaf-monoidal-category.md)
- [The affine tilde sheaf and localization](tilde-localization.md)

## Proof depends on

- [The tilde–global-sections adjunction](tilde-gamma-adjunction.md)
- Localization commutes with tensor products.
- [Isomorphisms are detected on stalks](../../sheaves/stalkwise-isomorphism.md)

## Sources

- [Hartshorne II.5, Proposition 5.2(b) on printed p. 110](../../../../sources/hartshorne-ii-5.md#modules-quasi-coherence-and-exactness)

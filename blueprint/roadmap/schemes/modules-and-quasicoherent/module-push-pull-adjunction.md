# Pushforward, pullback, and their adjunction

For a morphism of ringed spaces $f : (X,\mathcal{O}_X) \longrightarrow (Y,\mathcal{O}_Y)$, define the module
pushforward $f_*$ by giving the ordinary direct image its $\mathcal{O}_Y$-action through
$f^{\#}$.  Define module pullback by extension of scalars,
$f^*G=f^{-1}G\otimes_{f^{-1}\mathcal{O}_Y}\mathcal{O}_X$, and prove the natural adjunction

$\operatorname{Hom} _X(f^* G, F) \simeq \operatorname{Hom} _Y(G, f_*F)$.

## Depends on

- [Tensor products of module sheaves](module-tensor-product.md)
- [Direct image of a sheaf](../sheaf-functors/direct-image.md)
- [Inverse image of a sheaf](../sheaf-functors/inverse-image.md)

## Proof depends on

- [Inverse image is left adjoint to direct image](../sheaf-functors/inverse-direct-adjunction.md)
- Extension–restriction of scalars for modules.

## Sources

- [Hartshorne II.5, direct and inverse images on printed pp. 109–110](../../../sources/hartshorne-ii-5.md#modules-quasi-coherence-and-exactness)

---
article_id: af_8763f99884b849b82e0825eb
declaration: equiv
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.quasicoherentIdealSubsheafEquiv Hartshorne.QuasicoherentIdealSubsheaf Hartshorne.quasicoherentIdealSubsheafEquiv_ideal Hartshorne.QuasicoherentIdealSubsheaf.restrictTildeIso
---

# Module ideal sheaves and ideal data

For a scheme $X$, quasi-coherent ideal subsheaves
$I\hookrightarrow\mathcal{O}_X$ correspond to compatible ideals
on affine opens. On an affine open $U$, this correspondence sends
$I$ to $\Gamma(U,I)\subseteq\Gamma(U,\mathcal{O}_X)$ and reconstructs
$I|_U$ as the tilde sheaf of that ideal.

Compatibility means that the ideals agree under restriction to
smaller affine opens. This ensures that their tilde sheaves glue.

## Depends on

- [Sheaves of modules](../modules-and-quasicoherent/sheaves-of-modules.md)
- [Quasi-coherent affine-local criterion](../modules-and-quasicoherent/quasicoherent-affine-local-criterion.md)
- [Ideal sheaves of closed immersions](closed-immersion-ideal-sheaf.md)
- [Product of an ideal sheaf with a submodule sheaf](ideal-power-product.md)

## Proof depends on

- [Affine quasi-coherent equivalence](../modules-and-quasicoherent/affine-quasicoherent-equivalence.md)
- [Quasi-coherent sheaves are closed under kernels](../modules-and-quasicoherent/quasicoherent-abelian-closure.md)
- Compatibility of the affine ideals under restriction.

## Informally uses

- [Gluing sheaves of modules along open immersions](module-gluing.md)

## Sources

- [Hartshorne II.5, definition and Proposition 5.9 (pp.115–116)](../../../sources/hartshorne-ii-5.md#ideal-sheaves-and-closed-subschemes)

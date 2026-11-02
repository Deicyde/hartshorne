---
article_id: af_4e17f763aa8b789939a367cb
declaration: def
origin: cited
lean: AlgebraicGeometry.Scheme.relativeDifferentialsWithDerivation
statement: formalized
proof: formalized
---

# The relative differential sheaf

For a scheme morphism $f : X \to Y$, construct an $\mathcal{O} _X$-module $\Omega_{X/Y}$ and a
map of sheaves of abelian groups $d:\mathcal{O}_X\longrightarrow\Omega_{X/Y}$ satisfying the Leibniz
rule and vanishing on the image of $f^{-1}\mathcal{O} _Y \to \mathcal{O} _X$. The derivation is not an
$\mathcal{O} _X$-linear morphism.

Construct the sheaf directly from the presheaf of relative differentials and
sheafification. Its universal property and the comparison with Hartshorne's
conormal-sheaf definition are recorded separately, so this definition does not
presuppose a theory of conormal sheaves for arbitrary immersions.

## Depends on

- [Schemes over a base](../../spectrum-and-schemes/over-base.md)
- [Sheaves of modules](../../modules-and-quasicoherent/sheaves-of-modules.md)
- [Pushforward, pullback, and their adjunction](../../modules-and-quasicoherent/module-push-pull-adjunction.md)
- [The universal module of Kähler differentials](../kaehler-differentials/kahler-differential-universal.md)

## Proof depends on

- Sheafification of the relative differential presheaf.

## Sources

- [Hartshorne II.8, definition and Remarks 8.9.1–8.9.2, printed p. 175](../../../../sources/hartshorne-ii-8.md)

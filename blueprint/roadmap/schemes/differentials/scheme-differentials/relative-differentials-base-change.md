---
article_id: af_5eb05ef8388c7140be706e3a
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: AlgebraicGeometry.Scheme.relativeDifferentialsBaseChangeIso AlgebraicGeometry.Scheme.isIso_baseChangeRelativeDifferentialsMap AlgebraicGeometry.Scheme.baseChangeRelativeDifferentialsMap AlgebraicGeometry.Scheme.baseChangeRelativeDifferentialsMap_unit_d
---

# Base change for differential sheaves

Let $X' = X \times _Y Y'$, with projections $g' : X' \to X$ and $f' : X' \to Y'$.
There is a canonical isomorphism of $\mathcal{O} _{X'}$-modules

$\Omega_{X'/Y'} \cong g'^* \Omega_{X/Y}$,

compatible with the universal derivations.

## Depends on

- [Differentials on affine schemes](affine-relative-differentials.md)
- [Base extension](../../fiber-products/base-extension.md)
- [Pullback preserves quasi-coherence](../../modules-and-quasicoherent/pullback-quasicoherent.md)
- [Base change for Kähler differentials](../kaehler-differentials/kahler-differential-base-change.md)
- [The transitivity sequence for differential sheaves](relative-differentials-transitivity.md)

## Proof depends on

- [Fiber products of affine schemes](../../fiber-products/affine-fiber-product.md)
- The affine-local criterion for isomorphisms of quasi-coherent modules.

## Sources

- [Hartshorne II.8, Proposition 8.10, printed p. 175](../../../../sources/hartshorne-ii-8.md)

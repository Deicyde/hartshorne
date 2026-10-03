---
declaration: equiv
origin: bridged
source_units: [chapter-ii-section-5]
---

# Module ideal sheaves and ideal data

For a scheme `X`, quasi-coherent subobjects `I ↪ O_X` in `X.Modules`
correspond to `X.IdealSheafData`. On every affine open `U`, the correspondence
sends `I` to the ideal `Γ(U,I) ⊆ Γ(U,O_X)`, and reconstructs `I|_U` as the
tilde sheaf of that ideal.

This is a representation bridge. `IdealSheafData` must not be treated as
definitionally equal to a module subsheaf: Mathlib explicitly stores
compatible ideals on affine opens rather than an object of `X.Modules`.

## Depends on

- [Sheaves of modules](../modules-and-quasicoherent/sheaves-of-modules.md)
- [Quasi-coherent affine-local criterion](../modules-and-quasicoherent/quasicoherent-affine-local-criterion.md)
- [Ideal sheaves of closed immersions](closed-immersion-ideal-sheaf.md)

## Proof depends on

- [Affine quasi-coherent equivalence](../modules-and-quasicoherent/affine-quasicoherent-equivalence.md)
- [Quasi-coherent sheaves are closed under kernels](../modules-and-quasicoherent/quasicoherent-abelian-closure.md)
- Restriction compatibility for `Scheme.IdealSheafData.ideal`.

## Sources

- [Hartshorne II.5, definition and Proposition 5.9 (pp.115–116)](../../../sources/hartshorne-ii-5.md#ideal-sheaves-and-closed-subschemes)

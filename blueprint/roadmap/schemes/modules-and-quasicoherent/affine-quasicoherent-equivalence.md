---
declaration: equivalence
origin: cited
source_units: [chapter-ii-section-5]
mathlib: true
mathlib_declaration: AlgebraicGeometry.tildeEquiv
mathlib_file: Mathlib/AlgebraicGeometry/Modules/Tilde.lean
---

# Modules and quasi-coherent sheaves on an affine scheme

For `X = Spec A`, the tilde and global-sections functors give an equivalence
between `A`-modules and quasi-coherent `𝒪_X`-modules.  Its counit is the
canonical morphism `Γ(X,F)̃ ⟶ F`; consequently an affine module sheaf is
quasi-coherent exactly when this morphism is an isomorphism.

This is Corollary 5.5 together with the affine case of Proposition 5.4.  It is
exactly `AlgebraicGeometry.tildeEquiv` in pinned Mathlib.

## Depends on

- [The tilde–global-sections adjunction](tilde-gamma-adjunction.md)
- [Quasi-coherent sections on principal opens](quasicoherent-principal-open-localization.md)

## Proof depends on

- [Quasi-coherence by local presentations](quasicoherent-local-presentations.md)
- The counit of an adjunction with invertible unit is invertible precisely on
  the essential image of the left adjoint.

## Sources

- [Hartshorne II.5, Proposition 5.4 and Corollary 5.5 on printed p. 113](../../../sources/hartshorne-ii-5.md#modules-quasi-coherence-and-exactness)

---
article_id: af_dfec7c9ac3d21093d792a513
declaration: def
origin: cited
mathlib: true
mathlib_declaration: AlgebraicGeometry.tilde.adjunction
mathlib_file: Mathlib/AlgebraicGeometry/Modules/Tilde.lean
---

# The tilde–global-sections adjunction

For $X = \operatorname{Spec} A$, the tilde functor from $A$-modules to the category of $\mathcal{O}_X$-modules is left
adjoint to global sections.  Its unit $M \longrightarrow \Gamma (X,\widetilde{M})$ is an isomorphism, so the
tilde functor is fully faithful.  Equivalently,

$\operatorname{Hom} _{\mathcal{O} _X}(\widetilde{M},F) \simeq \operatorname{Hom} _A(M,\Gamma (X,F))$.

This packages Proposition 5.2(a)'s full-faithfulness clause together with the
adjunction delegated to Exercise 5.3.  Exactness is deliberately a separate
completion result.

## Depends on

- [The affine tilde sheaf and localization](tilde-localization.md)

## Proof depends on

- A module map into global sections extends uniquely to maps on every basic
  open by the localization universal property.

## Sources

- [Hartshorne II.5, Proposition 5.2(a)](../../../sources/hartshorne-ii-5.md#modules-quasi-coherence-and-exactness)
- [Hartshorne II.5, Exercise 5.3](../../../sources/hartshorne-ii-5.md#adopted-exercises-and-later-use-evidence)

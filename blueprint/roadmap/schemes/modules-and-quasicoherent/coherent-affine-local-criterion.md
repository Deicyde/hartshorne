---
article_id: af_3f8a16b57e3c983315a69204
declaration: theorem
origin: cited
source_units: [chapter-ii-section-5]
---

# The affine-local criterion for coherence

Let `X` be a locally Noetherian scheme.  For an `𝒪_X`-module `F`, prove that
Hartshorne coherence is equivalent to Mathlib finite presentation, and to the
condition that for every affine open `U = Spec A`,

`F|_U ≅ M̃`

for a finitely generated `A`-module `M`, necessarily `M = Γ(U,F)`.  This is
the coherent clause of Proposition 5.4 and Corollary 5.5.  The Noetherian
hypothesis is essential to replace finite presentation by finite generation.

## Depends on

- [The affine-local criterion for quasi-coherence](quasicoherent-affine-local-criterion.md)
- [Finite type and finite presentation for module sheaves](finite-type-and-finite-presentation.md)

## Proof depends on

- [Noetherian schemes are local on affine opens](../first-properties/noetherian-local-on-affines.md)
- Over a Noetherian ring, every finitely generated module is finitely
  presented and submodules of finite modules are finite.
- Finite generation is detected after a finite principal-open cover.

## Sources

- [Hartshorne II.5, Proposition 5.4 and Corollary 5.5 on printed p. 113](../../../sources/hartshorne-ii-5.md#modules-quasi-coherence-and-exactness)

/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.Differentials.KaehlerConormalExactSequence
import Mathlib.RingTheory.Smooth.Kaehler

/-!
# The local cotangent space via differentials

Hartshorne, *Algebraic Geometry*, II.8, Proposition 8.7 (p. 174).

Let `B` be a local `k`-algebra whose coefficient field `k` maps isomorphically
to the residue field of `B`.  The conormal map identifies the cotangent space
`𝔪 / 𝔪²` with the fibre of the module of Kähler differentials.

## Main results

* `Hartshorne.localCotangentToDifferentials` is the canonical conormal map,
  written with the tensor factors in Hartshorne's order.
* `Hartshorne.localCotangentToDifferentials_bijective` proves that this map is
  bijective when `k` is the residue field.
* `Hartshorne.localCotangentEquivDifferentials` packages the resulting
  `k`-linear equivalence.
-/

namespace Hartshorne

noncomputable section

open scoped TensorProduct

universe u v

variable (k : Type u) (B : Type v)
variable [Field k] [CommRing B] [IsLocalRing B] [Algebra k B]

private noncomputable def coefficientFieldEquiv
    (h : Function.Bijective (algebraMap k (IsLocalRing.ResidueField B))) :
    k ≃ₐ[k] IsLocalRing.ResidueField B :=
  AlgEquiv.ofBijective (Algebra.ofId k _) h

private noncomputable def coefficientFieldSectionModSquare
    (h : Function.Bijective (algebraMap k (IsLocalRing.ResidueField B))) :
    IsLocalRing.ResidueField B →ₐ[k]
      B ⧸ (RingHom.ker (algebraMap B (IsLocalRing.ResidueField B))) ^ 2 :=
  (Algebra.ofId k _).comp (coefficientFieldEquiv k B h).symm.toAlgHom

private theorem coefficientFieldSectionModSquare_isSection
    (h : Function.Bijective (algebraMap k (IsLocalRing.ResidueField B))) :
    (IsScalarTower.toAlgHom k B (IsLocalRing.ResidueField B)).kerSquareLift.comp
        (coefficientFieldSectionModSquare k B h) =
      AlgHom.id k (IsLocalRing.ResidueField B) := by
  ext x
  obtain ⟨a, rfl⟩ := h.surjective x
  simp [coefficientFieldSectionModSquare, coefficientFieldEquiv]

private theorem kerCotangentToTensor_injective
    (h : Function.Bijective (algebraMap k (IsLocalRing.ResidueField B))) :
    Function.Injective
      (KaehlerDifferential.kerCotangentToTensor
        k B (IsLocalRing.ResidueField B)) := by
  let s :
      { g //
          (IsScalarTower.toAlgHom k B (IsLocalRing.ResidueField B)).kerSquareLift.comp g =
            AlgHom.id k (IsLocalRing.ResidueField B) } :=
    ⟨coefficientFieldSectionModSquare k B h,
      coefficientFieldSectionModSquare_isSection k B h⟩
  let r :=
    (retractionKerCotangentToTensorEquivSection
      (R := k) (P := B) (S := IsLocalRing.ResidueField B)
      IsLocalRing.residue_surjective).symm s
  apply Function.LeftInverse.injective (g := r.1)
  intro x
  have hx := LinearMap.congr_fun r.2 x
  simpa only [LinearMap.comp_apply, LinearMap.id_apply] using hx

private theorem kerCotangentToTensor_surjective
    (h : Function.Bijective (algebraMap k (IsLocalRing.ResidueField B))) :
    Function.Surjective
      (KaehlerDifferential.kerCotangentToTensor
        k B (IsLocalRing.ResidueField B)) := by
  let _ : Subsingleton
      Ω[(IsLocalRing.ResidueField B)⁄k] :=
    KaehlerDifferential.subsingleton_of_surjective
      k (IsLocalRing.ResidueField B) h.surjective
  rw [← LinearMap.range_eq_top,
    KaehlerDifferential.range_kerCotangentToTensor
      k B (IsLocalRing.ResidueField B) IsLocalRing.residue_surjective]
  rw [eq_top_iff]
  intro x hx
  rw [Submodule.restrictScalars_mem, LinearMap.mem_ker]
  exact Subsingleton.elim _ _

private theorem kerCotangentToTensor_bijective
    (h : Function.Bijective (algebraMap k (IsLocalRing.ResidueField B))) :
    Function.Bijective
      (KaehlerDifferential.kerCotangentToTensor
        k B (IsLocalRing.ResidueField B)) :=
  ⟨kerCotangentToTensor_injective k B h,
    kerCotangentToTensor_surjective k B h⟩

private noncomputable def maximalIdealCotangentEquivKer :
    IsLocalRing.CotangentSpace B ≃ₗ[B]
      (RingHom.ker (algebraMap B (IsLocalRing.ResidueField B))).Cotangent :=
  Ideal.Cotangent.equivOfEq _ _ <| by
    rw [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.ker_residue]

/-- **Hartshorne II.8, Proposition 8.7.** The canonical map from the local
cotangent space to the fibre of the module of Kähler differentials.  The final
tensor symmetry puts the differential module first, as in Hartshorne. -/
noncomputable def localCotangentToDifferentials :
    IsLocalRing.CotangentSpace B →ₗ[k]
      Ω[B⁄k] ⊗[B] IsLocalRing.ResidueField B :=
  (((TensorProduct.comm B (IsLocalRing.ResidueField B) Ω[B⁄k]).toLinearMap.comp
      (KaehlerDifferential.kerCotangentToTensor
        k B (IsLocalRing.ResidueField B))).comp
      (maximalIdealCotangentEquivKer B).toLinearMap).restrictScalars k

/-- The local cotangent-to-differentials map is bijective when the given
coefficient field maps isomorphically to the residue field. -/
theorem localCotangentToDifferentials_bijective
    (h : Function.Bijective (algebraMap k (IsLocalRing.ResidueField B))) :
    Function.Bijective (localCotangentToDifferentials k B) :=
  (TensorProduct.comm B (IsLocalRing.ResidueField B) Ω[B⁄k]).bijective.comp
    ((kerCotangentToTensor_bijective k B h).comp
      (maximalIdealCotangentEquivKer B).bijective)

/-- **Hartshorne II.8, Proposition 8.7.** If the coefficient field is the
residue field, the local cotangent space is canonically `k`-linearly
equivalent to the fibre of the module of Kähler differentials. -/
noncomputable def localCotangentEquivDifferentials
    (h : Function.Bijective (algebraMap k (IsLocalRing.ResidueField B))) :
    IsLocalRing.CotangentSpace B ≃ₗ[k]
      Ω[B⁄k] ⊗[B] IsLocalRing.ResidueField B :=
  LinearEquiv.ofBijective (localCotangentToDifferentials k B)
    (localCotangentToDifferentials_bijective k B h)

end

end Hartshorne

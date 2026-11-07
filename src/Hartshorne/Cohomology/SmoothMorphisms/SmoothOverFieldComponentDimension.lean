/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.FlatFamilies.FlatEquidimensional
import Hartshorne.Scheme.Differentials.StandardSmoothFieldDimension
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Irreducible components of a scheme smooth over a field

Let `Z` be a scheme of finite type over a field `K` such that `Z → Spec K` is smooth of relative
dimension `n` (locally standard smooth of relative dimension `n`). Then every irreducible
component of `Z` has dimension `n`.

Let `ζ` be the generic point of the component. On an affine chart `Spec S ⊆ Z` around `ζ` with
`S` standard smooth of relative dimension `n` over `K`, `ζ` is a minimal prime `q`, so
`dim S_q = 0`, and `dim S_q + dim S ⧸ q = n`. The dimension of the component is the height of
`ζ` in the specialization order, which can be computed on the chart, where it is `dim S ⧸ q`.

This is the fibre-dimension clause in the comparison of Hartshorne's definition of a smooth
morphism (III.10, p. 268) with the standard smooth predicate.

## Main result

* `Hartshorne.topologicalKrullDim_of_mem_irreducibleComponents_of_smoothOfRelativeDimension`
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Order

namespace Hartshorne

universe u

open FlatEquidimensional

/-- Let `Z → Spec K` be of finite type and smooth of relative dimension `n` over a field `K`.
Every irreducible component of `Z` has dimension `n`. -/
theorem topologicalKrullDim_of_mem_irreducibleComponents_of_smoothOfRelativeDimension
    {K : Type u} [Field K] {Z : Scheme.{u}} (s : Z ⟶ Spec (.of K)) (hs : FiniteType s) (n : ℕ)
    [SmoothOfRelativeDimension n s] {C : Set Z} (hC : C ∈ irreducibleComponents Z) :
    topologicalKrullDim C = n := by
  obtain ⟨ζ, rfl⟩ := exists_closure_eq hC
  rw [topologicalKrullDim_closure_singleton]
  obtain ⟨U, hU, V, hV, hζV, e, hf⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := s) ζ
  -- The base chart is all of `Spec K`, whose ring of sections is a field.
  obtain rfl : U = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have : x = s ζ := Subsingleton.elim _ _
    rw [this]
    exact e hζV
  have hfield : IsField Γ(Spec (.of K), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField K)
  let : Field Γ(Spec (.of K), ⊤) := hfield.toField
  let := (s.appLE ⊤ V e).hom.toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension n Γ(Spec (.of K), ⊤) Γ(Z, V) := hf
  obtain ⟨ι, σ, _, _, P, hP⟩ := this
  -- The point `ζ` on the chart `Spec Γ(Z, V)`.
  set t := hV.primeIdealOf ⟨ζ, hζV⟩
  have hft : hV.fromSpec t = ζ := hV.fromSpec_primeIdealOf ⟨ζ, hζV⟩
  have : IsOpenImmersion hV.fromSpec := hV.isOpenImmersion_fromSpec
  have hheight := height_apply_of_isOpenImmersion s hs hV.fromSpec t
  rw [hft] at hheight
  rw [hheight, height_spec_eq]
  -- `dim O_{Z,ζ} = 0` since `ζ` is a maximal point.
  have hcoh : coheight ζ = 0 := by
    rw [coheight_eq_zero]
    intro z hz
    have hzC : closure ({ζ} : Set Z) ⊆ closure {z} :=
      closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hz))
        isClosed_closure
    have hirr : IsIrreducible (closure ({z} : Set Z)) := isIrreducible_singleton.closure
    have heq := hC.2 hirr hzC
    have hz' : z ∈ closure ({ζ} : Set Z) := heq (subset_closure rfl)
    exact specializes_iff_mem_closure.mpr hz'
  have hstalk : ringKrullDim (Z.presheaf.stalk ζ) = 0 := by
    rw [ringKrullDim_stalk_eq_coheight, hcoh]
    rfl
  have hloc : ringKrullDim (Localization.AtPrime t.asIdeal) = 0 := by
    let := TopCat.Presheaf.algebra_section_stalk Z.presheaf ⟨ζ, hζV⟩
    have := hV.isLocalization_stalk ⟨ζ, hζV⟩
    rw [← hstalk]
    exact ringKrullDim_eq_of_ringEquiv
      (IsLocalization.algEquiv t.asIdeal.primeCompl (Localization.AtPrime t.asIdeal)
        (Z.presheaf.stalk ζ)).toRingEquiv
  have key := SubmersivePresentation.ringKrullDim_localization_add_ringKrullDim_quotient P
    t.asIdeal
  rw [hloc, zero_add, hP] at key
  exact key

end Hartshorne

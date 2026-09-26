/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Curve.Basic
import Hartshorne.Curve.DVR
import Hartshorne.Curve.FunctionFieldDVR
import Hartshorne.Curve.KrullAkizuki
import Hartshorne.Morphism.LocalRingFunctionField
import Hartshorne.Nonsingular.LocalRingDimension
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Function-field DVRs dominating local rings

Hartshorne, *Algebraic Geometry*, I.6, proof of Theorem 6.9 (p. 45).

At a point of a curve, the image of the local ring in the function field is
dominated by a valuation subring.  Krull--Akizuki makes that valuation subring
Noetherian.  It cannot be a field, since the local inclusion would then make
the one-dimensional source local ring a field.  A nonfield Noetherian
valuation ring is a discrete valuation ring.
-/

namespace Hartshorne

noncomputable section

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

namespace Variety

/-- A local ring on a curve is dominated, inside the function field, by a
function-field DVR.  The order on `LocalSubring` records both inclusion and
locality of the inclusion. -/
theorem HasAffineOpenBasis.exists_functionFieldDVR_dominating_localRing
    {Y : Variety k} (hY : Y.HasAffineOpenBasis) (hcurve : Y.IsCurve)
    (Q : Y.carrier) :
    ∃ R : FunctionFieldDVR k Y.FunctionField,
      LocalSubring.range (Y.localToFunctionFieldAlgHom Q).toRingHom ≤
        R.toValuationSubring.toLocalSubring := by
  let A := Y.LocalRingAt Q
  let K := Y.FunctionField
  let A₀ : LocalSubring K :=
    LocalSubring.range (Y.localToFunctionFieldAlgHom Q).toRingHom
  obtain ⟨V, hV⟩ := A₀.exists_le_valuationSubring
  have hAV (a : A) : algebraMap A K a ∈ V := by
    apply hV.1
    exact ⟨a, rfl⟩
  let i : A →+* V := (algebraMap A K).codRestrict V.toSubring hAV
  let _ : Algebra A V := i.toAlgebra
  let _ : IsScalarTower A V K :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let _ : IsNoetherianRing A := hY.isNoetherianRing_localRingAt Q
  have hdim : ringKrullDim A = 1 :=
    (hY.ringKrullDim_localRingAt_eq Q).trans hcurve
  let _ : Ring.KrullDimLE 1 A := Ring.krullDimLE_iff.mpr hdim.le
  let _ : IsFractionRing A K := hY.isFractionRing_localRingAt Q
  let _ : NoZeroSMulDivisors V K := by
    constructor
    intro c x hcx
    rw [Algebra.smul_def] at hcx
    rcases mul_eq_zero.mp hcx with hc | hx
    · left
      apply Subtype.ext
      exact hc
    · exact Or.inr hx
  let _ : IsNoetherianRing V :=
    krullAkizuki_isNoetherianRing A K K V
  have hi_local : IsLocalHom i := by
    let g : A →+* A₀.toSubring :=
      (Y.localToFunctionFieldAlgHom Q).toRingHom.rangeRestrict
    let j : A₀.toSubring →+* V := Subring.inclusion hV.1
    let _ : IsLocalHom g :=
      IsLocalHom.of_surjective g
        (Y.localToFunctionFieldAlgHom Q).toRingHom.rangeRestrict_surjective
    let _ : IsLocalHom j := hV.2
    rw [show i = j.comp g by ext; rfl]
    infer_instance
  have hA_not_field : ¬ IsField A := fun hA ↦
    zero_ne_one ((ringKrullDim_eq_zero_of_isField hA).symm.trans hdim)
  have hV_not_field : ¬ IsField V := by
    intro hVfield
    let _ : IsLocalHom i := hi_local
    apply hA_not_field
    apply IsLocalHom.isField (f := i)
    · intro a b hab
      apply Y.localToFunctionFieldAlgHom_injective Q
      exact congrArg Subtype.val hab
    · exact hVfield
  have hVdvr : IsDiscreteValuationRing V :=
    ((IsDiscreteValuationRing.TFAE V hV_not_field).out 1 0).mp
      (inferInstance : ValuationRing V)
  have hk (x : k) : algebraMap k K x ∈ V := by
    apply hV.1
    refine ⟨algebraMap k A x, ?_⟩
    exact (Y.localToFunctionFieldAlgHom Q).commutes x
  exact ⟨⟨V, hVdvr, hk⟩, hV⟩

end Variety

end

end Hartshorne

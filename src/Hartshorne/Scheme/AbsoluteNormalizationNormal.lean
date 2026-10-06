/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.AbsoluteNormalization
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed

/-!
# Normality and integrality of the absolute normalization

Hartshorne, *Algebraic Geometry*, Exercise II.3.8, p. 91.
-/

noncomputable section

open CategoryTheory

namespace Hartshorne

open AlgebraicGeometry

universe u

instance absoluteNormalization_isIntegral
    (X : Scheme.{u}) [IsIntegral X] :
    IsIntegral (absoluteNormalization X) := by
  change IsIntegral ((absoluteNormalizationGenericMap X).normalization)
  infer_instance

instance absoluteNormalization_isNormal
    (X : Scheme.{u}) [IsIntegral X] :
    IsNormal (absoluteNormalization X) where
  isDomain_stalk x := inferInstance
  isIntegrallyClosed_stalk x := by
    let ν := absoluteNormalizationMap X
    let U : X.Opens :=
      (X.affineCover.f (X.affineCover.idx (ν x))).opensRange
    have hU : IsAffineOpen U := isAffineOpen_opensRange _
    have hxU : ν x ∈ U := X.affineCover.covers (ν x)
    let _ : Nonempty U := ⟨⟨ν x, hxU⟩⟩
    let V : (absoluteNormalization X).Opens := ν ⁻¹ᵁ U
    have hV : IsAffineOpen V := hU.preimage ν
    have hxV : x ∈ V := hxU
    let xV : V := ⟨x, hxV⟩
    let _ : Nonempty V := ⟨xV⟩
    let e : Γ(absoluteNormalization X, V) ≃+*
        integralClosure Γ(X, U) X.functionField :=
      (absoluteNormalizationObjIso X hU).commRingCatIsoToRingEquiv
    have hB : IsIntegrallyClosed
        (integralClosure Γ(X, U) X.functionField) := by
      let _ : IsFractionRing Γ(X, U) X.functionField :=
        functionField_isFractionRing_of_isAffineOpen X U hU
      exact integralClosure.isIntegrallyClosedOfFiniteExtension X.functionField
    let _ : IsIntegrallyClosed Γ(absoluteNormalization X, V) :=
      hB.of_equiv e.symm
    let p := (hV.primeIdealOf xV).asIdeal
    let _ : Algebra Γ(absoluteNormalization X, V)
        ((absoluteNormalization X).presheaf.stalk x) :=
      TopCat.Presheaf.algebra_section_stalk (absoluteNormalization X).presheaf xV
    let _ : IsLocalization.AtPrime
        ((absoluteNormalization X).presheaf.stalk x) p :=
      hV.isLocalization_stalk xV
    exact isIntegrallyClosed_of_isLocalization
      ((absoluteNormalization X).presheaf.stalk x) p.primeCompl
        p.primeCompl_le_nonZeroDivisors

/-- The absolute normalization of an integral scheme is a normal integral
scheme. -/
theorem absoluteNormalization_isNormal_and_isIntegral
    (X : Scheme.{u}) [IsIntegral X] :
    IsNormal (absoluteNormalization X) ∧
      IsIntegral (absoluteNormalization X) :=
  ⟨inferInstance, inferInstance⟩

end Hartshorne

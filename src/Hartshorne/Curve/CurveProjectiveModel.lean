/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Curve.FunctionFieldProjectiveModel
import Hartshorne.Rational.BirationalCriterion

/-!
# Projective models of curves

Hartshorne, *Algebraic Geometry*, I.6, Corollary 6.11 (p. 45).

Every curve is birational to a nonsingular projective curve.  We apply the
projective-model theorem to its one-dimensional function field and then use
the function-field criterion for birationality.
-/

namespace Hartshorne

noncomputable section

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {σ : Type u} [Finite σ]
variable {X : Set (ProjectiveSpace k σ)}

/-- **Hartshorne I.6, Corollary 6.11.** Every quasi-projective curve is
birational to a nonsingular projective curve. -/
theorem IsQuasiProjVariety.birational_nonsingular_projective
    (hX : IsQuasiProjVariety X)
    (hcurve : (Variety.ofQuasiProjective hX).IsCurve) :
    ∃ (τ : Type u) (_ : Finite τ) (_ : Nonempty τ)
      (Y : Set (ProjectiveSpace k τ)) (hY : IsProjVariety Y),
        (Variety.ofProjective hY).IsCurve ∧
        (Variety.ofProjective hY).Nonsingular ∧
        Birational
          ⟨Variety.ofQuasiProjective hX,
            isSeparated_ofQuasiProjective hX⟩
          ⟨Variety.ofProjective hY,
            isSeparated_ofQuasiProjective hY.isQuasiProjVariety⟩ := by
  classical
  have hσ : Nonempty σ := by
    obtain ⟨P, _⟩ := hX.1
    by_contra h
    apply P.rep_nonzero
    funext i
    exact (h ⟨i⟩).elim
  let _ := hσ
  let V := Variety.ofQuasiProjective hX
  let hVaff := Variety.hasAffineOpenBasis_ofQuasiProjective hX
  let _ : Algebra.EssFiniteType k V.FunctionField :=
    RationalMapFunctionField.essFiniteType_functionField hVaff
  have htrdeg : Algebra.trdeg k V.FunctionField = 1 :=
    (Variety.HasAffineOpenBasis.isCurve_iff_trdeg_eq_one hVaff).mp hcurve
  obtain ⟨D, _, hDcurve, hDnonsingular⟩ :=
    ValuationSpace.exists_nonsingular_projective_model htrdeg
  let _ := D.M₀.finite_ι
  let _ := D.M₁.finite_ι
  let S_X : SeparatedVariety k :=
    ⟨V, isSeparated_ofQuasiProjective hX⟩
  let S_Y : SeparatedVariety k :=
    ⟨Variety.ofProjective D.isProjVariety,
      isSeparated_ofQuasiProjective D.isProjVariety.isQuasiProjVariety⟩
  have hbirational : Birational S_X S_Y := by
    apply (birational_iff_nonempty_functionField_algEquiv S_X S_Y
      hVaff (Variety.hasAffineOpenBasis_ofProjective D.isProjVariety)).mpr
    exact ⟨(projectiveDiagonalFunctionFieldAlgEquiv D).symm⟩
  refine ⟨Option D.M₀.ι × Option D.M₁.ι, inferInstance,
    inferInstance, D.Y, D.isProjVariety, hDcurve, hDnonsingular, ?_⟩
  exact hbirational

end

end Hartshorne

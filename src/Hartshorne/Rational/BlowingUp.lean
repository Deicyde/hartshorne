/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Rational.BlowingUpExceptional
import Hartshorne.Rational.BlowingUpStrictTransform

/-!
# Blowing up affine space at the origin

Hartshorne, *Algebraic Geometry*, I.4, pp. 28–29.

This collects the construction and four basic properties of the blow-up of
affine space at the origin.  The incidence locus is closed relative to
`A^σ × P^σ`; it is not incorrectly asserted to be closed in the surrounding
projective space.
-/

namespace Hartshorne

open TopologicalSpace
open scoped Hartshorne

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {σ : Type u} [Finite σ] [DecidableEq σ] [Nonempty σ]

/-- The proposition collecting Hartshorne I.4's four properties of the
blow-up of affine space at the origin and its resulting birationality. -/
def AffineBlowupProperties : Prop :=
    let hBlow := isQuasiProjVariety_blowupSet (k := k) (σ := σ)
    let hAffine :=
      (affineSpace_isAffineVariety (k := k) (σ := σ)).isQuasiAffineVariety
    IsQuasiProjVariety (blowupSet (k := k) (σ := σ)) ∧
      IsClosed (blowupLocus (k := k) (σ := σ)) ∧
      (∀ P : BlowupAffineChart (k := k) (σ := σ),
        P ≠ blowupOrigin →
          ∃! R : BlowupPoint (k := k) (σ := σ), blowupAffine R = P) ∧
      (blowupProjectionPuncturedHom hBlow).IsIso ∧
      blowupExceptionalSet (k := k) (σ := σ) =
        exceptionalFibreFlat (k := k) (σ := σ) ∧
      (exceptionalDirectionHom (k := k) (σ := σ)).IsIso ∧
      (∀ Q : ProjectiveSpace k σ,
        blowupLineCurve (k := k) Q.rep Q.rep_nonzero blowupLineZero =
            exceptionalPoint (k := k) Q ∧
          blowupLineCurve (k := k) Q.rep Q.rep_nonzero ''
              blowupLinePunctured (k := k) ⊆
            blowupOrdinaryLocus (k := k) (σ := σ) ∧
          blowupLineCurve (k := k) Q.rep Q.rep_nonzero blowupLineZero ∈
            closure (blowupLineCurve (k := k) Q.rep Q.rep_nonzero ''
              blowupLinePunctured (k := k))) ∧
      Dense (blowupOrdinaryLocus (k := k) (σ := σ)) ∧
      IsIrreducible (blowupSet (k := k) (σ := σ)) ∧
      Birational
        ⟨Variety.ofQuasiProjective hBlow,
          isSeparated_ofQuasiProjective hBlow⟩
        ⟨Variety.ofQuasiAffine hAffine,
          RationalMapFunctionField.isSeparated_ofQuasiAffine hAffine⟩

/-- Hartshorne I.4's four properties of the blow-up of affine space at the
origin, together with the resulting birationality statement. -/
theorem affineBlowup_properties :
    AffineBlowupProperties (k := k) (σ := σ) := by
  unfold AffineBlowupProperties
  dsimp only
  refine ⟨isQuasiProjVariety_blowupSet (k := k) (σ := σ),
    isClosed_blowupLocus (k := k) (σ := σ),
    ?_, isIso_blowupProjectionPunctured
      (isQuasiProjVariety_blowupSet (k := k) (σ := σ)),
    blowupExceptionalSet_eq_fibre (k := k) (σ := σ),
    exceptionalDirectionHom_isIso (k := k) (σ := σ),
    ?_, dense_blowupOrdinaryLocus (k := k) (σ := σ),
    isIrreducible_blowupSet (k := k) (σ := σ), ?_⟩
  · intro P hP
    exact existsUnique_fibre_of_ne_origin P hP
  · intro Q
    refine ⟨?_,
      blowupLineCurve_punctured_subset_ordinary Q.rep Q.rep_nonzero,
      blowupLineCurve_zero_mem_closure_image Q.rep Q.rep_nonzero⟩
    rw [blowupLineCurve_zero, Q.mk_rep]
  · exact birational_affineBlowup
      (isQuasiProjVariety_blowupSet (k := k) (σ := σ))

/-- **Blowing up a point (Hartshorne I.4).**  The incidence construction has
the four stated properties.  For every affine variety through the origin, its
strict transform is birational to it when the punctured locus is nonempty; in
the sole remaining case the variety is `{0}` and its strict transform is
empty. -/
theorem blowing_up :
    AffineBlowupProperties (k := k) (σ := σ) ∧
      ∀ (Y : Set (σ → k)) (hY : IsAffineVariety Y)
          (_hzero : (0 : σ → k) ∈ Y),
        (∃ hne : (affineSubvarietyPunctured Y).Nonempty,
          IsQuasiProjVariety (strictTransform (k := k) (σ := σ) Y) ∧
            (strictTransformProjectionPunctured hY hne).IsIso ∧
            Birational
              ⟨Variety.ofQuasiProjective
                  (isQuasiProjVariety_strictTransform hY hne),
                isSeparated_ofQuasiProjective
                  (isQuasiProjVariety_strictTransform hY hne)⟩
              ⟨Variety.ofQuasiAffine hY.isQuasiAffineVariety,
                RationalMapFunctionField.isSeparated_ofQuasiAffine
                  hY.isQuasiAffineVariety⟩) ∨
          (Y = {0} ∧ strictTransform (k := k) (σ := σ) Y = ∅) := by
  refine ⟨affineBlowup_properties (k := k) (σ := σ), ?_⟩
  intro Y hY hzero
  exact strictTransform_dichotomy hY hzero

end Hartshorne

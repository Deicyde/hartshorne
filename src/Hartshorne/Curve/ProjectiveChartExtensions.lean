/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Curve.ProjectiveExtension
import Hartshorne.Curve.TwoAffineChartCover

/-!
# Projective closures of the two affine charts

Hartshorne, *Algebraic Geometry*, I.6, proof of Theorem 6.9 (p. 44).

The two affine normalization models covering the abstract valuation curve are
put into projective space by adjoining a homogenizing coordinate.  Their open
identifications with the valuation curve then extend to morphisms from the
whole abstract curve to the two projective closures.
-/

namespace Hartshorne

open Set TopologicalSpace
open scoped Hartshorne

noncomputable section

universe u

namespace ValuationSpace

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

namespace AffineNormalizationModel

variable [IsAlgClosed k] [Algebra.EssFiniteType k K]
variable {htrdeg : Algebra.trdeg k K = 1}
variable {C : SeparableNormalizationChart k K}

/-- The projective closure of an affine normalization model, using `none` as
the homogenizing coordinate and `some i` for each original affine coordinate. -/
noncomputable def projectiveClosure (M : AffineNormalizationModel htrdeg C) :
    Set (ProjectiveSpace k (Option M.ι)) := by
  classical
  exact Hartshorne.projectiveClosure (none : Option M.ι) M.projectiveReindex

/-- The projective closure of an affine normalization model is a projective
variety. -/
theorem projectiveClosure_isProjVariety
    (M : AffineNormalizationModel htrdeg C) :
    IsProjVariety M.projectiveClosure := by
  classical
  exact Hartshorne.projectiveClosure_isProjVariety
    (none : Option M.ι) M.projectiveReindex_isAffineVariety

/-- The defining affine chart of the projective closure is nonempty. -/
theorem projectiveClosure_chart_nonempty
    (M : AffineNormalizationModel htrdeg C) :
    (M.projectiveClosure ∩ standardChart (none : Option M.ι)).Nonempty := by
  classical
  exact Hartshorne.projectiveClosure_inter_standardChart_nonempty
    (none : Option M.ι) M.projectiveReindex_isAffineVariety

/-- The original affine model mapped into its projective closure through the
standard affine chart. -/
noncomputable def affineToProjectiveClosure
    (M : AffineNormalizationModel htrdeg C) :
    VarietyHom
      (Variety.ofQuasiAffine M.isAffineVariety.isQuasiAffineVariety)
      (Variety.ofProjective M.projectiveClosure_isProjVariety) := by
  classical
  let _ := M.finite_ι
  let hP := M.projectiveClosure_isProjVariety
  let hne := M.projectiveClosure_chart_nonempty
  let reindexToChart : VarietyHom
      (Variety.ofQuasiAffine
        M.projectiveReindex_isAffineVariety.isQuasiAffineVariety)
      (chartTarget k (none : Option M.ι) hP.isQuasiProjVariety hne) :=
    Classical.choose
      (Hartshorne.projectiveClosureChartToAffineHom_isIso
        (none : Option M.ι) M.projectiveReindex_isAffineVariety)
  let chartToRestriction : VarietyHom
      (chartTarget k (none : Option M.ι) hP.isQuasiProjVariety hne)
      ((Variety.ofProjective hP).restrict
        (projectiveChartOpen hP.isQuasiProjVariety (none : Option M.ι))
        (projectiveChartOpen_nonempty hP.isQuasiProjVariety
          (none : Option M.ι) hne)) :=
    Classical.choose
      (isIso_restrictChartHom hP.isQuasiProjVariety
        (none : Option M.ι) hne)
  let chartInclusion : VarietyHom
      ((Variety.ofProjective hP).restrict
        (projectiveChartOpen hP.isQuasiProjVariety (none : Option M.ι))
        (projectiveChartOpen_nonempty hP.isQuasiProjVariety
          (none : Option M.ι) hne))
      (Variety.ofProjective hP) :=
    (Variety.ofProjective hP).inclHom
      (projectiveChartOpen hP.isQuasiProjVariety (none : Option M.ι))
      (projectiveChartOpen_nonempty hP.isQuasiProjVariety
        (none : Option M.ι) hne)
  exact chartInclusion.comp
    (chartToRestriction.comp (reindexToChart.comp M.toProjectiveReindex))

/-- The inverse of the chosen identification between an affine normalization
model and its open image in the full valuation curve. -/
noncomputable def imageToAffine
    (M : AffineNormalizationModel htrdeg C) :
    VarietyHom
      ((abstractNonsingularCurveOfFunctionField htrdeg).restrict
        M.imageOpen M.imageOpen_nonempty)
      (Variety.ofQuasiAffine M.isAffineVariety.isQuasiAffineVariety) :=
  Classical.choose M.chartToImage_isIso

/-- The chosen inverse really is a left inverse to the chart identification. -/
theorem imageToAffine_comp_chartToImage
    (M : AffineNormalizationModel htrdeg C) :
    M.imageToAffine.comp M.chartToImage =
      VarietyHom.id
        (Variety.ofQuasiAffine M.isAffineVariety.isQuasiAffineVariety) :=
  (Classical.choose_spec M.chartToImage_isIso).1

/-- The original open identification, now viewed as a morphism into the
projective closure. -/
noncomputable def imageToProjectiveClosure
    (M : AffineNormalizationModel htrdeg C) :
    VarietyHom
      ((abstractNonsingularCurveOfFunctionField htrdeg).restrict
        M.imageOpen M.imageOpen_nonempty)
      (Variety.ofProjective M.projectiveClosure_isProjVariety) :=
  M.affineToProjectiveClosure.comp M.imageToAffine

theorem imageToProjectiveClosure_comp_chartToImage
    (M : AffineNormalizationModel htrdeg C) :
    M.imageToProjectiveClosure.comp M.chartToImage =
      M.affineToProjectiveClosure := by
  rw [imageToProjectiveClosure, VarietyHom.comp_assoc,
    M.imageToAffine_comp_chartToImage, VarietyHom.comp_id]

end AffineNormalizationModel

/-- **Hartshorne I.6, construction in the proof of Theorem 6.9.**  The two
affine normalization models covering the valuation curve have projective
closures, and their open affine identifications extend to morphisms from the
whole valuation curve. -/
theorem exists_two_projective_chart_extensions [IsAlgClosed k]
    [Algebra.EssFiniteType k K]
    (htrdeg : Algebra.trdeg k K = 1) :
    let C := separableNormalizationCharts k K htrdeg
    ∃ (M₀ : AffineNormalizationModel htrdeg C.atZero)
      (M₁ : AffineNormalizationModel htrdeg C.atInfinity),
      (M₀.imageOpen : Set
          (abstractNonsingularCurveOfFunctionField htrdeg).carrier) ∪
        (M₁.imageOpen : Set
          (abstractNonsingularCurveOfFunctionField htrdeg).carrier) = Set.univ ∧
      ∃ (Φ₀ : VarietyHom
          (abstractNonsingularCurveOfFunctionField htrdeg)
          (Variety.ofProjective M₀.projectiveClosure_isProjVariety))
        (Φ₁ : VarietyHom
          (abstractNonsingularCurveOfFunctionField htrdeg)
          (Variety.ofProjective M₁.projectiveClosure_isProjVariety)),
        Φ₀.comp M₀.embedding = M₀.affineToProjectiveClosure ∧
          Φ₁.comp M₁.embedding = M₁.affineToProjectiveClosure := by
  classical
  dsimp only
  obtain ⟨M₀, M₁, hcover⟩ := exists_two_affine_model_cover htrdeg
  let _ := M₀.finite_ι
  let _ := M₁.finite_ι
  have htop : ((⊤ : Opens (ValuationSpace k K)) :
      Set (ValuationSpace k K)).Nonempty := by
    let _ : Infinite (FunctionFieldDVR k K) :=
      FunctionFieldDVR.infinite_of_trdeg_eq_one htrdeg
    exact Set.univ_nonempty
  have hExt₀ :
      ∃! Φ : VarietyHom
          (abstractNonsingularCurveOfFunctionField htrdeg)
          (Variety.ofProjective M₀.projectiveClosure_isProjVariety),
        Φ.comp ((abstractNonsingularCurveOfFunctionField htrdeg).inclHom
          M₀.imageOpen M₀.imageOpen_nonempty) =
            M₀.imageToProjectiveClosure := by
    simpa only [abstractNonsingularCurveOfFunctionField] using
      (existsUnique_projective_extension_of_open
        htrdeg (⊤ : Opens (ValuationSpace k K)) htop
          M₀.imageOpen M₀.imageOpen_nonempty
          M₀.projectiveClosure_isProjVariety M₀.imageToProjectiveClosure)
  have hExt₁ :
      ∃! Φ : VarietyHom
          (abstractNonsingularCurveOfFunctionField htrdeg)
          (Variety.ofProjective M₁.projectiveClosure_isProjVariety),
        Φ.comp ((abstractNonsingularCurveOfFunctionField htrdeg).inclHom
          M₁.imageOpen M₁.imageOpen_nonempty) =
            M₁.imageToProjectiveClosure := by
    simpa only [abstractNonsingularCurveOfFunctionField] using
      (existsUnique_projective_extension_of_open
        htrdeg (⊤ : Opens (ValuationSpace k K)) htop
          M₁.imageOpen M₁.imageOpen_nonempty
          M₁.projectiveClosure_isProjVariety M₁.imageToProjectiveClosure)
  obtain ⟨Φ₀, hΦ₀, -⟩ := hExt₀
  obtain ⟨Φ₁, hΦ₁, -⟩ := hExt₁
  refine ⟨M₀, M₁, hcover, Φ₀, Φ₁, ?_, ?_⟩
  · rw [← M₀.embedding_factorization, ← VarietyHom.comp_assoc, hΦ₀,
      M₀.imageToProjectiveClosure_comp_chartToImage]
  · rw [← M₁.embedding_factorization, ← VarietyHom.comp_assoc, hΦ₁,
      M₁.imageToProjectiveClosure_comp_chartToImage]

end ValuationSpace

end

end Hartshorne

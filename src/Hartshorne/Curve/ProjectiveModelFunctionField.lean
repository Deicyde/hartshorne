/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Curve.ProjectiveDiagonal
import Hartshorne.Rational.RationalMapFunctionFieldEquivalence

/-!
# The function field of the projective diagonal model

Hartshorne, *Algebraic Geometry*, I.6, proof of Theorem 6.9 (pp. 44--45).

The dense diagonal morphism into the closure of its image induces an
isomorphism on function fields.  The proof compares its pullback with the
first affine normalization chart through the restricted Segre projection.
-/

namespace Hartshorne

open Set TopologicalSpace
open scoped Hartshorne

noncomputable section

universe u

private theorem VarietyHom.functionFieldAlgHom_comp'
    {k : Type u} [Field k] {X Y Z : Variety k}
    (g : VarietyHom Y Z) (f : VarietyHom X Y)
    (hg : DenseRange g.toFun) (hf : DenseRange f.toFun)
    (hgf : DenseRange (g.comp f).toFun) :
    (g.comp f).functionFieldAlgHom hgf =
      (f.functionFieldAlgHom hf).comp (g.functionFieldAlgHom hg) := by
  ext q
  refine Quotient.inductionOn q ?_
  intro r
  apply Quotient.sound
  intro x hx hx'
  rfl

private theorem VarietyHom.functionFieldAlgHom_congr'
    {k : Type u} [Field k] {X Y : Variety k}
    {f g : VarietyHom X Y} (h : f = g)
    (hf : DenseRange f.toFun) (hg : DenseRange g.toFun) :
    f.functionFieldAlgHom hf = g.functionFieldAlgHom hg := by
  subst g
  rfl

namespace ValuationSpace

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable [IsAlgClosed k] [Algebra.EssFiniteType k K]

namespace AffineNormalizationModel

variable {htrdeg : Algebra.trdeg k K = 1}
variable {C : SeparableNormalizationChart k K}

private theorem affineToProjectiveClosure_dense
    (M : AffineNormalizationModel htrdeg C) :
    DenseRange M.affineToProjectiveClosure.toFun := by
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
  have hReindexToChartIso : reindexToChart.IsIso := by
    refine ⟨projectiveClosureChartToAffineHom
      (none : Option M.ι) M.projectiveReindex_isAffineVariety, ?_, ?_⟩
    · exact (Classical.choose_spec
        (Hartshorne.projectiveClosureChartToAffineHom_isIso
          (none : Option M.ι) M.projectiveReindex_isAffineVariety)).2
    · exact (Classical.choose_spec
        (Hartshorne.projectiveClosureChartToAffineHom_isIso
          (none : Option M.ι) M.projectiveReindex_isAffineVariety)).1
  have hChartToRestrictionIso : chartToRestriction.IsIso := by
    refine ⟨restrictChartHom hP.isQuasiProjVariety
      (none : Option M.ι) hne, ?_, ?_⟩
    · exact (Classical.choose_spec
        (isIso_restrictChartHom hP.isQuasiProjVariety
          (none : Option M.ι) hne)).2
    · exact (Classical.choose_spec
        (isIso_restrictChartHom hP.isQuasiProjVariety
          (none : Option M.ι) hne)).1
  have h₀ : DenseRange M.toProjectiveReindex.toFun :=
    M.toProjectiveReindex_isIso.bijective.2.denseRange
  have h₁ : DenseRange reindexToChart.toFun :=
    hReindexToChartIso.bijective.2.denseRange
  have h₂ : DenseRange chartToRestriction.toFun :=
    hChartToRestrictionIso.bijective.2.denseRange
  have h₃ : DenseRange chartInclusion.toFun :=
    (Variety.ofProjective hP).dense_range_inclHom_open
      (projectiveChartOpen hP.isQuasiProjVariety (none : Option M.ι))
      (projectiveChartOpen_nonempty hP.isQuasiProjVariety
        (none : Option M.ι) hne)
  change DenseRange
    (chartInclusion.toFun ∘ chartToRestriction.toFun ∘
      reindexToChart.toFun ∘ M.toProjectiveReindex.toFun)
  exact DenseRange.comp h₃
    (DenseRange.comp h₂ (DenseRange.comp h₁ h₀
      reindexToChart.continuous_toFun) chartToRestriction.continuous_toFun)
    chartInclusion.continuous_toFun

private theorem affineToProjectiveClosure_functionFieldAlgHom_surjective
    (M : AffineNormalizationModel htrdeg C) :
    Function.Surjective
      (M.affineToProjectiveClosure.functionFieldAlgHom
        (affineToProjectiveClosure_dense M)) := by
  classical
  let _ := M.finite_ι
  let hP := M.projectiveClosure_isProjVariety
  let hne := M.projectiveClosure_chart_nonempty
  let f₀ := M.toProjectiveReindex
  let f₁ : VarietyHom
      (Variety.ofQuasiAffine
        M.projectiveReindex_isAffineVariety.isQuasiAffineVariety)
      (chartTarget k (none : Option M.ι) hP.isQuasiProjVariety hne) :=
    Classical.choose
      (Hartshorne.projectiveClosureChartToAffineHom_isIso
        (none : Option M.ι) M.projectiveReindex_isAffineVariety)
  let f₂ : VarietyHom
      (chartTarget k (none : Option M.ι) hP.isQuasiProjVariety hne)
      ((Variety.ofProjective hP).restrict
        (projectiveChartOpen hP.isQuasiProjVariety (none : Option M.ι))
        (projectiveChartOpen_nonempty hP.isQuasiProjVariety
          (none : Option M.ι) hne)) :=
    Classical.choose
      (isIso_restrictChartHom hP.isQuasiProjVariety
        (none : Option M.ι) hne)
  let f₃ : VarietyHom
      ((Variety.ofProjective hP).restrict
        (projectiveChartOpen hP.isQuasiProjVariety (none : Option M.ι))
        (projectiveChartOpen_nonempty hP.isQuasiProjVariety
          (none : Option M.ι) hne))
      (Variety.ofProjective hP) :=
    (Variety.ofProjective hP).inclHom
      (projectiveChartOpen hP.isQuasiProjVariety (none : Option M.ι))
      (projectiveChartOpen_nonempty hP.isQuasiProjVariety
        (none : Option M.ι) hne)
  have hf₀Iso : f₀.IsIso := M.toProjectiveReindex_isIso
  have hf₁Iso : f₁.IsIso := by
    refine ⟨projectiveClosureChartToAffineHom
      (none : Option M.ι) M.projectiveReindex_isAffineVariety, ?_, ?_⟩
    · exact (Classical.choose_spec
        (Hartshorne.projectiveClosureChartToAffineHom_isIso
          (none : Option M.ι) M.projectiveReindex_isAffineVariety)).2
    · exact (Classical.choose_spec
        (Hartshorne.projectiveClosureChartToAffineHom_isIso
          (none : Option M.ι) M.projectiveReindex_isAffineVariety)).1
  have hf₂Iso : f₂.IsIso := by
    refine ⟨restrictChartHom hP.isQuasiProjVariety
      (none : Option M.ι) hne, ?_, ?_⟩
    · exact (Classical.choose_spec
        (isIso_restrictChartHom hP.isQuasiProjVariety
          (none : Option M.ι) hne)).2
    · exact (Classical.choose_spec
        (isIso_restrictChartHom hP.isQuasiProjVariety
          (none : Option M.ι) hne)).1
  have hf₀ : DenseRange f₀.toFun := hf₀Iso.bijective.2.denseRange
  have hf₁ : DenseRange f₁.toFun := hf₁Iso.bijective.2.denseRange
  have hf₂ : DenseRange f₂.toFun := hf₂Iso.bijective.2.denseRange
  have hf₃ : DenseRange f₃.toFun :=
    (Variety.ofProjective hP).dense_range_inclHom_open
      (projectiveChartOpen hP.isQuasiProjVariety (none : Option M.ι))
      (projectiveChartOpen_nonempty hP.isQuasiProjVariety
        (none : Option M.ι) hne)
  let f₁₀ := f₁.comp f₀
  let f₂₁₀ := f₂.comp f₁₀
  have hf₁₀ : DenseRange f₁₀.toFun := by
    change DenseRange (f₁.toFun ∘ f₀.toFun)
    exact DenseRange.comp hf₁ hf₀ f₁.continuous_toFun
  have hf₂₁₀ : DenseRange f₂₁₀.toFun := by
    change DenseRange (f₂.toFun ∘ f₁₀.toFun)
    exact DenseRange.comp hf₂ hf₁₀ f₂.continuous_toFun
  have hf₃₂₁₀ : DenseRange (f₃.comp f₂₁₀).toFun := by
    change DenseRange (f₃.toFun ∘ f₂₁₀.toFun)
    exact DenseRange.comp hf₃ hf₂₁₀ f₃.continuous_toFun
  have hf₀Pull : Function.Bijective (f₀.functionFieldAlgHom hf₀) :=
    f₀.bijective_functionFieldHom_of_isIso hf₀Iso hf₀
  have hf₁Pull : Function.Bijective (f₁.functionFieldAlgHom hf₁) :=
    f₁.bijective_functionFieldHom_of_isIso hf₁Iso hf₁
  have hf₂Pull : Function.Bijective (f₂.functionFieldAlgHom hf₂) :=
    f₂.bijective_functionFieldHom_of_isIso hf₂Iso hf₂
  have hf₃Pull : Function.Bijective (f₃.functionFieldAlgHom hf₃) :=
    (RationalMapFunctionField.openFunctionFieldAlgEquiv
      (Variety.ofProjective hP)
      (projectiveChartOpen hP.isQuasiProjVariety (none : Option M.ι))
      (projectiveChartOpen_nonempty hP.isQuasiProjVariety
        (none : Option M.ι) hne)).bijective
  have hf₁₀Pull : Function.Surjective
      (f₁₀.functionFieldAlgHom hf₁₀) := by
    rw [VarietyHom.functionFieldAlgHom_comp' f₁ f₀ hf₁ hf₀ hf₁₀]
    exact hf₀Pull.2.comp hf₁Pull.2
  have hf₂₁₀Pull : Function.Surjective
      (f₂₁₀.functionFieldAlgHom hf₂₁₀) := by
    rw [VarietyHom.functionFieldAlgHom_comp' f₂ f₁₀ hf₂ hf₁₀ hf₂₁₀]
    exact hf₁₀Pull.comp hf₂Pull.2
  have hf₃₂₁₀Pull : Function.Surjective
      ((f₃.comp f₂₁₀).functionFieldAlgHom hf₃₂₁₀) := by
    rw [VarietyHom.functionFieldAlgHom_comp' f₃ f₂₁₀ hf₃ hf₂₁₀ hf₃₂₁₀]
    exact hf₂₁₀Pull.comp hf₃Pull.2
  change Function.Surjective
    ((f₃.comp (f₂.comp (f₁.comp f₀))).functionFieldAlgHom _)
  exact hf₃₂₁₀Pull

end AffineNormalizationModel

end ValuationSpace

/-- **Hartshorne I.6, function-field comparison in the proof of Theorem 6.9.**
The dense morphism from the abstract nonsingular curve to the projective
diagonal model induces a bijection on function fields. -/
theorem projectiveDiagonal_functionFieldAlgHom_bijective
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    [IsAlgClosed k] [Algebra.EssFiniteType k K]
    {htrdeg : Algebra.trdeg k K = 1}
    (D : ValuationSpace.ProjectiveDiagonalModel htrdeg) :
    Function.Bijective (D.φ.functionFieldAlgHom D.φ_dense) := by
  have hEmbeddingDense : DenseRange D.M₀.embedding.toFun := by
    change Dense (Set.range D.M₀.embedding.toFun)
    rw [D.M₀.range_embedding_eq_imageOpen]
    exact Variety.dense_of_isOpen_of_nonempty
      D.M₀.imageOpen.isOpen D.M₀.imageOpen_nonempty
  have hAffineDense : DenseRange D.M₀.affineToProjectiveClosure.toFun :=
    ValuationSpace.AffineNormalizationModel.affineToProjectiveClosure_dense D.M₀
  have hΦ₀compDense : DenseRange (D.Φ₀.comp D.M₀.embedding).toFun := by
    rw [D.extension₀]
    exact hAffineDense
  have hΦ₀Dense : DenseRange D.Φ₀.toFun :=
    Dense.mono (by
      rintro _ ⟨x, rfl⟩
      exact ⟨D.M₀.embedding x, rfl⟩) hΦ₀compDense
  have hProjectionCompDense : DenseRange
      (D.projection₀.comp D.φ).toFun := by
    rw [D.projection₀_comp_φ]
    exact hΦ₀Dense
  have hProjectionDense : DenseRange D.projection₀.toFun :=
    Dense.mono (by
      rintro _ ⟨x, rfl⟩
      exact ⟨D.φ x, rfl⟩) hProjectionCompDense
  have hExtensionPullback :
      (D.M₀.embedding.functionFieldAlgHom hEmbeddingDense).comp
          (D.Φ₀.functionFieldAlgHom hΦ₀Dense) =
        D.M₀.affineToProjectiveClosure.functionFieldAlgHom hAffineDense := by
    calc
      _ = (D.Φ₀.comp D.M₀.embedding).functionFieldAlgHom hΦ₀compDense :=
        (VarietyHom.functionFieldAlgHom_comp' D.Φ₀ D.M₀.embedding
          hΦ₀Dense hEmbeddingDense hΦ₀compDense).symm
      _ = _ := VarietyHom.functionFieldAlgHom_congr' D.extension₀
        hΦ₀compDense hAffineDense
  have hΦ₀Surjective : Function.Surjective
      (D.Φ₀.functionFieldAlgHom hΦ₀Dense) := by
    intro q
    obtain ⟨r, hr⟩ :=
      ValuationSpace.AffineNormalizationModel.affineToProjectiveClosure_functionFieldAlgHom_surjective
        D.M₀
        (D.M₀.embedding.functionFieldAlgHom hEmbeddingDense q)
    refine ⟨r, ?_⟩
    apply (D.M₀.embedding.functionFieldAlgHom hEmbeddingDense).toRingHom.injective
    calc
      D.M₀.embedding.functionFieldAlgHom hEmbeddingDense
          (D.Φ₀.functionFieldAlgHom hΦ₀Dense r) =
          D.M₀.affineToProjectiveClosure.functionFieldAlgHom hAffineDense r :=
        AlgHom.congr_fun hExtensionPullback r
      _ = D.M₀.embedding.functionFieldAlgHom hEmbeddingDense q := hr
  have hProjectionPullback :
      (D.φ.functionFieldAlgHom D.φ_dense).comp
          (D.projection₀.functionFieldAlgHom hProjectionDense) =
        D.Φ₀.functionFieldAlgHom hΦ₀Dense := by
    calc
      _ = (D.projection₀.comp D.φ).functionFieldAlgHom
          hProjectionCompDense :=
        (VarietyHom.functionFieldAlgHom_comp' D.projection₀ D.φ
          hProjectionDense D.φ_dense hProjectionCompDense).symm
      _ = _ := VarietyHom.functionFieldAlgHom_congr'
        D.projection₀_comp_φ hProjectionCompDense hΦ₀Dense
  constructor
  · exact (D.φ.functionFieldAlgHom D.φ_dense).toRingHom.injective
  · intro q
    obtain ⟨r, hr⟩ := hΦ₀Surjective q
    refine ⟨D.projection₀.functionFieldAlgHom hProjectionDense r, ?_⟩
    calc
      D.φ.functionFieldAlgHom D.φ_dense
          (D.projection₀.functionFieldAlgHom hProjectionDense r) =
          D.Φ₀.functionFieldAlgHom hΦ₀Dense r :=
        AlgHom.congr_fun hProjectionPullback r
      _ = q := hr

end

end Hartshorne

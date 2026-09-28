/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Curve.ProjectiveModelFunctionField
import Hartshorne.Morphism.DominantLocalRing

/-!
# Local rings of the projective diagonal model

Hartshorne, *Algebraic Geometry*, I.6, proof of Theorem 6.9 (p. 45).

The local ring of the diagonal image at `φ(P)`, transported into the original
function field `K`, is exactly the valuation ring represented by `P`.  The
proof follows Hartshorne's sandwich through whichever of the two affine charts
contains `P`.
-/

namespace Hartshorne

open Set TopologicalSpace
open scoped Hartshorne

noncomputable section

universe u

private theorem VarietyHom.bijective_localRingHom_comp'
    {k : Type u} [Field k] {X Y Z : Variety k}
    (g : VarietyHom Y Z) (f : VarietyHom X Y) (P : X.carrier)
    (hg : Function.Bijective (g.localRingHom (f P)))
    (hf : Function.Bijective (f.localRingHom P)) :
    Function.Bijective ((g.comp f).localRingHom P) := by
  rw [VarietyHom.localRingHom_comp]
  exact hf.comp hg

namespace ValuationSpace

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable [IsAlgClosed k] [Algebra.EssFiniteType k K]

private theorem valuationSpace_univ_nonempty
    (htrdeg : Algebra.trdeg k K = 1) :
    ((⊤ : Opens (ValuationSpace k K)) : Set (ValuationSpace k K)).Nonempty := by
  let _ : Infinite (FunctionFieldDVR k K) :=
    FunctionFieldDVR.infinite_of_trdeg_eq_one htrdeg
  exact Set.univ_nonempty

namespace AffineNormalizationModel

variable {htrdeg : Algebra.trdeg k K = 1}
variable {C : SeparableNormalizationChart k K}

/-- The affine normalization chart and its projective closure have isomorphic
local rings at corresponding points. -/
private theorem affineToProjectiveClosure_localRingHom_bijective
    (M : AffineNormalizationModel htrdeg C)
    (Q : (Variety.ofQuasiAffine
      M.isAffineVariety.isQuasiAffineVariety).carrier) :
    Function.Bijective (M.affineToProjectiveClosure.localRingHom Q) := by
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
  have hf₀ : Function.Bijective (f₀.localRingHom Q) :=
    f₀.bijective_localRingHom_of_isIso hf₀Iso Q
  have hf₁ : Function.Bijective (f₁.localRingHom (f₀ Q)) :=
    f₁.bijective_localRingHom_of_isIso hf₁Iso (f₀ Q)
  have hf₂ : Function.Bijective (f₂.localRingHom (f₁ (f₀ Q))) :=
    f₂.bijective_localRingHom_of_isIso hf₂Iso (f₁ (f₀ Q))
  have hf₃ : Function.Bijective
      (f₃.localRingHom (f₂ (f₁ (f₀ Q)))) :=
    Variety.bijective_localRingHom_inclHom (f₂ (f₁ (f₀ Q)))
  have hf₁₀ : Function.Bijective ((f₁.comp f₀).localRingHom Q) :=
    VarietyHom.bijective_localRingHom_comp' f₁ f₀ Q hf₁ hf₀
  have hf₂₁₀ : Function.Bijective
      ((f₂.comp (f₁.comp f₀)).localRingHom Q) :=
    VarietyHom.bijective_localRingHom_comp' f₂ (f₁.comp f₀) Q hf₂ hf₁₀
  have hf₃₂₁₀ : Function.Bijective
      ((f₃.comp (f₂.comp (f₁.comp f₀))).localRingHom Q) :=
    VarietyHom.bijective_localRingHom_comp'
      f₃ (f₂.comp (f₁.comp f₀)) Q hf₃ hf₂₁₀
  change Function.Bijective
    ((f₃.comp (f₂.comp (f₁.comp f₀))).localRingHom Q)
  exact hf₃₂₁₀

/-- On a point belonging to an affine normalization chart, its extension to
the projective closure induces a surjection on local rings. -/
private theorem projectiveExtension_localRingHom_surjective
    (M : AffineNormalizationModel htrdeg C)
    (Φ : VarietyHom (abstractNonsingularCurveOfFunctionField htrdeg)
      (Variety.ofProjective M.projectiveClosure_isProjVariety))
    (hΦ : Φ.comp M.embedding = M.affineToProjectiveClosure)
    (P : (abstractNonsingularCurveOfFunctionField htrdeg).carrier)
    (hP : P ∈ M.imageOpen) :
    Function.Surjective (Φ.localRingHom P) := by
  have hPrange : P ∈ Set.range M.embedding.toFun := by
    rw [M.range_embedding_eq_imageOpen]
    exact hP
  obtain ⟨Q, hQ⟩ := hPrange
  subst P
  have hEmbeddingDense : DenseRange M.embedding.toFun := by
    change Dense (Set.range M.embedding.toFun)
    rw [M.range_embedding_eq_imageOpen]
    exact Variety.dense_of_isOpen_of_nonempty
      M.imageOpen.isOpen M.imageOpen_nonempty
  have hEmbeddingInjective : Function.Injective (M.embedding.localRingHom Q) :=
    M.embedding.injective_localRingHom_of_denseRange hEmbeddingDense Q
  have hComposite : Function.Bijective
      ((Φ.comp M.embedding).localRingHom Q) := by
    rw [hΦ]
    exact M.affineToProjectiveClosure_localRingHom_bijective Q
  have hComposite' : Function.Bijective
      ((M.embedding.localRingHom Q).comp
        (Φ.localRingHom (M.embedding Q))) := by
    rw [← VarietyHom.localRingHom_comp]
    exact hComposite
  intro b
  obtain ⟨a, ha⟩ := hComposite'.2 (M.embedding.localRingHom Q b)
  refine ⟨a, ?_⟩
  apply hEmbeddingInjective
  exact ha

end AffineNormalizationModel

end ValuationSpace

/-- The exact function-field identification used for the projective diagonal
model: pull back along its packaged dense morphism, then use the canonical
identification of the abstract valuation curve's function field with `K`. -/
noncomputable def projectiveDiagonalFunctionFieldAlgEquiv
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    [IsAlgClosed k] [Algebra.EssFiniteType k K]
    {htrdeg : Algebra.trdeg k K = 1}
    (D : ValuationSpace.ProjectiveDiagonalModel htrdeg) :
    (Variety.ofProjective D.isProjVariety).FunctionField ≃ₐ[k] K :=
  (AlgEquiv.ofBijective
    (D.φ.functionFieldAlgHom D.φ_dense)
    (projectiveDiagonal_functionFieldAlgHom_bijective D)).trans
      (ValuationSpace.abstractNonsingularCurveFunctionFieldAlgEquiv
        htrdeg (⊤ : Opens (ValuationSpace k K))
        (ValuationSpace.valuationSpace_univ_nonempty htrdeg)).symm

/-- The local ring of the diagonal model, embedded into the fixed ambient
function field through the packaged function-field identification. -/
noncomputable def projectiveDiagonalLocalToAmbientAlgHom
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    [IsAlgClosed k] [Algebra.EssFiniteType k K]
    {htrdeg : Algebra.trdeg k K = 1}
    (D : ValuationSpace.ProjectiveDiagonalModel htrdeg)
    (P : (ValuationSpace.abstractNonsingularCurveOfFunctionField
      htrdeg).carrier) :
    (Variety.ofProjective D.isProjVariety).LocalRingAt (D.φ P) →ₐ[k] K :=
  (projectiveDiagonalFunctionFieldAlgEquiv D).toAlgHom.comp
    ((Variety.ofProjective D.isProjVariety).localToFunctionFieldAlgHom (D.φ P))

private theorem projectiveDiagonalLocalToAmbientAlgHom_apply
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    [IsAlgClosed k] [Algebra.EssFiniteType k K]
    {htrdeg : Algebra.trdeg k K = 1}
    (D : ValuationSpace.ProjectiveDiagonalModel htrdeg)
    (P : (ValuationSpace.abstractNonsingularCurveOfFunctionField
      htrdeg).carrier)
    (a : (Variety.ofProjective D.isProjVariety).LocalRingAt (D.φ P)) :
    projectiveDiagonalLocalToAmbientAlgHom D P a =
      (ValuationSpace.abstractNonsingularCurveFunctionFieldAlgEquiv
        htrdeg (⊤ : Opens (ValuationSpace k K))
        (ValuationSpace.valuationSpace_univ_nonempty htrdeg)).symm
          ((ValuationSpace.abstractNonsingularCurveOfFunctionField htrdeg).localToFunctionFieldAlgHom
            P (D.φ.localRingHom P a)) := by
  change (ValuationSpace.abstractNonsingularCurveFunctionFieldAlgEquiv
      htrdeg (⊤ : Opens (ValuationSpace k K))
      (ValuationSpace.valuationSpace_univ_nonempty htrdeg)).symm
        (D.φ.functionFieldAlgHom D.φ_dense
          ((Variety.ofProjective D.isProjVariety).localToFunctionFieldAlgHom
            (D.φ P) a)) = _
  congr 1
  exact D.φ.functionFieldHom_localToFunctionFieldAlgHom D.φ_dense P a

/-- The projective diagonal induces an isomorphism on local rings at every
point of the abstract valuation curve. -/
theorem projectiveDiagonal_localRingHom_bijective
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    [IsAlgClosed k] [Algebra.EssFiniteType k K]
    {htrdeg : Algebra.trdeg k K = 1}
    (D : ValuationSpace.ProjectiveDiagonalModel htrdeg)
    (P : (ValuationSpace.abstractNonsingularCurveOfFunctionField
      htrdeg).carrier) :
    Function.Bijective (D.φ.localRingHom P) := by
  have hSurjective : Function.Surjective (D.φ.localRingHom P) := by
    have hPcover :
        P ∈ (D.M₀.imageOpen : Set
          (ValuationSpace.abstractNonsingularCurveOfFunctionField
            htrdeg).carrier) ∪
          (D.M₁.imageOpen : Set
            (ValuationSpace.abstractNonsingularCurveOfFunctionField
              htrdeg).carrier) := by
      rw [D.cover]
      trivial
    rcases hPcover with hP₀ | hP₁
    · have hΦ : Function.Surjective (D.Φ₀.localRingHom P) :=
        D.M₀.projectiveExtension_localRingHom_surjective
          D.Φ₀ D.extension₀ P hP₀
      have hcomp : Function.Surjective
          ((D.projection₀.comp D.φ).localRingHom P) := by
        rw [D.projection₀_comp_φ]
        exact hΦ
      have hcomp' : Function.Surjective
          ((D.φ.localRingHom P).comp
            (D.projection₀.localRingHom (D.φ P))) := by
        rw [← VarietyHom.localRingHom_comp]
        exact hcomp
      intro b
      obtain ⟨a, ha⟩ := hcomp' b
      refine ⟨D.projection₀.localRingHom (D.φ P) a, ?_⟩
      exact ha
    · have hΦ : Function.Surjective (D.Φ₁.localRingHom P) :=
        D.M₁.projectiveExtension_localRingHom_surjective
          D.Φ₁ D.extension₁ P hP₁
      have hcomp : Function.Surjective
          ((D.projection₁.comp D.φ).localRingHom P) := by
        rw [D.projection₁_comp_φ]
        exact hΦ
      have hcomp' : Function.Surjective
          ((D.φ.localRingHom P).comp
            (D.projection₁.localRingHom (D.φ P))) := by
        rw [← VarietyHom.localRingHom_comp]
        exact hcomp
      intro b
      obtain ⟨a, ha⟩ := hcomp' b
      refine ⟨D.projection₁.localRingHom (D.φ P) a, ?_⟩
      exact ha
  exact ⟨D.φ.injective_localRingHom_of_denseRange D.φ_dense P, hSurjective⟩

/-- **Hartshorne I.6, local-ring comparison in the proof of Theorem 6.9.**
Inside the fixed ambient function field `K`, the image of the local ring at
`φ(P)` is exactly the valuation subring represented by `P`. -/
theorem projectiveDiagonal_localRingRange_eq
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    [IsAlgClosed k] [Algebra.EssFiniteType k K]
    {htrdeg : Algebra.trdeg k K = 1}
    (D : ValuationSpace.ProjectiveDiagonalModel htrdeg)
    (P : (ValuationSpace.abstractNonsingularCurveOfFunctionField
      htrdeg).carrier) :
    (projectiveDiagonalLocalToAmbientAlgHom D P).range.toSubring =
      ((ValuationSpace.of k K).symm P.1).toValuationSubring.toSubring := by
  let C := ValuationSpace.abstractNonsingularCurveOfFunctionField htrdeg
  let eC :=
    (ValuationSpace.abstractNonsingularCurveFunctionFieldAlgEquiv
      htrdeg (⊤ : Opens (ValuationSpace k K))
      (ValuationSpace.valuationSpace_univ_nonempty htrdeg)).symm
  let toK : C.LocalRingAt P →ₐ[k] K :=
    eC.toAlgHom.comp (C.localToFunctionFieldAlgHom P)
  have hRanges :
      (projectiveDiagonalLocalToAmbientAlgHom D P).range.toSubring =
        toK.range.toSubring := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨D.φ.localRingHom P a, ?_⟩
      change toK (D.φ.localRingHom P a) =
        projectiveDiagonalLocalToAmbientAlgHom D P a
      exact (projectiveDiagonalLocalToAmbientAlgHom_apply D P a).symm
    · rintro ⟨b, rfl⟩
      obtain ⟨a, ha⟩ :=
        (projectiveDiagonal_localRingHom_bijective D P).2 b
      refine ⟨a, ?_⟩
      change projectiveDiagonalLocalToAmbientAlgHom D P a = toK b
      rw [projectiveDiagonalLocalToAmbientAlgHom_apply, ha]
      rfl
  rw [hRanges]
  ext x
  let eLocal : C.LocalRingAt P ≃ₐ[k]
      ((ValuationSpace.of k K).symm P.1).toValuationSubring :=
    ValuationSpace.abstractNonsingularCurveLocalRingAlgEquiv
      htrdeg (⊤ : Opens (ValuationSpace k K))
      (ValuationSpace.valuationSpace_univ_nonempty htrdeg) P
  have hLocalCoe (a : C.LocalRingAt P) :
      (((eLocal a :
        ((ValuationSpace.of k K).symm P.1).toValuationSubring) : K)) =
        toK a := by
    exact ValuationSpace.abstractNonsingularCurveLocalRingAlgEquiv_coe
      htrdeg (⊤ : Opens (ValuationSpace k K))
      (ValuationSpace.valuationSpace_univ_nonempty htrdeg) P a
  constructor
  · rintro ⟨a, rfl⟩
    change toK a ∈
      ((ValuationSpace.of k K).symm P.1).toValuationSubring
    rw [← hLocalCoe]
    exact (eLocal a).2
  · intro hx
    let z : ((ValuationSpace.of k K).symm P.1).toValuationSubring := ⟨x, hx⟩
    obtain ⟨a, ha⟩ := eLocal.surjective z
    refine ⟨a, ?_⟩
    change toK a = x
    rw [← hLocalCoe]
    exact congrArg Subtype.val ha

end

end Hartshorne

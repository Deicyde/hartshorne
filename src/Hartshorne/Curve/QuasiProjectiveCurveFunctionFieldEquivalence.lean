/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Curve.Categories
import Hartshorne.Rational.ProjectiveClosure

/-!
# Quasi-projective curves and one-dimensional function fields

Hartshorne, *Algebraic Geometry*, I.6, Corollary 6.12 (pp. 45--46).

The function-field construction gives a contravariant equivalence from
quasi-projective curves with dominant rational maps to one-dimensional
function fields.  Essential surjectivity is obtained by realizing a field as
the function field of an affine variety and then taking its projective closure.

## Main definition

* `Hartshorne.quasiProjectiveCurveFunctionFieldEquivalence`
-/

namespace Hartshorne

open CategoryTheory MvPolynomial TopologicalSpace

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

namespace QuasiProjectiveCurveCat

/-! ## Reindexing affine coordinates into a projective chart -/

private def reindexCoordinates {σ τ : Type u} (e : σ ≃ τ) (x : σ → k) : τ → k :=
  x ∘ e.symm

private def inverseReindexCoordinates {σ τ : Type u} (e : σ ≃ τ)
    (y : τ → k) : σ → k :=
  y ∘ e

/-- The non-homogenizing coordinates of `Option σ` are canonically indexed by
`σ`. -/
private def optionChartEquiv (σ : Type u) :
    σ ≃ {j : Option σ // j ≠ none} where
  toFun i := ⟨some i, by simp⟩
  invFun j := by
    rcases j with ⟨_ | i, h⟩
    · exact (h rfl).elim
    · exact i
  left_inv _ := rfl
  right_inv j := by
    rcases j with ⟨_ | i, h⟩
    · exact (h rfl).elim
    · rfl

omit [Field k] [IsAlgClosed k] in
@[simp]
private theorem inverseReindexCoordinates_reindexCoordinates
    {σ τ : Type u} (e : σ ≃ τ) (x : σ → k) :
    inverseReindexCoordinates e (reindexCoordinates e x) = x := by
  funext i
  simp [inverseReindexCoordinates, reindexCoordinates]

omit [Field k] [IsAlgClosed k] in
@[simp]
private theorem reindexCoordinates_inverseReindexCoordinates
    {σ τ : Type u} (e : σ ≃ τ) (y : τ → k) :
    reindexCoordinates e (inverseReindexCoordinates e y) = y := by
  funext i
  simp [inverseReindexCoordinates, reindexCoordinates]

omit [IsAlgClosed k] in
private theorem continuous_reindexCoordinates {σ τ : Type u} (e : σ ≃ τ) :
    Continuous (reindexCoordinates (k := k) e) := by
  rw [continuous_iff_isClosed]
  intro C hC
  obtain ⟨T, rfl⟩ := isClosed_iff_isAlgebraicSet.1 hC
  have heq :
      reindexCoordinates (k := k) e ⁻¹' zeroSet T =
        zeroSet (rename e.symm '' T) := by
    ext x
    simp only [Set.mem_preimage, mem_zeroSet_iff, Set.mem_image]
    constructor
    · intro hx p hp
      obtain ⟨q, hq, rfl⟩ := hp
      rw [MvPolynomial.eval_rename]
      simpa [reindexCoordinates, Function.comp_def] using hx q hq
    · intro hx q hq
      have h := hx (rename e.symm q) ⟨q, hq, rfl⟩
      rw [MvPolynomial.eval_rename] at h
      simpa [reindexCoordinates, Function.comp_def] using h
  rw [heq]
  exact isClosed_zeroSet _

omit [IsAlgClosed k] in
private theorem continuous_inverseReindexCoordinates {σ τ : Type u}
    (e : σ ≃ τ) :
    Continuous (inverseReindexCoordinates (k := k) e) := by
  rw [continuous_iff_isClosed]
  intro C hC
  obtain ⟨T, rfl⟩ := isClosed_iff_isAlgebraicSet.1 hC
  have heq :
      inverseReindexCoordinates (k := k) e ⁻¹' zeroSet T =
        zeroSet (rename e '' T) := by
    ext y
    simp only [Set.mem_preimage, mem_zeroSet_iff, Set.mem_image]
    constructor
    · intro hy p hp
      obtain ⟨q, hq, rfl⟩ := hp
      rw [MvPolynomial.eval_rename]
      simpa [inverseReindexCoordinates, Function.comp_def] using hy q hq
    · intro hy q hq
      have h := hy (rename e q) ⟨q, hq, rfl⟩
      rw [MvPolynomial.eval_rename] at h
      simpa [inverseReindexCoordinates, Function.comp_def] using h
  rw [heq]
  exact isClosed_zeroSet _

private def reindexAffineSet {σ τ : Type u} (e : σ ≃ τ)
    (Y : Set (σ → k)) : Set (τ → k) :=
  reindexCoordinates e '' Y

omit [Field k] [IsAlgClosed k] in
private theorem reindexAffineSet_eq_preimage {σ τ : Type u} (e : σ ≃ τ)
    (Y : Set (σ → k)) :
    reindexAffineSet (k := k) e Y =
      inverseReindexCoordinates (k := k) e ⁻¹' Y := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro hy
    exact ⟨inverseReindexCoordinates e y, hy,
      reindexCoordinates_inverseReindexCoordinates e y⟩

omit [IsAlgClosed k] in
private theorem reindexAffineSet_isAffineVariety {σ τ : Type u}
    (e : σ ≃ τ) {Y : Set (σ → k)} (hY : IsAffineVariety Y) :
    IsAffineVariety (reindexAffineSet (k := k) e Y) := by
  refine ⟨hY.isIrreducible.image _
    (continuous_reindexCoordinates (k := k) e).continuousOn, ?_⟩
  rw [reindexAffineSet_eq_preimage]
  exact hY.isClosed.preimage (continuous_inverseReindexCoordinates (k := k) e)

omit [IsAlgClosed k] in
private theorem affineCoordinate_isGlobalRegular
    {σ : Type u} [Finite σ] {Y : Set (σ → k)}
    (hY : IsQuasiAffineVariety Y) (i : σ) :
    (Variety.ofQuasiAffine hY).IsGlobalRegular (fun y ↦ y.1 i) := by
  intro _
  exact ⟨Set.univ, isOpen_univ, Set.mem_univ _, X i, 1, by simp, by simp⟩

private def reindexToOriginalFun {σ τ : Type u} (e : σ ≃ τ)
    {Y : Set (σ → k)} : reindexAffineSet (k := k) e Y → Y :=
  fun y ↦ ⟨inverseReindexCoordinates e y.1, by
    change y.1 ∈ inverseReindexCoordinates (k := k) e ⁻¹' Y
    rw [← reindexAffineSet_eq_preimage]
    exact y.2⟩

private def originalToReindexFun {σ τ : Type u} (e : σ ≃ τ)
    {Y : Set (σ → k)} : Y → reindexAffineSet (k := k) e Y :=
  fun x ↦ ⟨reindexCoordinates e x.1, ⟨x.1, x.2, rfl⟩⟩

private noncomputable def reindexToOriginalHom
    {σ τ : Type u} [Finite σ] [Finite τ] (e : σ ≃ τ)
    {Y : Set (σ → k)} (hY : IsAffineVariety Y) :
    VarietyHom
      (Variety.ofQuasiAffine
        (reindexAffineSet_isAffineVariety (k := k) e hY).isQuasiAffineVariety)
      (Variety.ofQuasiAffine hY.isQuasiAffineVariety) :=
  VarietyHom.ofCoords hY.isQuasiAffineVariety
    (reindexToOriginalFun e) fun i ↦ by
      simpa [reindexToOriginalFun, inverseReindexCoordinates] using
        affineCoordinate_isGlobalRegular
          (reindexAffineSet_isAffineVariety
            (k := k) e hY).isQuasiAffineVariety (e i)

private noncomputable def originalToReindexHom
    {σ τ : Type u} [Finite σ] [Finite τ] (e : σ ≃ τ)
    {Y : Set (σ → k)} (hY : IsAffineVariety Y) :
    VarietyHom
      (Variety.ofQuasiAffine hY.isQuasiAffineVariety)
      (Variety.ofQuasiAffine
        (reindexAffineSet_isAffineVariety (k := k) e hY).isQuasiAffineVariety) :=
  VarietyHom.ofCoords
    (reindexAffineSet_isAffineVariety (k := k) e hY).isQuasiAffineVariety
    (originalToReindexFun e) fun j ↦ by
      simpa [originalToReindexFun, reindexCoordinates] using
        affineCoordinate_isGlobalRegular hY.isQuasiAffineVariety (e.symm j)

omit [IsAlgClosed k] in
private theorem reindexToOriginalHom_apply
    {σ τ : Type u} [Finite σ] [Finite τ] (e : σ ≃ τ)
    {Y : Set (σ → k)} (hY : IsAffineVariety Y)
    (y : (Variety.ofQuasiAffine
      (reindexAffineSet_isAffineVariety (k := k) e hY).isQuasiAffineVariety).carrier) :
    (reindexToOriginalHom (k := k) e hY y).1 =
      inverseReindexCoordinates e y.1 := by
  have hfun : (reindexToOriginalHom (k := k) e hY).toFun =
      reindexToOriginalFun e := by
    unfold reindexToOriginalHom
    exact VarietyHom.ofCoords_toFun _ _ _
  exact congrArg Subtype.val (congrFun hfun y)

omit [IsAlgClosed k] in
private theorem originalToReindexHom_apply
    {σ τ : Type u} [Finite σ] [Finite τ] (e : σ ≃ τ)
    {Y : Set (σ → k)} (hY : IsAffineVariety Y)
    (x : (Variety.ofQuasiAffine hY.isQuasiAffineVariety).carrier) :
    (originalToReindexHom (k := k) e hY x).1 = reindexCoordinates e x.1 := by
  have hfun : (originalToReindexHom (k := k) e hY).toFun =
      originalToReindexFun e := by
    unfold originalToReindexHom
    exact VarietyHom.ofCoords_toFun _ _ _
  exact congrArg Subtype.val (congrFun hfun x)

omit [IsAlgClosed k] in
private theorem reindexToOriginalHom_isIso
    {σ τ : Type u} [Finite σ] [Finite τ] (e : σ ≃ τ)
    {Y : Set (σ → k)} (hY : IsAffineVariety Y) :
    (reindexToOriginalHom (k := k) e hY).IsIso := by
  refine ⟨originalToReindexHom (k := k) e hY, ?_, ?_⟩
  · apply VarietyHom.ext
    funext y
    apply Subtype.ext
    rw [VarietyHom.comp_apply, originalToReindexHom_apply,
      reindexToOriginalHom_apply,
      reindexCoordinates_inverseReindexCoordinates]
    rfl
  · apply VarietyHom.ext
    funext x
    apply Subtype.ext
    rw [VarietyHom.comp_apply, reindexToOriginalHom_apply,
      originalToReindexHom_apply,
      inverseReindexCoordinates_reindexCoordinates]
    rfl

/-! ## The function-field functor -/

/-- The function field of a quasi-projective curve, regarded as a
one-dimensional function field. -/
noncomputable def functionFieldObj (X : QuasiProjectiveCurveCat k) :
    OneDimensionalFunctionFieldCat k where
  obj := CommAlgCat.of k X.toVariety.FunctionField
  property := by
    let hX := Variety.hasAffineOpenBasis_ofQuasiProjective X.isQuasiProjective
    exact ⟨Variety.isField_functionField,
      RationalMapFunctionField.essFiniteType_functionField hX,
      hX.isCurve_iff_trdeg_eq_one.mp X.isCurve⟩

/-- The canonical contravariant function-field functor on quasi-projective
curves. -/
noncomputable def functionFieldFunctor :
    (QuasiProjectiveCurveCat k)ᵒᵖ ⥤ OneDimensionalFunctionFieldCat k where
  obj X := functionFieldObj X.unop
  map f := ObjectProperty.homMk
    (CommAlgCat.ofHom (DominantRatMap.functionFieldAlgHom f.unop))
  map_id X := by
    apply ObjectProperty.hom_ext
    show CommAlgCat.ofHom
      (DominantRatMap.functionFieldAlgHom (DominantRatMap.id
        X.unop.toVariety X.unop.isSeparated)) = _
    rw [DominantRatMap.functionFieldAlgHom_id]
    rfl
  map_comp f g := by
    apply ObjectProperty.hom_ext
    show CommAlgCat.ofHom
      (DominantRatMap.functionFieldAlgHom
        (DominantRatMap.comp f.unop g.unop)) = _
    rw [DominantRatMap.functionFieldAlgHom_comp]
    rfl

instance faithful_functionFieldFunctor :
    (functionFieldFunctor (k := k)).Faithful where
  map_injective {X Y} {f g} h := by
    apply Quiver.Hom.unop_inj
    apply (RationalMapFunctionField.dominantRatMapEquivFunctionFieldAlgHom
      X.unop.isSeparated
      (Variety.hasAffineOpenBasis_ofQuasiProjective
        X.unop.isQuasiProjective)).injective
    exact congrArg
      (fun m => CommAlgCat.Hom.hom (InducedCategory.Hom.hom m)) h

instance full_functionFieldFunctor :
    (functionFieldFunctor (k := k)).Full where
  map_surjective {X Y} ψ := by
    let e := RationalMapFunctionField.dominantRatMapEquivFunctionFieldAlgHom
      (X := Y.unop.toVariety) (Y := X.unop.toVariety)
      X.unop.isSeparated
      (Variety.hasAffineOpenBasis_ofQuasiProjective
        X.unop.isQuasiProjective)
    let θ := CommAlgCat.Hom.hom (InducedCategory.Hom.hom ψ)
    let q : Y.unop ⟶ X.unop := e.symm θ
    refine ⟨q.op, ?_⟩
    apply ObjectProperty.hom_ext
    show CommAlgCat.ofHom (DominantRatMap.functionFieldAlgHom q) = _
    have hq : DominantRatMap.functionFieldAlgHom q = θ := e.apply_symm_apply θ
    rw [hq]
    rfl

/-- Every one-dimensional function field is the function field of a
quasi-projective curve. -/
theorem exists_quasiProjectiveCurve_functionField_algEquiv
    (K : Type u) [Field K] [Algebra k K] [Algebra.EssFiniteType k K]
    (htrdeg : Algebra.trdeg k K = 1) :
    ∃ X : QuasiProjectiveCurveCat k,
      Nonempty (X.toVariety.FunctionField ≃ₐ[k] K) := by
  classical
  let B := Algebra.EssFiniteType.subalgebra k K
  let _ : Algebra.FiniteType k B := inferInstance
  let _ : IsDomain B := inferInstance
  obtain ⟨τ, hτ, Z, hZ, ⟨eB⟩⟩ :=
    RationalMapFunctionField.exists_isAffineVariety_coordinateRing_equiv_sameUniverse
      (k := k) (B := B)
  let _ : Finite τ := hτ
  let _ : IsDomain (coordinateRing Z) := isDomain_coordinateRing hZ
  let _ : IsFractionRing (coordinateRing Z)
      (FunctionField hZ.isIrreducible) :=
    isFractionRing_functionField hZ.isIrreducible
  have hM : Algebra.EssFiniteType.submonoid k K = nonZeroDivisors B := by
    ext x
    simp only [Algebra.EssFiniteType.submonoid, Submonoid.mem_comap,
      IsUnit.mem_submonoid_iff]
    rw [mem_nonZeroDivisors_iff_ne_zero]
    rw [show IsUnit (algebraMap B K x) ↔ algebraMap B K x ≠ 0 from
      isUnit_iff_ne_zero]
    exact map_ne_zero_iff _ Subtype.val_injective
  have hfrac : IsFractionRing B K := by
    change IsLocalization (nonZeroDivisors B) K
    rw [← hM]
    infer_instance
  let _ : IsFractionRing B K := hfrac
  let efrac : FunctionField hZ.isIrreducible ≃ₐ[k] K :=
    IsFractionRing.algEquivOfAlgEquiv eB
  let eZK : (Variety.ofQuasiAffine hZ.isQuasiAffineVariety).FunctionField ≃ₐ[k] K :=
    (RationalMapFunctionField.functionFieldAlgEquivAffine
      hZ.isQuasiAffineVariety).trans efrac
  let e : τ ≃ {j : Option τ // j ≠ none} := optionChartEquiv τ
  let Y : Set ({j : Option τ // j ≠ none} → k) :=
    reindexAffineSet (k := k) (σ := τ)
      (τ := {j : Option τ // j ≠ none}) e Z
  let hY : IsAffineVariety Y :=
    reindexAffineSet_isAffineVariety (k := k) (σ := τ)
      (τ := {j : Option τ // j ≠ none}) e hZ
  let reindexHom : VarietyHom
      (Variety.ofQuasiAffine hY.isQuasiAffineVariety)
      (Variety.ofQuasiAffine hZ.isQuasiAffineVariety) :=
    reindexToOriginalHom (k := k) (σ := τ)
      (τ := {j : Option τ // j ≠ none}) e hZ
  have hreindexHom : reindexHom.IsIso :=
    reindexToOriginalHom_isIso (k := k) (σ := τ)
      (τ := {j : Option τ // j ≠ none}) e hZ
  let eYK : (Variety.ofQuasiAffine hY.isQuasiAffineVariety).FunctionField ≃ₐ[k] K :=
    (RationalMapFunctionField.functionFieldAlgEquivOfIsIso
      reindexHom hreindexHom).symm.trans eZK
  let H := projectiveClosure (none : Option τ) Y
  let hH : IsProjVariety H :=
    projectiveClosure_isProjVariety (none : Option τ) hY
  let P : SeparatedVariety k :=
    ⟨Variety.ofProjective hH,
      isSeparated_ofQuasiProjective hH.isQuasiProjVariety⟩
  let A : SeparatedVariety k :=
    ⟨Variety.ofQuasiAffine hY.isQuasiAffineVariety,
      RationalMapFunctionField.isSeparated_ofQuasiAffine
        hY.isQuasiAffineVariety⟩
  obtain ⟨ePA⟩ :=
    (birational_iff_nonempty_functionField_algEquiv P A
      (Variety.hasAffineOpenBasis_ofProjective hH)
      (Variety.hasAffineOpenBasis_ofAffine hY)).mp
      (birational_projectiveClosure (none : Option τ) hY)
  let ePK : P.toVariety.FunctionField ≃ₐ[k] K := ePA.trans eYK
  have hcurve : (Variety.ofProjective hH).IsCurve :=
    (Variety.hasAffineOpenBasis_ofProjective hH).isCurve_iff_trdeg_eq_one.mpr
      (ePK.trdeg_eq.trans htrdeg)
  let X : QuasiProjectiveCurveCat k :=
    { ι := Option τ
      carrier := H
      isQuasiProjective := hH.isQuasiProjVariety
      isCurve := hcurve }
  refine ⟨X, ⟨?_⟩⟩
  exact ePK

instance essSurj_functionFieldFunctor :
    (functionFieldFunctor (k := k)).EssSurj where
  mem_essImage K := by
    let _ : Field K.obj := K.property.1.toField
    let _ : Algebra.EssFiniteType k K.obj := K.property.2.1
    obtain ⟨X, ⟨e⟩⟩ :=
      exists_quasiProjectiveCurve_functionField_algEquiv
        (k := k) K.obj K.property.2.2
    exact ⟨Opposite.op X,
      ⟨ObjectProperty.isoMk _ (CommAlgCat.isoMk e)⟩⟩

instance isEquivalence_functionFieldFunctor :
    (functionFieldFunctor (k := k)).IsEquivalence where

end QuasiProjectiveCurveCat

/-- The arrow-reversing equivalence between quasi-projective curves with
dominant rational maps and one-dimensional function fields. -/
noncomputable def quasiProjectiveCurveFunctionFieldEquivalence :
    (QuasiProjectiveCurveCat k)ᵒᵖ ≌ OneDimensionalFunctionFieldCat k :=
  (QuasiProjectiveCurveCat.functionFieldFunctor (k := k)).asEquivalence

end Hartshorne

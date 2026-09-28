/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Curve.CurveToValuationSpaceIso
import Hartshorne.Curve.DVRAffineModel
import Hartshorne.Curve.ValuationSpaceFieldEquivalence
import Hartshorne.Rational.ProjectiveClosure

/-!
# Two affine charts covering a valuation curve

The normalizations of `k[t]` and `k[t⁻¹]` in a one-dimensional function
field give two nonsingular affine curves.  We realize each affine curve in a
standard projective chart, apply the point-to-local-ring isomorphism, and then
transport its function field back to the prescribed ambient field.  The two
resulting open embeddings cover the whole valuation curve.
-/

namespace Hartshorne

open MvPolynomial Set TopologicalSpace Topology
open scoped Hartshorne

noncomputable section

universe u v

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

namespace ValuationSpace

/-! ## Reindexing an affine presentation into an `Option` chart -/

private def optionCoordinates {σ : Type v} (x : σ → k) :
    {j : Option σ // j ≠ none} → k
  | ⟨none, h⟩ => (h rfl).elim
  | ⟨some i, _⟩ => x i

private def eraseNone {σ : Type v}
    (y : {j : Option σ // j ≠ none} → k) : σ → k :=
  fun i ↦ y ⟨some i, by simp⟩

omit [Field k] in
@[simp]
private theorem eraseNone_optionCoordinates {σ : Type v} (x : σ → k) :
    eraseNone (optionCoordinates x) = x := by
  funext i
  rfl

omit [Field k] in
@[simp]
private theorem optionCoordinates_eraseNone {σ : Type v}
    (y : {j : Option σ // j ≠ none} → k) :
    optionCoordinates (eraseNone y) = y := by
  funext j
  rcases j with ⟨_ | i, h⟩
  · exact (h rfl).elim
  · rfl

private theorem continuous_eraseNone {σ : Type v} :
    Continuous (eraseNone (k := k) (σ := σ)) := by
  rw [continuous_iff_isClosed]
  intro C hC
  obtain ⟨T, rfl⟩ := isClosed_iff_isAlgebraicSet.1 hC
  have heq :
      eraseNone (k := k) ⁻¹' zeroSet T =
        zeroSet (rename (fun i : σ ↦ (⟨some i, by simp⟩ :
          {j : Option σ // j ≠ none})) '' T) := by
    ext y
    simp only [Set.mem_preimage, mem_zeroSet_iff, Set.mem_image]
    constructor
    · intro hy p hp
      obtain ⟨q, hq, rfl⟩ := hp
      rw [MvPolynomial.eval_rename]
      exact hy q hq
    · intro hy q hq
      have h := hy (rename
        (fun i : σ ↦ (⟨some i, by simp⟩ :
          {j : Option σ // j ≠ none})) q) ⟨q, hq, rfl⟩
      rw [MvPolynomial.eval_rename] at h
      exact h
  rw [heq]
  exact isClosed_zeroSet _

private def optionIndex {σ : Type v} :
    {j : Option σ // j ≠ none} → σ
  | ⟨none, h⟩ => (h rfl).elim
  | ⟨some i, _⟩ => i

omit [Field k] in
private theorem optionCoordinates_eq_comp {σ : Type v} (x : σ → k) :
    optionCoordinates x = x ∘ optionIndex := by
  funext j
  rcases j with ⟨_ | i, h⟩
  · exact (h rfl).elim
  · rfl

private theorem continuous_optionCoordinates {σ : Type v} :
    Continuous (optionCoordinates (k := k) (σ := σ)) := by
  rw [continuous_iff_isClosed]
  intro C hC
  obtain ⟨T, rfl⟩ := isClosed_iff_isAlgebraicSet.1 hC
  have heq :
      optionCoordinates (k := k) ⁻¹' zeroSet T =
        zeroSet (rename (optionIndex (σ := σ)) '' T) := by
    ext x
    simp only [Set.mem_preimage, mem_zeroSet_iff, Set.mem_image]
    constructor
    · intro hx p hp
      obtain ⟨q, hq, rfl⟩ := hp
      rw [MvPolynomial.eval_rename]
      simpa [optionCoordinates_eq_comp] using hx q hq
    · intro hx q hq
      have h := hx (rename (optionIndex (σ := σ)) q) ⟨q, hq, rfl⟩
      rw [MvPolynomial.eval_rename] at h
      simpa [optionCoordinates_eq_comp] using h
  rw [heq]
  exact isClosed_zeroSet _

private def optionReindex {σ : Type v} (Y : Set (σ → k)) :
    Set ({j : Option σ // j ≠ none} → k) :=
  optionCoordinates '' Y

omit [Field k] in
private theorem optionReindex_eq_preimage {σ : Type v} (Y : Set (σ → k)) :
    optionReindex (k := k) Y = eraseNone (k := k) ⁻¹' Y := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro hy
    exact ⟨eraseNone y, hy, optionCoordinates_eraseNone y⟩

private theorem optionReindex_isAffineVariety {σ : Type v}
    {Y : Set (σ → k)} (hY : IsAffineVariety Y) :
    IsAffineVariety (optionReindex (k := k) Y) := by
  refine ⟨hY.isIrreducible.image _
    (continuous_optionCoordinates (k := k) (σ := σ)).continuousOn, ?_⟩
  rw [optionReindex_eq_preimage]
  exact hY.isClosed.preimage (continuous_eraseNone (k := k) (σ := σ))

private theorem affineCoordinate_isGlobalRegular
    {σ : Type u} [Finite σ] {Y : Set (σ → k)}
    (hY : IsQuasiAffineVariety Y) (i : σ) :
    (Variety.ofQuasiAffine hY).IsGlobalRegular (fun y ↦ y.1 i) := by
  intro _
  exact ⟨Set.univ, isOpen_univ, Set.mem_univ _, X i, 1, by simp, by simp⟩

private def optionReindexToOriginalFun {σ : Type v} {Y : Set (σ → k)} :
    optionReindex (k := k) Y → Y :=
  fun y ↦ ⟨eraseNone y.1, by
    change y.1 ∈ eraseNone (k := k) ⁻¹' Y
    rw [← optionReindex_eq_preimage]
    exact y.2⟩

private def originalToOptionReindexFun {σ : Type v} {Y : Set (σ → k)} :
    Y → optionReindex (k := k) Y :=
  fun x ↦ ⟨optionCoordinates x.1, ⟨x.1, x.2, rfl⟩⟩

private noncomputable def optionReindexToOriginalHom
    {σ : Type u} [Finite σ] {Y : Set (σ → k)} (hY : IsAffineVariety Y) :
    VarietyHom
      (Variety.ofQuasiAffine
        (optionReindex_isAffineVariety (k := k) hY).isQuasiAffineVariety)
      (Variety.ofQuasiAffine hY.isQuasiAffineVariety) :=
  VarietyHom.ofCoords hY.isQuasiAffineVariety
    optionReindexToOriginalFun fun i ↦ by
      simpa [optionReindexToOriginalFun, eraseNone] using
        affineCoordinate_isGlobalRegular
          (optionReindex_isAffineVariety (k := k) hY).isQuasiAffineVariety
          (⟨some i, by simp⟩ : {j : Option σ // j ≠ none})

private noncomputable def originalToOptionReindexHom
    {σ : Type u} [Finite σ] {Y : Set (σ → k)} (hY : IsAffineVariety Y) :
    VarietyHom
      (Variety.ofQuasiAffine hY.isQuasiAffineVariety)
      (Variety.ofQuasiAffine
        (optionReindex_isAffineVariety (k := k) hY).isQuasiAffineVariety) :=
  VarietyHom.ofCoords
    (optionReindex_isAffineVariety (k := k) hY).isQuasiAffineVariety
    originalToOptionReindexFun fun j ↦ by
      rcases j with ⟨_ | i, hj⟩
      · exact (hj rfl).elim
      · simpa [originalToOptionReindexFun, optionCoordinates] using
          affineCoordinate_isGlobalRegular hY.isQuasiAffineVariety i

private theorem optionReindexToOriginalHom_apply
    {σ : Type u} [Finite σ] {Y : Set (σ → k)} (hY : IsAffineVariety Y)
    (y : (Variety.ofQuasiAffine
      (optionReindex_isAffineVariety (k := k) hY).isQuasiAffineVariety).carrier) :
    (optionReindexToOriginalHom (k := k) hY y).1 = eraseNone y.1 := by
  have hfun : (optionReindexToOriginalHom (k := k) hY).toFun =
      optionReindexToOriginalFun := by
    unfold optionReindexToOriginalHom
    exact VarietyHom.ofCoords_toFun _ _ _
  exact congrArg Subtype.val (congrFun hfun y)

private theorem originalToOptionReindexHom_apply
    {σ : Type u} [Finite σ] {Y : Set (σ → k)} (hY : IsAffineVariety Y)
    (x : (Variety.ofQuasiAffine hY.isQuasiAffineVariety).carrier) :
    (originalToOptionReindexHom (k := k) hY x).1 =
      optionCoordinates x.1 := by
  have hfun : (originalToOptionReindexHom (k := k) hY).toFun =
      originalToOptionReindexFun := by
    unfold originalToOptionReindexHom
    exact VarietyHom.ofCoords_toFun _ _ _
  exact congrArg Subtype.val (congrFun hfun x)

private theorem optionReindexToOriginalHom_isIso
    {σ : Type u} [Finite σ] {Y : Set (σ → k)} (hY : IsAffineVariety Y) :
    (optionReindexToOriginalHom (k := k) hY).IsIso := by
  refine ⟨originalToOptionReindexHom (k := k) hY, ?_, ?_⟩
  · apply VarietyHom.ext
    funext y
    apply Subtype.ext
    rw [VarietyHom.comp_apply, originalToOptionReindexHom_apply,
      optionReindexToOriginalHom_apply, optionCoordinates_eraseNone]
    rfl
  · apply VarietyHom.ext
    funext x
    apply Subtype.ext
    rw [VarietyHom.comp_apply, optionReindexToOriginalHom_apply,
      originalToOptionReindexHom_apply, eraseNone_optionCoordinates]
    rfl

/-! ## An open affine normalization model -/

private theorem isOpenEmbedding_of_varietyHom_isIso
    {X Y : Variety k} {f : VarietyHom X Y} (hf : f.IsIso) :
    IsOpenEmbedding f.toFun := by
  obtain ⟨g, hgf, hfg⟩ := hf
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap
    f.continuous_toFun ?_ (IsOpenMap.of_inverse g.continuous_toFun ?_ ?_)
  · exact (show f.IsIso from ⟨g, hgf, hfg⟩).bijective.injective
  · intro y
    have h := congrArg (fun q : VarietyHom Y Y ↦ q.toFun y) hfg
    simpa using h
  · intro x
    have h := congrArg (fun q : VarietyHom X X ↦ q.toFun x) hgf
    simpa using h

private def restrictOpenOfLE (X : Variety k) (U V : Opens X.carrier)
    (hV : (V : Set X.carrier).Nonempty) :
    Opens (X.restrict V hV).carrier where
  carrier := {x | x.1 ∈ U}
  is_open' := U.isOpen.preimage continuous_subtype_val

private theorem restrictOpenOfLE_nonempty (X : Variety k)
    (U V : Opens X.carrier) (hUV : U ≤ V)
    (hU : (U : Set X.carrier).Nonempty)
    (hV : (V : Set X.carrier).Nonempty) :
    ((restrictOpenOfLE X U V hV : Opens (X.restrict V hV).carrier) :
      Set (X.restrict V hV).carrier).Nonempty := by
  obtain ⟨x, hx⟩ := hU
  exact ⟨⟨x, hUV hx⟩, hx⟩

private noncomputable def restrictToRestrictOfLEHom (X : Variety k)
    (U V : Opens X.carrier) (hUV : U ≤ V)
    (hU : (U : Set X.carrier).Nonempty)
    (hV : (V : Set X.carrier).Nonempty) :
    VarietyHom (X.restrict U hU)
      ((X.restrict V hV).restrict (restrictOpenOfLE X U V hV)
        (restrictOpenOfLE_nonempty X U V hUV hU hV)) :=
  VarietyHom.liftToRestrict (X.inclHomOfLE hUV hU hV)
    (restrictOpenOfLE X U V hV)
    (restrictOpenOfLE_nonempty X U V hUV hU hV) (fun x ↦ x.2)

private noncomputable def restrictToRestrictOfLEInv (X : Variety k)
    (U V : Opens X.carrier) (hUV : U ≤ V)
    (hU : (U : Set X.carrier).Nonempty)
    (hV : (V : Set X.carrier).Nonempty) :
    VarietyHom
      ((X.restrict V hV).restrict (restrictOpenOfLE X U V hV)
        (restrictOpenOfLE_nonempty X U V hUV hU hV))
      (X.restrict U hU) :=
  VarietyHom.liftToRestrict
    ((X.inclHom V hV).comp
      ((X.restrict V hV).inclHom (restrictOpenOfLE X U V hV)
        (restrictOpenOfLE_nonempty X U V hUV hU hV)))
    U hU (fun x ↦ x.2)

private theorem restrictToRestrictOfLEHom_isIso (X : Variety k)
    (U V : Opens X.carrier) (hUV : U ≤ V)
    (hU : (U : Set X.carrier).Nonempty)
    (hV : (V : Set X.carrier).Nonempty) :
    (restrictToRestrictOfLEHom X U V hUV hU hV).IsIso := by
  refine ⟨restrictToRestrictOfLEInv X U V hUV hU hV, ?_, ?_⟩
  · apply VarietyHom.ext
    funext x
    rfl
  · apply VarietyHom.ext
    funext x
    rfl

private noncomputable def abstractCurveOpenInFull
    [IsAlgClosed k] [Algebra.EssFiniteType k K]
    (htrdeg : Algebra.trdeg k K = 1)
    (U : Opens (ValuationSpace k K)) :
    Opens (abstractNonsingularCurveOfFunctionField htrdeg).carrier where
  carrier := {R | R.1 ∈ U}
  is_open' := U.isOpen.preimage continuous_subtype_val

private theorem abstractCurveOpenInFull_nonempty
    [IsAlgClosed k] [Algebra.EssFiniteType k K]
    (htrdeg : Algebra.trdeg k K = 1)
    (U : Opens (ValuationSpace k K))
    (hU : (U : Set (ValuationSpace k K)).Nonempty) :
    ((abstractCurveOpenInFull htrdeg U : Opens
      (abstractNonsingularCurveOfFunctionField htrdeg).carrier) :
      Set (abstractNonsingularCurveOfFunctionField htrdeg).carrier).Nonempty := by
  obtain ⟨R, hR⟩ := hU
  exact ⟨⟨R, trivial⟩, hR⟩

private noncomputable def abstractCurveOpenToFullRestrictionHom
    [IsAlgClosed k] [Algebra.EssFiniteType k K]
    (htrdeg : Algebra.trdeg k K = 1)
    (U : Opens (ValuationSpace k K))
    (hU : (U : Set (ValuationSpace k K)).Nonempty) :
    VarietyHom (abstractNonsingularCurve htrdeg U hU)
      ((abstractNonsingularCurveOfFunctionField htrdeg).restrict
        (abstractCurveOpenInFull htrdeg U)
        (abstractCurveOpenInFull_nonempty htrdeg U hU)) := by
  have htop : ((⊤ : Opens (ValuationSpace k K)) :
      Set (ValuationSpace k K)).Nonempty := ⟨hU.some, trivial⟩
  unfold abstractNonsingularCurveOfFunctionField
  unfold abstractNonsingularCurve
  unfold abstractCurveOpenInFull
  exact restrictToRestrictOfLEHom (abstractNonsingularCurveAmbient htrdeg)
    U ⊤ (fun _ _ ↦ trivial) hU htop

private theorem abstractCurveOpenToFullRestrictionHom_isIso
    [IsAlgClosed k] [Algebra.EssFiniteType k K]
    (htrdeg : Algebra.trdeg k K = 1)
    (U : Opens (ValuationSpace k K))
    (hU : (U : Set (ValuationSpace k K)).Nonempty) :
    (abstractCurveOpenToFullRestrictionHom htrdeg U hU).IsIso := by
  have htop : ((⊤ : Opens (ValuationSpace k K)) :
      Set (ValuationSpace k K)).Nonempty := ⟨hU.some, trivial⟩
  unfold abstractCurveOpenToFullRestrictionHom
  unfold abstractNonsingularCurveOfFunctionField
  unfold abstractNonsingularCurve
  unfold abstractCurveOpenInFull
  exact restrictToRestrictOfLEHom_isIso (abstractNonsingularCurveAmbient htrdeg)
    U ⊤ (fun _ _ ↦ trivial) hU htop

/-- One normalization chart, realized as a nonsingular affine curve and as an
open subcurve of the full valuation curve.  Besides the open embedding, the
package retains the coordinate-ring and function-field identifications used
to construct it. -/
structure AffineNormalizationModel [IsAlgClosed k]
    [Algebra.EssFiniteType k K]
    (htrdeg : Algebra.trdeg k K = 1)
    (C : SeparableNormalizationChart k K) where
  ι : Type u
  [finite_ι : Finite ι]
  Y : Set (ι → k)
  isAffineVariety : IsAffineVariety Y
  coordinateRingEquiv : coordinateRing Y ≃ₐ[k] C.normalization
  functionFieldEquiv : FunctionField isAffineVariety.isIrreducible ≃ₐ[k] K
  isCurve :
    (Variety.ofQuasiAffine isAffineVariety.isQuasiAffineVariety).IsCurve
  nonsingular :
    (Variety.ofQuasiAffine isAffineVariety.isQuasiAffineVariety).Nonsingular
  functionFieldEquiv_coord : ∀ a : coordinateRing Y,
    functionFieldEquiv
        (coordToRational isAffineVariety.isIrreducible a) =
      ((coordinateRingEquiv a : C.normalization) : K)
  openCurve : Variety k
  chartIso : VarietyHom
    (Variety.ofQuasiAffine isAffineVariety.isQuasiAffineVariety) openCurve
  chartIso_isIso : chartIso.IsIso
  inclusion : VarietyHom openCurve
    (abstractNonsingularCurveOfFunctionField htrdeg)
  inclusion_isOpenEmbedding : IsOpenEmbedding inclusion.toFun
  imageOpen : Opens
    (abstractNonsingularCurveOfFunctionField htrdeg).carrier
  imageOpen_nonempty :
    ((imageOpen : Opens
      (abstractNonsingularCurveOfFunctionField htrdeg).carrier) :
      Set (abstractNonsingularCurveOfFunctionField htrdeg).carrier).Nonempty
  inclusionToImage : VarietyHom openCurve
    ((abstractNonsingularCurveOfFunctionField htrdeg).restrict
      imageOpen imageOpen_nonempty)
  inclusionToImage_isIso : inclusionToImage.IsIso
  inclusion_factorization :
    ((abstractNonsingularCurveOfFunctionField htrdeg).inclHom
      imageOpen imageOpen_nonempty).comp inclusionToImage = inclusion
  contains_normalization_mem_range :
    ∀ R : FunctionFieldDVR k K,
      C.normalization.toSubring ≤ R.toValuationSubring.toSubring →
      (⟨ValuationSpace.of k K R, trivial⟩ :
        (abstractNonsingularCurveOfFunctionField htrdeg).carrier) ∈
        Set.range inclusion

namespace AffineNormalizationModel

/-- The affine normalization model embedded into the full valuation curve. -/
noncomputable def embedding [IsAlgClosed k] [Algebra.EssFiniteType k K]
    {htrdeg : Algebra.trdeg k K = 1}
    {C : SeparableNormalizationChart k K}
    (M : AffineNormalizationModel htrdeg C) :
    VarietyHom
      (Variety.ofQuasiAffine M.isAffineVariety.isQuasiAffineVariety)
      (abstractNonsingularCurveOfFunctionField htrdeg) :=
  M.inclusion.comp M.chartIso

/-- The affine chart, with its codomain restricted to its named open image. -/
noncomputable def chartToImage [IsAlgClosed k]
    [Algebra.EssFiniteType k K]
    {htrdeg : Algebra.trdeg k K = 1}
    {C : SeparableNormalizationChart k K}
    (M : AffineNormalizationModel htrdeg C) :
    VarietyHom
      (Variety.ofQuasiAffine M.isAffineVariety.isQuasiAffineVariety)
      ((abstractNonsingularCurveOfFunctionField htrdeg).restrict
        M.imageOpen M.imageOpen_nonempty) :=
  M.inclusionToImage.comp M.chartIso

/-- The affine model is isomorphic, as a variety, to its named open image. -/
theorem chartToImage_isIso [IsAlgClosed k]
    [Algebra.EssFiniteType k K]
    {htrdeg : Algebra.trdeg k K = 1}
    {C : SeparableNormalizationChart k K}
    (M : AffineNormalizationModel htrdeg C) :
    M.chartToImage.IsIso :=
  M.inclusionToImage_isIso.comp M.chartIso_isIso

/-- The affine embedding factors through its named open image. -/
theorem embedding_factorization [IsAlgClosed k]
    [Algebra.EssFiniteType k K]
    {htrdeg : Algebra.trdeg k K = 1}
    {C : SeparableNormalizationChart k K}
    (M : AffineNormalizationModel htrdeg C) :
    ((abstractNonsingularCurveOfFunctionField htrdeg).inclHom
      M.imageOpen M.imageOpen_nonempty).comp M.chartToImage = M.embedding := by
  calc
    ((abstractNonsingularCurveOfFunctionField htrdeg).inclHom
          M.imageOpen M.imageOpen_nonempty).comp M.chartToImage =
        (((abstractNonsingularCurveOfFunctionField htrdeg).inclHom
          M.imageOpen M.imageOpen_nonempty).comp M.inclusionToImage).comp
            M.chartIso :=
      (VarietyHom.comp_assoc _ _ _).symm
    _ = M.inclusion.comp M.chartIso := by rw [M.inclusion_factorization]
    _ = M.embedding := rfl

/-- The affine model is openly embedded in the full valuation curve. -/
theorem embedding_isOpenEmbedding [IsAlgClosed k]
    [Algebra.EssFiniteType k K]
    {htrdeg : Algebra.trdeg k K = 1}
    {C : SeparableNormalizationChart k K}
    (M : AffineNormalizationModel htrdeg C) :
    IsOpenEmbedding M.embedding.toFun :=
  M.inclusion_isOpenEmbedding.comp
    (isOpenEmbedding_of_varietyHom_isIso M.chartIso_isIso)

/-- The set-theoretic image of the affine embedding is its named open. -/
theorem range_embedding_eq_imageOpen [IsAlgClosed k]
    [Algebra.EssFiniteType k K]
    {htrdeg : Algebra.trdeg k K = 1}
    {C : SeparableNormalizationChart k K}
    (M : AffineNormalizationModel htrdeg C) :
    Set.range M.embedding.toFun = (M.imageOpen : Set
      (abstractNonsingularCurveOfFunctionField htrdeg).carrier) := by
  calc
    Set.range M.embedding.toFun = Set.range M.inclusion.toFun := by
      change Set.range (M.inclusion.toFun ∘ M.chartIso.toFun) =
        Set.range M.inclusion.toFun
      exact M.chartIso_isIso.bijective.surjective.range_comp _
    _ = Set.range
        (((abstractNonsingularCurveOfFunctionField htrdeg).inclHom
          M.imageOpen M.imageOpen_nonempty).comp M.inclusionToImage).toFun := by
      rw [M.inclusion_factorization]
    _ = Set.range
        ((abstractNonsingularCurveOfFunctionField htrdeg).inclHom
          M.imageOpen M.imageOpen_nonempty).toFun := by
      change Set.range
          (((abstractNonsingularCurveOfFunctionField htrdeg).inclHom
            M.imageOpen M.imageOpen_nonempty).toFun ∘
              M.inclusionToImage.toFun) = _
      exact M.inclusionToImage_isIso.bijective.surjective.range_comp _
    _ = (M.imageOpen : Set
        (abstractNonsingularCurveOfFunctionField htrdeg).carrier) := by
      change Set.range (fun x : M.imageOpen ↦ x.1) = _
      exact Subtype.range_coe

/-- A valuation ring containing the normalization lies in the image of the
corresponding affine model. -/
theorem contains_normalization_mem_range_embedding [IsAlgClosed k]
    [Algebra.EssFiniteType k K]
    {htrdeg : Algebra.trdeg k K = 1}
    {C : SeparableNormalizationChart k K}
    (M : AffineNormalizationModel htrdeg C)
    (R : FunctionFieldDVR k K)
    (hR : C.normalization.toSubring ≤ R.toValuationSubring.toSubring) :
    (⟨ValuationSpace.of k K R, trivial⟩ :
      (abstractNonsingularCurveOfFunctionField htrdeg).carrier) ∈
      Set.range M.embedding := by
  obtain ⟨w, hw⟩ := M.contains_normalization_mem_range R hR
  obtain ⟨y, rfl⟩ := M.chartIso_isIso.bijective.surjective w
  exact ⟨y, hw⟩

/-! The coordinate reindexing used to take the projective closure of a model. -/

/-- Reindex an affine normalization model by the non-homogenizing coordinates
of `Option M.ι`.  The extra coordinate `none` is reserved for homogenization. -/
def projectiveReindex [IsAlgClosed k] [Algebra.EssFiniteType k K]
    {htrdeg : Algebra.trdeg k K = 1}
    {C : SeparableNormalizationChart k K}
    (M : AffineNormalizationModel htrdeg C) :
    Set ({j : Option M.ι // j ≠ none} → k) :=
  optionReindex (k := k) M.Y

/-- The coordinate reindexing of an affine normalization model is again an
affine variety. -/
theorem projectiveReindex_isAffineVariety [IsAlgClosed k]
    [Algebra.EssFiniteType k K]
    {htrdeg : Algebra.trdeg k K = 1}
    {C : SeparableNormalizationChart k K}
    (M : AffineNormalizationModel htrdeg C) :
    IsAffineVariety M.projectiveReindex :=
  optionReindex_isAffineVariety (k := k) M.isAffineVariety

/-- The original affine model, with its coordinates reindexed for the
projective-closure construction. -/
noncomputable def toProjectiveReindex [IsAlgClosed k]
    [Algebra.EssFiniteType k K]
    {htrdeg : Algebra.trdeg k K = 1}
    {C : SeparableNormalizationChart k K}
    (M : AffineNormalizationModel htrdeg C) :
    VarietyHom
      (Variety.ofQuasiAffine M.isAffineVariety.isQuasiAffineVariety)
      (Variety.ofQuasiAffine
        M.projectiveReindex_isAffineVariety.isQuasiAffineVariety) := by
  letI := M.finite_ι
  exact originalToOptionReindexHom (k := k) M.isAffineVariety

/-- Reindexing the affine coordinates does not change the affine variety up to
isomorphism. -/
theorem toProjectiveReindex_isIso [IsAlgClosed k]
    [Algebra.EssFiniteType k K]
    {htrdeg : Algebra.trdeg k K = 1}
    {C : SeparableNormalizationChart k K}
    (M : AffineNormalizationModel htrdeg C) :
    M.toProjectiveReindex.IsIso := by
  let _ := M.finite_ι
  change (originalToOptionReindexHom (k := k) M.isAffineVariety).IsIso
  refine ⟨optionReindexToOriginalHom (k := k) M.isAffineVariety, ?_, ?_⟩
  · apply VarietyHom.ext
    funext x
    apply Subtype.ext
    rw [VarietyHom.comp_apply, optionReindexToOriginalHom_apply,
      originalToOptionReindexHom_apply, eraseNone_optionCoordinates]
    rfl
  · apply VarietyHom.ext
    funext y
    apply Subtype.ext
    rw [VarietyHom.comp_apply, originalToOptionReindexHom_apply,
      optionReindexToOriginalHom_apply, optionCoordinates_eraseNone]
    rfl

end AffineNormalizationModel

private noncomputable def abstractNonsingularCurveInclHom
    [IsAlgClosed k] [Algebra.EssFiniteType k K]
    (htrdeg : Algebra.trdeg k K = 1)
    (U : Opens (ValuationSpace k K))
    (hU : (U : Set (ValuationSpace k K)).Nonempty) :
    VarietyHom (abstractNonsingularCurve htrdeg U hU)
      (abstractNonsingularCurveOfFunctionField htrdeg) := by
  have htop : ((⊤ : Opens (ValuationSpace k K)) :
      Set (ValuationSpace k K)).Nonempty :=
    ⟨hU.some, trivial⟩
  unfold abstractNonsingularCurveOfFunctionField
  unfold abstractNonsingularCurve
  exact Variety.inclHomOfLE _ le_top hU htop

private theorem abstractNonsingularCurveInclHom_isOpenEmbedding
    [IsAlgClosed k] [Algebra.EssFiniteType k K]
    (htrdeg : Algebra.trdeg k K = 1)
    (U : Opens (ValuationSpace k K))
    (hU : (U : Set (ValuationSpace k K)).Nonempty) :
    IsOpenEmbedding
      (abstractNonsingularCurveInclHom htrdeg U hU).toFun := by
  change IsOpenEmbedding (fun x : U ↦
    (⟨x.1, trivial⟩ : (⊤ : Opens (ValuationSpace k K))))
  let g : (abstractNonsingularCurveOfFunctionField htrdeg).carrier →
      ValuationSpace k K := fun R ↦ R.1
  have hg : IsOpenEmbedding g := by
    exact (isOpen_univ : IsOpen (Set.univ : Set (ValuationSpace k K))).isOpenEmbedding_subtypeVal
  apply IsOpenEmbedding.of_comp _ hg
  change IsOpenEmbedding (fun x : U ↦ x.1)
  exact U.isOpen.isOpenEmbedding_subtypeVal

private theorem exists_affineNormalizationModel [IsAlgClosed k]
    [Algebra.EssFiniteType k K]
    (htrdeg : Algebra.trdeg k K = 1)
    (C : SeparableNormalizationChart k K) :
    Nonempty (AffineNormalizationModel htrdeg C) := by
  classical
  obtain ⟨τ, hτ, Y, hY, ⟨eB⟩⟩ :=
    RationalMapFunctionField.exists_isAffineVariety_coordinateRing_equiv_sameUniverse
      (k := k) (B := C.normalization)
  let _ : Finite τ := hτ
  let _ : IsDomain (coordinateRing Y) := isDomain_coordinateRing hY
  let _ : IsFractionRing (coordinateRing Y)
      (FunctionField hY.isIrreducible) :=
    isFractionRing_functionField hY.isIrreducible
  let eK : FunctionField hY.isIrreducible ≃ₐ[k] K :=
    IsFractionRing.algEquivOfAlgEquiv eB
  have hcurve :
      (Variety.ofQuasiAffine hY.isQuasiAffineVariety).IsCurve := by
    change dim Y = 1
    rw [dim_eq_ringKrullDim_coordinateRing hY.isAlgebraicSet,
      ringKrullDim_eq_of_ringEquiv eB.toRingEquiv,
      C.ringKrullDim_normalization]
  have hnfield : ¬ IsField C.normalization := fun hB ↦
    zero_ne_one
      ((ringKrullDim_eq_zero_of_isField hB).symm.trans
        C.ringKrullDim_normalization)
  have hns :
      (Variety.ofQuasiAffine hY.isQuasiAffineVariety).Nonsingular := by
    intro Q
    rw [Variety.NonsingularAt]
    let Q' : Y := affinePoint hY.isQuasiAffineVariety Q
    let q : Ideal C.normalization :=
      Ideal.map eB.toRingHom (maximalIdealAt Y Q')
    let _ : q.IsMaximal := by
      dsimp [q]
      exact (maximalIdealAt_isMaximal Q').map_bijective
        eB.toRingHom eB.bijective
    let _ : q.IsPrime := (show q.IsMaximal from inferInstance).isPrime
    have hQ : maximalIdealAt Y Q' = Ideal.comap eB.toRingHom q := by
      dsimp [q]
      exact (Ideal.comap_map_of_bijective eB.toRingHom eB.bijective).symm
    have hsub :
        Submonoid.map eB (maximalIdealAt Y Q').primeCompl = q.primeCompl := by
      ext b
      constructor
      · rintro ⟨a, ha, rfl⟩
        change a ∉ maximalIdealAt Y Q' at ha
        change eB a ∉ q
        intro hea
        apply ha
        rw [hQ, Ideal.mem_comap]
        exact hea
      · intro hb
        refine ⟨eB.symm b, ?_, eB.apply_symm_apply b⟩
        change b ∉ q at hb
        change eB.symm b ∉ maximalIdealAt Y Q'
        intro he
        apply hb
        have hc : eB.symm b ∈ Ideal.comap eB.toRingHom q := by
          rw [← hQ]
          exact he
        rw [Ideal.mem_comap] at hc
        simpa using hc
    have hq : q ≠ ⊥ :=
      Ring.ne_bot_of_isMaximal_of_not_isField
        (show q.IsMaximal from inferInstance) hnfield
    let _ : IsDiscreteValuationRing (Localization.AtPrime q) :=
      dedekind_localization_dvr C.normalization
        C.ringKrullDim_normalization q hq
    let eQ : LocalRingAt hY.isIrreducible Q' ≃+*
        Localization.AtPrime q :=
      (localizationEquivLocalRing hY.isIrreducible Q').symm.trans
        (IsLocalization.ringEquivOfRingEquiv
          (Localization.AtPrime (maximalIdealAt Y Q'))
          (Localization.AtPrime q) eB.toRingEquiv hsub)
    let eAbstract :
      (Variety.ofQuasiAffine hY.isQuasiAffineVariety).LocalRingAt Q ≃+*
          Localization.AtPrime q :=
      (localRingEquivAffine hY.isQuasiAffineVariety Q).trans eQ
    exact (isRegularLocalRing_iff_of_ringEquiv
      (R := (Variety.ofQuasiAffine
        hY.isQuasiAffineVariety).LocalRingAt Q)
      (S := Localization.AtPrime q) eAbstract).mpr (by infer_instance)
  have hcoord : ∀ a : coordinateRing Y,
      eK (coordToRational hY.isIrreducible a) =
        ((eB a : C.normalization) : K) := by
    intro a
    change eK (algebraMap (coordinateRing Y)
      (FunctionField hY.isIrreducible) a) =
        algebraMap C.normalization K (eB a)
    exact IsFractionRing.algEquivOfAlgEquiv_algebraMap eB a
  let Z := optionReindex (k := k) Y
  let hZ : IsAffineVariety Z := optionReindex_isAffineVariety (k := k) hY
  let i : Option τ := none
  let P := projectiveClosure i Z
  let hP : IsProjVariety P := projectiveClosure_isProjVariety i hZ
  let hne : (P ∩ standardChart i).Nonempty :=
    projectiveClosure_inter_standardChart_nonempty i hZ
  let hQ : IsQuasiProjVariety (P ∩ standardChart i) :=
    isQuasiProjVariety_inter_standardChart k i hP.isQuasiProjVariety hne
  let Q := Variety.ofQuasiProjective hQ
  let qToZ : VarietyHom Q
      (Variety.ofQuasiAffine hZ.isQuasiAffineVariety) :=
    (projectiveClosureChartToAffineHom i hZ).comp
      (chartHom k i hP.isQuasiProjVariety hne)
  have hqToZ : qToZ.IsIso :=
    (projectiveClosureChartToAffineHom_isIso i hZ).comp
      (isIso_chartHom k i hP.isQuasiProjVariety hne)
  let zToY : VarietyHom
      (Variety.ofQuasiAffine hZ.isQuasiAffineVariety)
      (Variety.ofQuasiAffine hY.isQuasiAffineVariety) :=
    optionReindexToOriginalHom (k := k) hY
  have hzToY : zToY.IsIso :=
    optionReindexToOriginalHom_isIso (k := k) hY
  let qToY : VarietyHom Q
      (Variety.ofQuasiAffine hY.isQuasiAffineVariety) := zToY.comp qToZ
  have hqToY : qToY.IsIso := hzToY.comp hqToZ
  let V : Opens Q.carrier := ⊤
  have hV : (V : Set Q.carrier).Nonempty := Set.univ_nonempty
  let topIncl : VarietyHom (Q.restrict V hV) Q := Q.inclHom V hV
  have htopIncl : topIncl.IsIso := by
    refine ⟨Q.topRestrictHom, ?_, ?_⟩
    · apply VarietyHom.ext
      funext x
      rfl
    · apply VarietyHom.ext
      funext x
      rfl
  let φ : VarietyHom (Q.restrict V hV)
      (Variety.ofQuasiAffine hY.isQuasiAffineVariety) := qToY.comp topIncl
  have hφ : φ.IsIso := hqToY.comp htopIncl
  let eChart : Q.FunctionField ≃ₐ[k] FunctionField hY.isIrreducible :=
    (RationalMapFunctionField.affineChartFunctionFieldAlgEquiv
      V hV hY φ hφ).trans
      (RationalMapFunctionField.functionFieldAlgEquivAffine
        hY.isQuasiAffineVariety)
  let eQK : Q.FunctionField ≃ₐ[k] K := eChart.trans eK
  let hQbasis := Variety.hasAffineOpenBasis_ofQuasiProjective hQ
  let _ : Algebra.EssFiniteType k Q.FunctionField :=
    RationalMapFunctionField.essFiniteType_functionField hQbasis
  have hcurveQ : Q.IsCurve :=
    hQbasis.isCurve_iff_trdeg_eq_one.mpr (eQK.trdeg_eq.trans htrdeg)
  have hnsQ : Q.Nonsingular :=
    (Variety.nonsingular_iff_of_isIso hqToY).mpr hns
  let W := hQ.localRingMapAbstractCurve hcurveQ hnsQ
  let qToW : VarietyHom Q W := hQ.localRingMapAbstractCurveHom hcurveQ hnsQ
  have hqToW : qToW.IsIso :=
    hQ.localRingMapAbstractCurveHom_isIso hcurveQ hnsQ
  obtain ⟨yToQ, hyq, hqy⟩ := hqToY
  have hyToQ : yToQ.IsIso := ⟨qToY, hqy, hyq⟩
  let chartIso : VarietyHom
      (Variety.ofQuasiAffine hY.isQuasiAffineVariety) W := qToW.comp yToQ
  have hchartIso : chartIso.IsIso := hqToW.comp hyToQ
  have htrdegQ : Algebra.trdeg k Q.FunctionField = 1 :=
    hQbasis.isCurve_iff_trdeg_eq_one.mp hcurveQ
  let openIncl : VarietyHom W
      (abstractNonsingularCurveOfFunctionField htrdegQ) :=
    abstractNonsingularCurveInclHom htrdegQ
      (hQ.localRingMapRangeOpen hcurveQ hnsQ)
      (hQ.localRingMapRangeOpen_nonempty hcurveQ hnsQ)
  have hopenIncl : IsOpenEmbedding openIncl.toFun :=
    abstractNonsingularCurveInclHom_isOpenEmbedding htrdegQ
      (hQ.localRingMapRangeOpen hcurveQ hnsQ)
      (hQ.localRingMapRangeOpen_nonempty hcurveQ hnsQ)
  let fieldHom : VarietyHom
      (abstractNonsingularCurveOfFunctionField htrdegQ)
      (abstractNonsingularCurveOfFunctionField htrdeg) :=
    abstractNonsingularCurveHomOfAlgEquiv htrdegQ htrdeg eQK
  have hfieldHom : fieldHom.IsIso :=
    (abstractNonsingularCurveIsoOfAlgEquiv htrdegQ htrdeg eQK).1
  let inclusion : VarietyHom W
      (abstractNonsingularCurveOfFunctionField htrdeg) :=
    fieldHom.comp openIncl
  have hinclusion : IsOpenEmbedding inclusion.toFun := by
    exact (isOpenEmbedding_of_varietyHom_isIso hfieldHom).comp hopenIncl
  obtain ⟨fieldInv, hfieldInv, hinvField⟩ := hfieldHom
  let sourceOpen : Opens
      (abstractNonsingularCurveOfFunctionField htrdegQ).carrier :=
    abstractCurveOpenInFull htrdegQ
      (hQ.localRingMapRangeOpen hcurveQ hnsQ)
  have hsourceOpen : ((sourceOpen : Opens
      (abstractNonsingularCurveOfFunctionField htrdegQ).carrier) :
      Set (abstractNonsingularCurveOfFunctionField htrdegQ).carrier).Nonempty :=
    abstractCurveOpenInFull_nonempty htrdegQ
      (hQ.localRingMapRangeOpen hcurveQ hnsQ)
      (hQ.localRingMapRangeOpen_nonempty hcurveQ hnsQ)
  let wToSource : VarietyHom W
      ((abstractNonsingularCurveOfFunctionField htrdegQ).restrict
        sourceOpen hsourceOpen) :=
    abstractCurveOpenToFullRestrictionHom htrdegQ
      (hQ.localRingMapRangeOpen hcurveQ hnsQ)
      (hQ.localRingMapRangeOpen_nonempty hcurveQ hnsQ)
  have hwToSource : wToSource.IsIso :=
    abstractCurveOpenToFullRestrictionHom_isIso htrdegQ
      (hQ.localRingMapRangeOpen hcurveQ hnsQ)
      (hQ.localRingMapRangeOpen_nonempty hcurveQ hnsQ)
  let imageOpen : Opens
      (abstractNonsingularCurveOfFunctionField htrdeg).carrier :=
    Variety.isoPreimageOpen fieldInv sourceOpen
  have himageOpen : ((imageOpen : Opens
      (abstractNonsingularCurveOfFunctionField htrdeg).carrier) :
      Set (abstractNonsingularCurveOfFunctionField htrdeg).carrier).Nonempty := by
    obtain ⟨x, hx⟩ := hsourceOpen
    refine ⟨fieldHom x, ?_⟩
    change fieldInv (fieldHom x) ∈ sourceOpen
    have he := congrArg
      (fun f : VarietyHom
          (abstractNonsingularCurveOfFunctionField htrdegQ)
          (abstractNonsingularCurveOfFunctionField htrdegQ) ↦ f x)
      hfieldInv
    have he' : fieldInv (fieldHom x) = x := by simpa using he
    rw [he']
    exact hx
  let sourceIncl : VarietyHom
      ((abstractNonsingularCurveOfFunctionField htrdegQ).restrict
        sourceOpen hsourceOpen)
      (abstractNonsingularCurveOfFunctionField htrdegQ) :=
    (abstractNonsingularCurveOfFunctionField htrdegQ).inclHom
      sourceOpen hsourceOpen
  let sourceToTarget : VarietyHom
      ((abstractNonsingularCurveOfFunctionField htrdegQ).restrict
        sourceOpen hsourceOpen)
      (abstractNonsingularCurveOfFunctionField htrdeg) :=
    fieldHom.comp sourceIncl
  have hsourceToTarget (x :
      ((abstractNonsingularCurveOfFunctionField htrdegQ).restrict
        sourceOpen hsourceOpen).carrier) : sourceToTarget x ∈ imageOpen := by
    change fieldInv (fieldHom x.1) ∈ sourceOpen
    have he := congrArg
      (fun f : VarietyHom
          (abstractNonsingularCurveOfFunctionField htrdegQ)
          (abstractNonsingularCurveOfFunctionField htrdegQ) ↦ f x.1)
      hfieldInv
    have he' : fieldInv (fieldHom x.1) = x.1 := by simpa using he
    rw [he']
    exact x.2
  let sourceToImage : VarietyHom
      ((abstractNonsingularCurveOfFunctionField htrdegQ).restrict
        sourceOpen hsourceOpen)
      ((abstractNonsingularCurveOfFunctionField htrdeg).restrict
        imageOpen himageOpen) :=
    VarietyHom.liftToRestrict sourceToTarget imageOpen himageOpen
      hsourceToTarget
  let imageToSource : VarietyHom
      ((abstractNonsingularCurveOfFunctionField htrdeg).restrict
        imageOpen himageOpen)
      ((abstractNonsingularCurveOfFunctionField htrdegQ).restrict
        sourceOpen hsourceOpen) :=
    Variety.restrictIsoPreimageHom fieldInv sourceOpen hsourceOpen himageOpen
  have hsourceToImage : sourceToImage.IsIso := by
    refine ⟨imageToSource, ?_, ?_⟩
    · apply VarietyHom.ext
      funext x
      apply Subtype.ext
      change fieldInv (fieldHom x.1) = x.1
      have he := congrArg
        (fun f : VarietyHom
            (abstractNonsingularCurveOfFunctionField htrdegQ)
            (abstractNonsingularCurveOfFunctionField htrdegQ) ↦ f x.1)
        hfieldInv
      simpa using he
    · apply VarietyHom.ext
      funext x
      apply Subtype.ext
      change fieldHom (fieldInv x.1) = x.1
      have he := congrArg
        (fun f : VarietyHom
            (abstractNonsingularCurveOfFunctionField htrdeg)
            (abstractNonsingularCurveOfFunctionField htrdeg) ↦ f x.1)
        hinvField
      simpa using he
  let inclusionToImage : VarietyHom W
      ((abstractNonsingularCurveOfFunctionField htrdeg).restrict
        imageOpen himageOpen) := sourceToImage.comp wToSource
  have hinclusionToImage : inclusionToImage.IsIso :=
    hsourceToImage.comp hwToSource
  have hinclusionFactorization :
      ((abstractNonsingularCurveOfFunctionField htrdeg).inclHom
        imageOpen himageOpen).comp inclusionToImage = inclusion := by
    apply VarietyHom.ext
    funext x
    apply Subtype.ext
    rfl
  have hcontains : ∀ R : FunctionFieldDVR k K,
      C.normalization.toSubring ≤ R.toValuationSubring.toSubring →
      (⟨ValuationSpace.of k K R, trivial⟩ :
        (abstractNonsingularCurveOfFunctionField htrdeg).carrier) ∈
        Set.range inclusion := by
    intro R hR
    let S : FunctionFieldDVR k Q.FunctionField := transportDVR eQK.symm R
    have hS : ∀ b : coordinateRing Y,
        eChart.symm (coordToRational hY.isIrreducible b) ∈
          S.toValuationSubring := by
      intro b
      rw [show eChart.symm (coordToRational hY.isIrreducible b) ∈
            S.toValuationSubring ↔
          eQK (eChart.symm (coordToRational hY.isIrreducible b)) ∈
            R.toValuationSubring by
        exact mem_transportDVR eQK.symm R _]
      have hb : eK (coordToRational hY.isIrreducible b) ∈
          R.toValuationSubring := by
        rw [hcoord]
        exact hR (eB b).2
      simpa [eQK] using hb
    have hSrange :=
      hQ.functionFieldDVR_mem_range_localRingMap_of_affineChart
        hcurveQ hnsQ V hV hY φ hφ S hS
    obtain ⟨q, hq⟩ := hSrange
    let w : W.carrier := qToW q
    refine ⟨w, ?_⟩
    apply Subtype.ext
    change (valuationSpaceHomeomorph eQK
      ((hQ.localRingMapAbstractCurveHom hcurveQ hnsQ q).1)) =
        ValuationSpace.of k K R
    change (valuationSpaceHomeomorph eQK
      ((hQ.localRingMapAbstractCurveHomeomorph hcurveQ hnsQ q).1)) =
        ValuationSpace.of k K R
    rw [hQ.localRingMapAbstractCurveHomeomorph_apply_val hcurveQ hnsQ q]
    change valuationSpaceHomeomorph eQK
        (ValuationSpace.of k Q.FunctionField
          (hQbasis.functionFieldDVRAt hcurveQ hnsQ q)) =
      ValuationSpace.of k K R
    rw [hq]
    apply (ValuationSpace.of k K).symm.injective
    rw [valuationSpaceHomeomorph_apply, ValuationSpace.of_symm_apply_apply]
    apply FunctionFieldDVR.ext
    intro x
    simp [S]
  exact ⟨{
    ι := τ
    finite_ι := hτ
    Y := Y
    isAffineVariety := hY
    coordinateRingEquiv := eB
    functionFieldEquiv := eK
    isCurve := hcurve
    nonsingular := hns
    functionFieldEquiv_coord := hcoord
    openCurve := W
    chartIso := chartIso
    chartIso_isIso := hchartIso
    inclusion := inclusion
    inclusion_isOpenEmbedding := hinclusion
    imageOpen := imageOpen
    imageOpen_nonempty := himageOpen
    inclusionToImage := inclusionToImage
    inclusionToImage_isIso := hinclusionToImage
    inclusion_factorization := hinclusionFactorization
    contains_normalization_mem_range := hcontains
  }⟩

/-- **Hartshorne I.6, first paragraph of Theorem 6.9.**  The normalization
charts at a separating parameter and its inverse give two nonsingular affine
models, openly embedded in the valuation curve, whose images cover it. -/
theorem exists_two_affine_model_cover [IsAlgClosed k]
    [Algebra.EssFiniteType k K]
    (htrdeg : Algebra.trdeg k K = 1) :
    let C := separableNormalizationCharts k K htrdeg
    ∃ (M₀ : AffineNormalizationModel htrdeg C.atZero)
      (M₁ : AffineNormalizationModel htrdeg C.atInfinity),
      (M₀.imageOpen : Set
          (abstractNonsingularCurveOfFunctionField htrdeg).carrier) ∪
        (M₁.imageOpen : Set
          (abstractNonsingularCurveOfFunctionField htrdeg).carrier) = Set.univ := by
  classical
  dsimp only
  let C := separableNormalizationCharts k K htrdeg
  let M₀ := (exists_affineNormalizationModel htrdeg C.atZero).some
  let M₁ := (exists_affineNormalizationModel htrdeg C.atInfinity).some
  refine ⟨M₀, M₁, ?_⟩
  apply Set.eq_univ_of_forall
  intro R
  let R₀ : FunctionFieldDVR k K := (ValuationSpace.of k K).symm R.1
  rcases C.normalization_cover R₀ with hzero | hinfinity
  · left
    have h := M₀.contains_normalization_mem_range_embedding R₀ hzero
    rw [M₀.range_embedding_eq_imageOpen] at h
    have hpoint :
        (⟨ValuationSpace.of k K R₀, trivial⟩ :
          (abstractNonsingularCurveOfFunctionField htrdeg).carrier) = R := by
      apply Subtype.ext
      exact ValuationSpace.of_apply_symm_apply k K R.1
    rwa [hpoint] at h
  · right
    have h := M₁.contains_normalization_mem_range_embedding R₀ hinfinity
    rw [M₁.range_embedding_eq_imageOpen] at h
    have hpoint :
        (⟨ValuationSpace.of k K R₀, trivial⟩ :
          (abstractNonsingularCurveOfFunctionField htrdeg).carrier) = R := by
      apply Subtype.ext
      exact ValuationSpace.of_apply_symm_apply k K R.1
    rwa [hpoint] at h

end ValuationSpace

end

end Hartshorne

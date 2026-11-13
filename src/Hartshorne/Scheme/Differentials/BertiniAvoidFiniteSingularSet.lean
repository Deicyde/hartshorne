/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.Differentials.BertiniRegularHyperplaneSection
import Hartshorne.Scheme.ReducedInducedSubscheme

/-!
# Bertini's theorem with finitely many singular points

Hartshorne, *Algebraic Geometry*, II.8, Remark 8.18.1 (p. 180).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
  IsLocalRing Topology

namespace Hartshorne

universe u

/-! ### Finite unions of proper closed sets -/

/-- In an irreducible space, a finite union of proper closed subsets is a proper subset. -/
theorem biUnion_ne_univ_of_irreducibleSpace {α ι : Type*} [TopologicalSpace α] [IrreducibleSpace α]
    {S : Set ι} (hS : S.Finite) {T : ι → Set α} (hT : ∀ i ∈ S, IsClosed (T i))
    (hne : ∀ i ∈ S, T i ≠ Set.univ) : (⋃ i ∈ S, T i) ≠ Set.univ := by
  classical
  intro h
  obtain ⟨z, hz, hsub⟩ := isIrreducible_iff_sUnion_isClosed.mp
    (IrreducibleSpace.isIrreducible_univ α) (hS.toFinset.image T)
    (by
      intro z hz
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      exact hT i (hS.mem_toFinset.mp hi))
    (by
      rw [← h]
      intro y hy
      obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp hy
      exact Set.mem_sUnion.mpr ⟨T i, by simpa using ⟨i, hi, rfl⟩, hyi⟩)
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
  exact hne i (hS.mem_toFinset.mp hi) (Set.eq_univ_of_univ_subset hsub)

/-! ### Dimension of a closed irreducible set and of its open traces -/

section Dimension

variable {k : Type u} [Field k]

/-- Let `P` be of finite type over a field. If `Z ⊆ P` is closed and irreducible and the open set
`W` meets `Z`, then `dim Z ≤ dim (Z ∩ W)`: with its reduced structure `Z` is an integral scheme of
finite type over `k`, and its nonempty opens have the same dimension (Exercise II.3.20). -/
theorem topologicalKrullDim_le_inter_of_isIrreducible {P : Scheme.{u}} (p : P ⟶ Spec (.of k))
    (hp : FiniteType p) {Z W : Set P} (hZ : IsClosed Z) (hZi : IsIrreducible Z) (hW : IsOpen W)
    (hne : (Z ∩ W).Nonempty) :
    topologicalKrullDim Z ≤ topologicalKrullDim (Z ∩ W : Set P) := by
  have := hp.1
  have := hp.2
  let Zc : Closeds P := ⟨Z, hZ⟩
  let ι := reducedInducedSubschemeι Zc
  have hrange : Set.range ι = Z := range_reducedInducedSubschemeι Zc
  have hemb : IsEmbedding ι := ι.isClosedEmbedding.isEmbedding
  have hdimR : topologicalKrullDim (reducedInducedSubscheme Zc) = topologicalKrullDim Z := by
    rw [← hrange]
    exact IsHomeomorph.topologicalKrullDim_eq _ hemb.toHomeomorph.isHomeomorph
  have : IrreducibleSpace (reducedInducedSubscheme Zc) := by
    have : IrreducibleSpace (Set.range ι) := by
      rw [hrange]
      exact Subtype.irreducibleSpace hZi
    exact (Homeomorph.irreducibleSpace_iff hemb.toHomeomorph).mpr this
  have : IsIntegral (reducedInducedSubscheme Zc) :=
    isIntegral_of_irreducibleSpace_of_isReduced _
  have hpR : FiniteType (ι ≫ p) := ⟨inferInstance, inferInstance⟩
  obtain ⟨m, hm, -⟩ := exists_topologicalKrullDim_eq_trdeg (ι ≫ p) hpR
  let U : (reducedInducedSubscheme Zc).Opens := ι ⁻¹ᵁ ⟨W, hW⟩
  obtain ⟨w, hwZ, hwW⟩ := hne
  obtain ⟨u, hu⟩ : w ∈ Set.range ι := hrange ▸ hwZ
  have : Nonempty U := ⟨⟨u, show ι u ∈ W from hu ▸ hwW⟩⟩
  have : IsIntegral (U : Scheme) := isIntegral_of_isOpenImmersion U.ι
  have hU := topologicalKrullDim_opens_eq (ι ≫ p) hpR hm U
  let g : U → (Z ∩ W : Set P) := fun v => ⟨ι v.1, hrange ▸ ⟨v.1, rfl⟩, v.2⟩
  have hg : IsInducing g := by
    have h1 : IsInducing (fun v : U => ι v.1) := hemb.isInducing.comp IsInducing.subtypeVal
    exact IsInducing.of_comp (f := g) (g := Subtype.val) (by fun_prop) continuous_subtype_val h1
  rw [← hdimR, hm, ← hU]
  exact hg.topologicalKrullDim_le

end Dimension

namespace BertiniIncidence

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### The universal hyperplane -/

section Universal

variable {k : Type u} [Field k] {n : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ projectiveSpaceOverScheme n (Spec (CommRingCat.of k)))

local notation "qφ" => φ ≫ projectiveSpaceOverSchemeProjection n (Spec (CommRingCat.of k))
local notation "hLφ" => isInvertible_pullback_projectiveSpaceTwistingSheaf φ

/-- On the chart `X_{sᵢ}` where `sᵢ` trivializes `L`, the section `∑ aⱼ sⱼ` lies in `𝔪_x L_x`
iff the function `∑ aⱼ (sⱼ / sᵢ)` vanishes at `x`. -/
theorem germ_linearSystemSection_mem_iff_chart (q : X ⟶ Spec (CommRingCat.of k)) {L : X.Modules}
    (hL : L.IsInvertible) (s : Fin (n + 1) → Γ(L, ⊤)) (i : Fin (n + 1)) {x : X}
    (hx : x ∈ nonvanishingLocusOpens hL (s i)) (a : Fin (n + 1) → k) :
    L.presheaf.germ ⊤ x trivial (linearSystemSection q s a) ∈
        maximalIdeal (X.presheaf.stalk x) •
          (⊤ : Submodule (X.presheaf.stalk x) (L.presheaf.stalk x)) ↔
      X.presheaf.germ _ x hx (∑ j, X.presheaf.map (homOfLE (le_top :
        nonvanishingLocusOpens hL (s i) ≤ ⊤)).op (kConst q (a j)) * sectionRatio hL s i j) ∈
        maximalIdeal (X.presheaf.stalk x) := by
  have hε := isTrivializingSection_nonvanishingLocusOpens hL (s i)
  have key : L.presheaf.map (homOfLE (le_top : nonvanishingLocusOpens hL (s i) ≤ ⊤)).op
      (linearSystemSection q s a) = (∑ j, X.presheaf.map (homOfLE (le_top :
        nonvanishingLocusOpens hL (s i) ≤ ⊤)).op (kConst q (a j)) * sectionRatio hL s i j) •
          L.presheaf.map (homOfLE le_top).op (s i) := by
    rw [linearSystemSection, map_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Scheme.Modules.map_smul, mul_smul, ← sectionRatio_spec]
  have hgerm : L.presheaf.germ ⊤ x trivial (linearSystemSection q s a) =
      X.presheaf.germ _ x hx (∑ j, X.presheaf.map (homOfLE (le_top :
        nonvanishingLocusOpens hL (s i) ≤ ⊤)).op (kConst q (a j)) * sectionRatio hL s i j) •
          L.presheaf.germ _ x hx (L.presheaf.map (homOfLE le_top).op (s i)) := by
    rw [← germ_smul_module, ← key, TopCat.Presheaf.germ_res_apply]
  rw [hgerm]
  exact smul_germ_mem_smul_top_iff hε hx _ _

/-- **Points of a hyperplane section on a coordinate chart.** On the open set `X_{sᵢ}` where the
pulled-back coordinate `sᵢ = φ^* xᵢ` does not vanish, a point `x` lies on `H_a ∩ X` exactly when
the function `∑ⱼ aⱼ (sⱼ / sᵢ)` vanishes at `x`. -/
theorem mem_support_hyperplaneSectionIdeal_iff_chart (i : Fin (n + 1)) {x : X}
    (hx : x ∈ nonvanishingLocusOpens (isInvertible_pullback_projectiveSpaceTwistingSheaf φ)
      (pulledBackCoordinates φ i)) (a : Fin (n + 1) → k) :
    x ∈ (hyperplaneSectionIdeal φ a).support ↔ X.presheaf.germ _ x hx
      (∑ j, X.presheaf.map (homOfLE le_top).op
          (kConst (φ ≫ projectiveSpaceOverSchemeProjection n _) (a j)) *
        sectionRatio (isInvertible_pullback_projectiveSpaceTwistingSheaf φ)
          (pulledBackCoordinates φ) i j) ∈ maximalIdeal (X.presheaf.stalk x) := by
  rw [hyperplaneSectionIdeal_eq, mem_support_invertibleZeroIdeal_iff,
    ← linearSystemSection_pulledBackCoordinates, nonvanishingLocus, Set.mem_ofPred_eq, not_not]
  exact germ_linearSystemSection_mem_iff_chart _ _ _ i hx a

/-- Every point of `X` lies on a chart `X_{sᵢ}` of the pulled-back coordinates. -/
theorem exists_mem_nonvanishingLocusOpens_pulledBackCoordinates (x : X) :
    ∃ i, x ∈ nonvanishingLocusOpens (isInvertible_pullback_projectiveSpaceTwistingSheaf φ)
      (pulledBackCoordinates φ i) := by
  obtain ⟨i, hi⟩ := exists_mem_chartPreimage φ x
  refine ⟨i, ?_⟩
  rw [← preimage_projectiveSpaceChart_eq_nonvanishingLocusOpens
    (isInvertible_pullback_projectiveSpaceTwistingSheaf φ) (pulledBackCoordinates φ) φ
    (Iso.refl _) (fun _ => rfl) i]
  exact hi

/-- A point `x` on the chart `X_{sᵢ}` does not lie on the coordinate hyperplane `xᵢ = 0`. -/
theorem notMem_support_hyperplaneSectionIdeal_single {i : Fin (n + 1)} {x : X}
    (hx : x ∈ nonvanishingLocusOpens (isInvertible_pullback_projectiveSpaceTwistingSheaf φ)
      (pulledBackCoordinates φ i)) :
    x ∉ (hyperplaneSectionIdeal φ (Pi.single i 1)).support := by
  rw [hyperplaneSectionIdeal_eq, mem_support_invertibleZeroIdeal_iff,
    ← linearSystemSection_pulledBackCoordinates, linearSystemSection_single, not_not]
  exact hx

/-- The universal hyperplane `{(x, H) : x ∈ H}` in `X ×_k (ℙⁿ_k)^∨`: on each chart
`X_{sᵢ} ×_k D₊(a_β)` it is cut out by the function `∑ⱼ (sⱼ / sᵢ) · a_j / a_β`. -/
def universalHyperplane : Set (incidenceAmbient (φ ≫ projectiveSpaceOverSchemeProjection n _) n) :=
  ⋂ (i : Fin (n + 1)) (β : Fin (n + 1)),
    ((incidenceAmbient (φ ≫ projectiveSpaceOverSchemeProjection n _) n).basicOpen
      (incidenceChartEquation (φ ≫ projectiveSpaceOverSchemeProjection n _)
        (r := 0) (fun _ j => sectionRatio (isInvertible_pullback_projectiveSpaceTwistingSheaf φ)
          (pulledBackCoordinates φ) i j) β 0) : Set _)ᶜ

theorem isClosed_universalHyperplane : IsClosed (universalHyperplane φ) :=
  isClosed_iInter fun _ => isClosed_iInter fun _ => (Opens.isOpen _).isClosed_compl

/-- **Points of the universal hyperplane.** If the image of `z` in `(ℙⁿ_k)^∨` represents the
nonzero vector `a`, then `z` lies on the universal hyperplane exactly when its image in `X` lies
on the hyperplane section `H_a ∩ X`. -/
theorem mem_universalHyperplane_iff {z : incidenceAmbient (φ ≫ projectiveSpaceOverSchemeProjection n _) n}
    {a : Fin (n + 1) → k} (ha : a ≠ 0)
    (hza : Represents a (pullback.snd _ (dualProjectiveSpaceStructure k n) z)) :
    z ∈ universalHyperplane φ ↔
      pullback.fst _ (dualProjectiveSpaceStructure k n) z ∈ (hyperplaneSectionIdeal φ a).support := by
  have hchart : ∀ i β (hz : z ∈ incidenceChart qφ (nonvanishingLocusOpens hLφ
      (pulledBackCoordinates φ i)) β),
      z ∈ chartIncidence qφ (r := 0) (fun _ j => sectionRatio hLφ (pulledBackCoordinates φ) i j) β ↔
        pullback.fst _ (dualProjectiveSpaceStructure k n) z ∈
          (hyperplaneSectionIdeal φ a).support := by
    intro i β hz
    rw [mem_chartIncidence_iff qφ _ β hz ha hza,
      mem_support_hyperplaneSectionIdeal_iff_chart φ i (incidenceChart_le_fst qφ _ β hz) a]
    exact ⟨fun h => h 0, fun h _ => h⟩
  constructor
  · intro hz
    obtain ⟨i, hi⟩ := exists_mem_nonvanishingLocusOpens_pulledBackCoordinates φ
      (pullback.fst _ (dualProjectiveSpaceStructure k n) z)
    obtain ⟨β, hβ⟩ := Function.ne_iff.mp ha
    have hzW : z ∈ incidenceChart qφ (nonvanishingLocusOpens hLφ (pulledBackCoordinates φ i)) β :=
      ⟨hi, (represents_mem_basicOpen_iff hza ha β).mpr hβ⟩
    refine (hchart i β hzW).mp ⟨hzW, ?_⟩
    simp only [Set.mem_iUnion, not_exists]
    intro ℓ
    rw [Fin.fin_one_eq_zero ℓ]
    exact Set.mem_iInter.mp (Set.mem_iInter.mp hz i) β
  · intro h
    refine Set.mem_iInter.mpr fun i => Set.mem_iInter.mpr fun β hzB => ?_
    have hzW : z ∈ incidenceChart qφ (nonvanishingLocusOpens hLφ (pulledBackCoordinates φ i)) β :=
      Scheme.basicOpen_le _ _ hzB
    exact ((hchart i β hzW).mpr h).2 (Set.mem_iUnion.mpr ⟨0, hzB⟩)

/-- The hyperplanes of `ℙⁿ_k` through the image of a point `x` of `X`, as a subset of
`(ℙⁿ_k)^∨`: the image of the fibre over `x` of the universal hyperplane. -/
def hyperplanesThrough (x : X) : Set (projectiveSpaceScheme k n) :=
  pullback.snd _ (dualProjectiveSpaceStructure k n) ''
    (universalHyperplane φ ∩ pullback.fst _ (dualProjectiveSpaceStructure k n) ⁻¹' {x})

/-- **The hyperplanes through a closed point form a proper closed subset of `(ℙⁿ_k)^∨`.**
Let `φ : X ⟶ ℙⁿ_k` be a closed immersion over an algebraically closed field `k` and `x` a closed
point of `X`. The set of hyperplanes containing `φ(x)` is closed in `(ℙⁿ_k)^∨`, is not all of
`(ℙⁿ_k)^∨`, and a closed point representing `a ≠ 0` lies in it iff `x ∈ H_a ∩ X`. -/
theorem hyperplanesThrough_spec [IsAlgClosed k] [IsClosedImmersion φ] (x : X) (hx : IsClosed {x}) :
    IsClosed (hyperplanesThrough φ x) ∧ hyperplanesThrough φ x ≠ Set.univ ∧
      ∀ H : projectiveSpaceScheme k n, IsClosed {H} → ∀ a : Fin (n + 1) → k, a ≠ 0 →
        Represents a H → (H ∈ hyperplanesThrough φ x ↔ x ∈ (hyperplaneSectionIdeal φ a).support) := by
  have : IsProper (projectiveSpaceOverSchemeProjection n (Spec (CommRingCat.of k))) :=
    projectiveSpaceOverSchemeProjection_isProper n _
  set q := φ ≫ projectiveSpaceOverSchemeProjection n (Spec (CommRingCat.of k))
  set g := dualProjectiveSpaceStructure k n
  have hmem : ∀ H : projectiveSpaceScheme k n, IsClosed {H} → ∀ a : Fin (n + 1) → k, a ≠ 0 →
      Represents a H → (H ∈ hyperplanesThrough φ x ↔ x ∈ (hyperplaneSectionIdeal φ a).support) := by
    intro H hH a ha hra
    constructor
    · rintro ⟨z, ⟨hzU, hzx⟩, rfl⟩
      have hzx : pullback.fst q g z = x := hzx
      rw [← hzx]
      exact (mem_universalHyperplane_iff φ ha hra).mp hzU
    · intro hxa
      obtain ⟨z, -, hzx, hzH⟩ := incidenceAmbient_exists_closedPoint_of_isClosed q x hx H hH
      refine ⟨z, ⟨(mem_universalHyperplane_iff φ ha (hzH ▸ hra)).mpr (hzx ▸ hxa), hzx⟩, hzH⟩
  refine ⟨isClosed_image_snd q _ ((isClosed_universalHyperplane φ).inter
    (hx.preimage (pullback.fst q g).continuous)), ?_, hmem⟩
  obtain ⟨i, hi⟩ := exists_mem_nonvanishingLocusOpens_pulledBackCoordinates φ x
  have h1 : (Pi.single i 1 : Fin (n + 1) → k) ≠ 0 := by
    intro h
    simpa using congrFun h i
  obtain ⟨H, hH, hra⟩ := exists_isClosed_represents (k := k) h1
  intro huniv
  exact notMem_support_hyperplaneSectionIdeal_single φ hi
    ((hmem H hH _ h1 hra).mp (huniv ▸ Set.mem_univ H))

/-! ### Avoiding finitely many points -/

/-- **Hyperplanes avoiding finitely many points.** Let `φ : X ⟶ ℙⁿ_k` be a closed immersion over
an algebraically closed field `k` and `S` a finite set of closed points of `X`. There is a dense
open subset `A` of `(ℙⁿ_k)^∨` whose closed points are exactly the hyperplanes `H_a` with
`x ∉ H_a ∩ X` for every `x ∈ S`. -/
theorem exists_isOpen_dense_avoiding [IsAlgClosed k] [IsClosedImmersion φ] {S : Set X}
    (hS : S.Finite) (hSc : ∀ x ∈ S, IsClosed {x}) :
    ∃ A : Set (projectiveSpaceScheme k n), IsOpen A ∧ Dense A ∧
      ∀ H : projectiveSpaceScheme k n, IsClosed {H} → ∀ a : Fin (n + 1) → k, a ≠ 0 →
        Represents a H → (H ∈ A ↔ ∀ x ∈ S, x ∉ (hyperplaneSectionIdeal φ a).support) := by
  have : IrreducibleSpace (projectiveSpaceScheme k n) :=
    projectiveSpace_irreducibleSpace (k := k) (n := n)
  have hcl : IsClosed (⋃ x ∈ S, hyperplanesThrough φ x) :=
    hS.isClosed_biUnion fun x hx => (hyperplanesThrough_spec φ x (hSc x hx)).1
  refine ⟨(⋃ x ∈ S, hyperplanesThrough φ x)ᶜ, hcl.isOpen_compl,
    hcl.isOpen_compl.dense (Set.nonempty_compl.mpr (biUnion_ne_univ_of_irreducibleSpace hS
      (fun x hx => (hyperplanesThrough_spec φ x (hSc x hx)).1)
      (fun x hx => (hyperplanesThrough_spec φ x (hSc x hx)).2.1))), fun H hH a ha hra => ?_⟩
  simp only [Set.mem_compl_iff, Set.mem_iUnion₂, not_exists]
  exact forall₂_congr fun x hx =>
    not_congr ((hyperplanesThrough_spec φ x (hSc x hx)).2.2 H hH a ha hra)

end Universal

end BertiniIncidence

end Hartshorne

namespace Hartshorne.BertiniIncidence

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] {n : ℕ}

/-- **Hyperplanes avoiding a finite set of points** (Hartshorne II, Remark 8.18.1). Let `k` be
algebraically closed and `S` a finite set of closed points of `ℙⁿ_k`. The hyperplanes avoiding
every point of `S` form a dense open subset of the dual projective space: there is a dense open
`A ⊆ (ℙⁿ_k)^∨` whose closed points are exactly the hyperplanes `H_a = {∑ aᵢ xᵢ = 0}` (the zero
schemes of the linear forms `∑ aᵢ xᵢ ∈ Γ(ℙⁿ_k, 𝒪(1))`, `a ≠ 0`) containing no point of `S`. -/
theorem hyperplanes_avoiding_finite_set_dense [IsAlgClosed k]
    {S : Set (projectiveSpaceOverScheme n (Spec (CommRingCat.of k)))} (hS : S.Finite)
    (hSc : ∀ P ∈ S, IsClosed {P}) :
    ∃ A : Set (projectiveSpaceScheme k n), IsOpen A ∧ Dense A ∧
      ∀ H : projectiveSpaceScheme k n, IsClosed {H} → ∀ a : Fin (n + 1) → k, a ≠ 0 →
        Represents a H →
        (H ∈ A ↔ ∀ P ∈ S, P ∉ (invertibleZeroIdeal (isInvertible_projectiveSpaceTwistingSheaf n _ 1)
          (linearSection k n a)).support) := by
  obtain ⟨A, hAo, hAd, hA⟩ := exists_isOpen_dense_avoiding
    (𝟙 (projectiveSpaceOverScheme n (Spec (CommRingCat.of k)))) hS hSc
  refine ⟨A, hAo, hAd, fun H hH a ha hra => ?_⟩
  rw [hA H hH a ha hra]
  simp only [hyperplaneSectionIdeal, Scheme.IdealSheafData.support_comap]
  rfl

/-- **Regular hyperplane sections avoiding finitely many points** (Hartshorne II, Theorem 8.18 and
Remark 8.18.1). Let `k` be algebraically closed, `φ : X ⟶ ℙⁿ_k` a closed immersion of a
nonsingular integral scheme, and `S` a finite set of closed points of `ℙⁿ_k`. There is a dense
open subset `U` of `(ℙⁿ_k)^∨` whose closed points are exactly the hyperplanes `H_a` containing no
point of `S`, not containing `X`, and with `H_a ∩ X` regular at every point. -/
theorem bertini_regular_hyperplane_section_avoiding [IsAlgClosed k] {X : Scheme.{u}}
    (φ : X ⟶ projectiveSpaceOverScheme n (Spec (CommRingCat.of k))) [IsClosedImmersion φ]
    [IsIntegral X] (hX : X.IsRegular)
    {S : Set (projectiveSpaceOverScheme n (Spec (CommRingCat.of k)))} (hS : S.Finite)
    (hSc : ∀ P ∈ S, IsClosed {P}) :
    ∃ U : Set (projectiveSpaceScheme k n), IsOpen U ∧ Dense U ∧
      ∀ H : projectiveSpaceScheme k n, IsClosed {H} → ∀ a : Fin (n + 1) → k, a ≠ 0 →
        Represents a H →
        (H ∈ U ↔ (∀ P ∈ S, P ∉ (invertibleZeroIdeal
            (isInvertible_projectiveSpaceTwistingSheaf n _ 1) (linearSection k n a)).support) ∧
          (∃ x : X, x ∉ (hyperplaneSectionIdeal φ a).support) ∧
          (hyperplaneSectionIdeal φ a).subscheme.IsRegular) := by
  obtain ⟨A, hAo, hAd, hA⟩ := hyperplanes_avoiding_finite_set_dense hS hSc
  obtain ⟨B, hBo, hBd, hB⟩ := bertini_regular_hyperplane_section φ hX
  refine ⟨A ∩ B, hAo.inter hBo, hAd.inter_of_isOpen_left hBd hAo, fun H hH a ha hra => ?_⟩
  rw [Set.mem_inter_iff, hA H hH a ha hra, hB H hH a ha hra]

end Hartshorne.BertiniIncidence

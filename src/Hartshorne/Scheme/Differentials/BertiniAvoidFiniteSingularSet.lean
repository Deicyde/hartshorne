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

/-! ### Local equations near regular points -/

/-- **The bad hyperplanes at a regular closed point.** Let `k` be algebraically closed and
`φ : X ⟶ ℙⁿ_k` a closed immersion of an integral scheme of dimension `r`. At a closed point `x`
where `X` is regular, the coefficient vectors of the bad hyperplanes form a subspace of `kⁿ⁺¹` of
dimension `n - r`. -/
theorem finrank_badHyperplaneSubspace_of_isRegularAt [IsAlgClosed k] [IsClosedImmersion φ]
    [IsIntegral X] {r : ℕ} (hr : topologicalKrullDim X = r) (x : X) (hx : IsClosed {x})
    (hreg : X.IsRegularAt x) :
    Module.finrank k (badHyperplaneSubspace φ x) = n - r := by
  have : IsProper (projectiveSpaceOverSchemeProjection n (Spec (CommRingCat.of k))) :=
    projectiveSpaceOverSchemeProjection_isProper n _
  have : IsRegularLocalRing (X.presheaf.stalk x) := hreg
  have hdim := dimension_at_closed_point (φ ≫ projectiveSpaceOverSchemeProjection n _)
    ⟨inferInstance, inferInstance⟩ x hx
  rw [hr] at hdim
  exact finrank_badSubspace _ (isInvertible_pullback_projectiveSpaceTwistingSheaf φ) _ φ rfl
    (Iso.refl _) (fun _ => rfl) x hx hdim.symm

/-- **Local equations for the bad hyperplanes near regular points.** Let `k` be algebraically
closed, `φ : X ⟶ ℙⁿ_k` a closed immersion of an integral scheme of dimension `r`, and `O ⊆ X` an
open set whose closed points are regular points of `X`. Every closed point `x₀ ∈ O` has an affine
neighbourhood `V ⊆ O` carrying functions `μ ℓ j` (`ℓ ≤ r`, `j ≤ n`) with an `(r + 1)`-minor
invertible on `V`, such that at every closed point `x ∈ V`, `a ∈ K_x` iff the `r + 1` functions
`∑ⱼ aⱼ μ ℓ j` all vanish at `x`. -/
theorem exists_local_incidence_equations_of_isOpen [IsAlgClosed k] [IsClosedImmersion φ]
    [IsIntegral X] {O : Set X} (hO : IsOpen O) (hreg : ∀ x ∈ O, IsClosed {x} → X.IsRegularAt x)
    {r : ℕ} (hr : topologicalKrullDim X = r) (x₀ : X) (hx₀O : x₀ ∈ O) (hx₀ : IsClosed {x₀}) :
    ∃ (V : X.Opens) (_ : IsAffineOpen V) (_ : x₀ ∈ V) (_ : (V : Set X) ⊆ O)
      (μ : Fin (r + 1) → Fin (n + 1) → Γ(X, V)) (J : Fin (r + 1) ↪ Fin (n + 1)),
      IsUnit (Matrix.det (Matrix.of fun ℓ ℓ' => μ ℓ (J ℓ'))) ∧
      ∀ (x : X) (hx : x ∈ V), IsClosed {x} → ∀ a : Fin (n + 1) → k,
        (a ∈ badHyperplaneSubspace φ x ↔
          ∀ ℓ, X.presheaf.germ V x hx (∑ j, X.presheaf.map (homOfLE le_top).op
            (kConst (φ ≫ projectiveSpaceOverSchemeProjection n _) (a j)) * μ ℓ j) ∈
            IsLocalRing.maximalIdeal (X.presheaf.stalk x)) := by
  classical
  have : IsProper (projectiveSpaceOverSchemeProjection n (Spec (CommRingCat.of k))) :=
    projectiveSpaceOverSchemeProjection_isProper n _
  set q := φ ≫ projectiveSpaceOverSchemeProjection n (Spec (CommRingCat.of k)) with hq
  have hL := isInvertible_pullback_projectiveSpaceTwistingSheaf φ
  set s := pulledBackCoordinates φ with hs
  obtain ⟨i, hi⟩ := exists_mem_chartPreimage φ x₀
  set U := nonvanishingLocusOpens hL (s i) with hU_def
  have hx₀U : x₀ ∈ U := by
    rw [hU_def, ← preimage_projectiveSpaceChart_eq_nonvanishingLocusOpens hL s φ (Iso.refl _)
      (fun _ => rfl) i]
    exact hi
  obtain ⟨hU, hsurj⟩ :=
    (isClosedImmersion_iff_isAffineOpen_and_surjective_chartSectionPolynomialMap hL s q φ
      (Iso.refl _) (fun _ => rfl) rfl).1 inferInstance i
  let : Algebra k Γ(X, U) :=
    ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.comp (kConst q)).toAlgebra
  have halg : ∀ c, algebraMap k Γ(X, U) c = X.presheaf.map (homOfLE le_top).op (kConst q c) :=
    fun _ => rfl
  let f : Fin (n + 1) → Γ(X, U) := sectionRatio hL s i
  have hgen : Algebra.adjoin k (Set.range f) = ⊤ := by
    rw [Algebra.adjoin_range_eq_range_aeval, eq_top_iff]
    rintro g -
    obtain ⟨P, rfl⟩ := hsurj g
    refine (AlgHom.mem_range _).2
      ⟨MvPolynomial.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom P, ?_⟩
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map, chartSectionPolynomialMap,
      MvPolynomial.coe_eval₂Hom]
    congr 1
    ext b
    change X.presheaf.map _ (q.appTop ((Scheme.ΓSpecIso _).inv ((Scheme.ΓSpecIso _).hom b))) = _
    rw [Iso.hom_inv_id_apply]
    rfl
  have : Algebra.FiniteType k Γ(X, U) :=
    ⟨⟨Finset.univ.image f, by rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, hgen]⟩⟩
  have hpt : ∀ (x : X) (hx : x ∈ U), x ∈ O → IsClosed {x} → ∃ ev : Γ(X, U) →ₐ[k] k,
      (∀ g, ev g = 0 ↔ X.presheaf.germ U x hx g ∈ maximalIdeal (X.presheaf.stalk x)) ∧
      (∀ g, X.presheaf.germ U x hx g ∈ maximalIdeal (X.presheaf.stalk x) ^ 2 ↔
        g ∈ RingHom.ker ev ^ 2) ∧
      Module.finrank k (Γ(X, U) ⧸ RingHom.ker ev ^ 2) = r + 1 := by
    intro x hx hxO hxc
    have : IsRegularLocalRing (X.presheaf.stalk x) := hreg x hxO hxc
    obtain ⟨ev, h1, h2, h3⟩ := incidence_exists_kPoint_chart q hU halg x hx hxc
    refine ⟨ev, h1, h2, ?_⟩
    have hdim := dimension_at_closed_point q ⟨inferInstance, inferInstance⟩ x hxc
    rw [hr] at hdim
    have h := (IsRegularLocalRing.iff_finrank_cotangentSpace (X.presheaf.stalk x)).mp
      inferInstance
    rw [← hdim] at h
    have h' : Module.finrank (ResidueField (X.presheaf.stalk x))
        (CotangentSpace (X.presheaf.stalk x)) = r := by exact_mod_cast h
    rw [h3, h']
  obtain ⟨ev₀, hev₀, -, hdim₀⟩ := hpt x₀ hx₀U hx₀O hx₀
  obtain ⟨J, μ, h, hh, hμ⟩ := exists_jetFrame_incidence_equations f ev₀
    (incidence_exists_sub_sum_mem_ker_sq f i (sectionRatio_self hL s i) hgen ev₀) hdim₀
  obtain ⟨g, hgO, hx₀g⟩ := hU.exists_basicOpen_le (V := ⟨O, hO⟩) ⟨x₀, hx₀O⟩ hx₀U
  set D := h * (Matrix.of fun ℓ ℓ' => μ ℓ (J ℓ')).det * g with hD
  have hEunit : ∀ (E : Γ(X, U)) (x : X) (hxU : x ∈ U) (ev : Γ(X, U) →ₐ[k] k),
      (∀ g, ev g = 0 ↔ X.presheaf.germ U x hxU g ∈ maximalIdeal (X.presheaf.stalk x)) →
      (x ∈ X.basicOpen E ↔ ev E ≠ 0) := by
    intro E x hxU ev hev
    rw [X.mem_basicOpen E x hxU, Ne, hev, notMem_maximalIdeal]
  have hg₀ : ev₀ g ≠ 0 := (hEunit g x₀ hx₀U ev₀ hev₀).1 hx₀g
  have hDO : (X.basicOpen D : Set X) ⊆ O := by
    intro x hx
    rw [hD, Scheme.basicOpen_mul] at hx
    exact hgO hx.2
  refine ⟨X.basicOpen D, hU.basicOpen D, (hEunit D x₀ hx₀U ev₀ hev₀).2 (by
      rw [hD, map_mul]; exact mul_ne_zero hh hg₀), hDO,
    fun ℓ j => X.presheaf.map (homOfLE (X.basicOpen_le D)).op (μ ℓ j), J, ?_, ?_⟩
  · have hdet : Matrix.det (Matrix.of fun ℓ ℓ' =>
        X.presheaf.map (homOfLE (X.basicOpen_le D)).op (μ ℓ (J ℓ'))) =
        X.presheaf.map (homOfLE (X.basicOpen_le D)).op (Matrix.of fun ℓ ℓ' => μ ℓ (J ℓ')).det := by
      rw [RingHom.map_det]
      rfl
    rw [hdet]
    have hu := X.toRingedSpace.isUnit_res_basicOpen D
    change IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le D)).op D) at hu
    rw [hD, map_mul, map_mul] at hu
    exact isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hu)
  · intro x hx hxc a
    have hxU : x ∈ U := X.basicOpen_le D hx
    have hxO : x ∈ O := hDO hx
    obtain ⟨ev, hev, hsq, -⟩ := hpt x hxU hxO hxc
    have hevD' := (hEunit D x hxU ev hev).1 hx
    rw [hD, map_mul, map_mul] at hevD'
    have hevD := left_ne_zero_of_mul hevD'
    have hgerm : ∀ ℓ, X.presheaf.germ (X.basicOpen D) x hx
        (∑ j, X.presheaf.map (homOfLE le_top).op (kConst q (a j)) *
          X.presheaf.map (homOfLE (X.basicOpen_le D)).op (μ ℓ j)) =
        X.presheaf.germ U x hxU (∑ j, algebraMap k _ (a j) * μ ℓ j) := by
      intro ℓ
      simp only [map_sum, map_mul, TopCat.Presheaf.germ_res_apply, halg]
    simp_rw [hgerm, ← hev]
    simp only [map_sum, map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
    refine incidence_mem_iff_of_minor (fun ℓ j => ev (μ ℓ j)) J ?_ _
      (finrank_badHyperplaneSubspace_of_isRegularAt φ hr x hxc (hreg x hxO hxc)) ?_ a
    · convert right_ne_zero_of_mul hevD using 1
      rw [AlgHom.map_det]
      rfl
    · intro b hb
      rw [badHyperplaneSubspace, incidence_mem_badSubspace_iff_chart q hL s i halg x hxU, hsq]
      exact hμ ev (left_ne_zero_of_mul hevD) b hb

/-! ### The incidence correspondence over the regular points -/

/-- A hyperplane bad at `x` passes through `x`. -/
theorem mem_support_of_isBadHyperplaneAt {a : Fin (n + 1) → k} {x : X}
    (h : IsBadHyperplaneAt φ a x) : x ∈ (hyperplaneSectionIdeal φ a).support := by
  rcases h with h | ⟨z, rfl, -⟩
  · exact h x
  · change _ ∈ ((hyperplaneSectionIdeal φ a).support : Set X)
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨z, rfl⟩

/-- **The bad-hyperplane incidence over an open set of regular points.** Let `k` be algebraically
closed, `φ : X ⟶ ℙⁿ_k` a closed immersion of an integral scheme of dimension `r < n`, and `O ⊆ X`
an open set whose closed points are regular points of `X`. There is a closed subset `Z` of
`X ×_k (ℙⁿ_k)^∨` of dimension at most `n - 1`, contained in the universal hyperplane, whose
closed points over `O` are exactly the pairs `(x, H_a)` with `H_a` bad at `x`. Here `Z` is the
closure of these pairs; on the charts over `O` it is computed by local equations, it is
irreducible, and its dimension is that of its trace over `O`. -/
theorem bertini_bad_hyperplane_incidence_of_isOpen [IsAlgClosed k] [IsClosedImmersion φ]
    [IsIntegral X] {O : Set X} (hO : IsOpen O) (hreg : ∀ x ∈ O, IsClosed {x} → X.IsRegularAt x)
    {r : ℕ} (hr : topologicalKrullDim X = r) (hrn : r < n) :
    ∃ Z : Set (incidenceAmbient (φ ≫ projectiveSpaceOverSchemeProjection n _) n),
      IsClosed Z ∧ Z ⊆ universalHyperplane φ ∧
      topologicalKrullDim Z ≤ ((n - 1 : ℕ) : WithBot ℕ∞) ∧
      ∀ z, IsClosed {z} → pullback.fst _ (dualProjectiveSpaceStructure k n) z ∈ O →
        ∀ a : Fin (n + 1) → k, a ≠ 0 →
        Represents a (pullback.snd _ (dualProjectiveSpaceStructure k n) z) →
        (z ∈ Z ↔
          IsBadHyperplaneAt φ a (pullback.fst _ (dualProjectiveSpaceStructure k n) z)) := by
  classical
  have : IsProper (projectiveSpaceOverSchemeProjection n (Spec (CommRingCat.of k))) :=
    projectiveSpaceOverSchemeProjection_isProper n _
  have hqft : FiniteType (qφ) := ⟨inferInstance, inferInstance⟩
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (qφ)
  have : JacobsonSpace (incidenceAmbient (qφ) n) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.fst (qφ) (dualProjectiveSpaceStructure k n) ≫ qφ)
  set q := φ ≫ projectiveSpaceOverSchemeProjection n (Spec (CommRingCat.of k)) with hq_def
  set P := incidenceAmbient q n
  set fst := pullback.fst q (dualProjectiveSpaceStructure k n)
  set snd := pullback.snd q (dualProjectiveSpaceStructure k n)
  set K := badHyperplaneSubspace φ
  have hfO : IsOpen (fst ⁻¹' O) := hO.preimage fst.continuous
  -- local equations near each closed point of `O`
  choose V hV hxV hVO μ J hdet hiff using fun (x₀ : X) (h₀O : x₀ ∈ O) (h₀ : IsClosed {x₀}) =>
    exists_local_incidence_equations_of_isOpen φ hO hreg hr x₀ h₀O h₀
  set B := incidencePoints φ ∩ fst ⁻¹' O
  set Z := closure B
  -- the closure of `B` on a chart
  have hchart : ∀ x₀ h₀O h₀ β,
      Z ∩ (incidenceChart q (V x₀ h₀O h₀) β : Set P) = chartIncidence q (μ x₀ h₀O h₀) β := by
    intro x₀ h₀O h₀ β
    set W := incidenceChart q (V x₀ h₀O h₀) β
    have hWO : ∀ z ∈ W, fst z ∈ O := fun z hz => hVO x₀ h₀O h₀ (incidenceChart_le_fst q _ β hz)
    have hpt : ∀ z ∈ W, IsClosed {z} → (z ∈ B ↔ z ∈ chartIncidence q (μ x₀ h₀O h₀) β) := by
      intro z hzW hz
      obtain ⟨hfz, -, a, ha, hra⟩ := incidenceAmbient_closedPoint q z hz
      constructor
      · rintro ⟨⟨-, a', ha', hra', hK⟩, -⟩
        rw [mem_chartIncidence_iff q (μ x₀ h₀O h₀) β hzW ha' hra']
        exact (hiff x₀ h₀O h₀ (fst z) (incidenceChart_le_fst q _ β hzW) hfz a').mp hK
      · intro hC
        exact ⟨⟨hz, a, ha, hra, (hiff x₀ h₀O h₀ (fst z) (incidenceChart_le_fst q _ β hzW) hfz
          a).mpr ((mem_chartIncidence_iff q (μ x₀ h₀O h₀) β hzW ha hra).mp hC)⟩, hWO z hzW⟩
    set U := ⋃ ℓ, (P.basicOpen (incidenceChartEquation q (μ x₀ h₀O h₀) β ℓ) : Set P)
    have hU : IsOpen U := isOpen_iUnion fun ℓ => (P.basicOpen _).isOpen
    have hC : chartIncidence q (μ x₀ h₀O h₀) β = (W : Set P) ∩ Uᶜ := Set.sdiff_eq _ _
    apply le_antisymm
    · rintro z ⟨hzZ, hzW⟩
      refine ⟨hzW, fun hzU => ?_⟩
      obtain ⟨b, ⟨hbU, hbW⟩, hbB⟩ := mem_closure_iff.mp hzZ _ (hU.inter W.isOpen) ⟨hzU, hzW⟩
      have := (hpt b hbW hbB.1.1).mp hbB
      rw [hC] at this
      exact this.2 hbU
    · intro z hz
      refine ⟨?_, (hC ▸ hz).1⟩
      have hlc : IsLocallyClosed (chartIncidence q (μ x₀ h₀O h₀) β) := by
        rw [hC]; exact W.isOpen.isLocallyClosed.inter hU.isClosed_compl.isLocallyClosed
      have hsub : chartIncidence q (μ x₀ h₀O h₀) β ∩ closedPoints P ⊆ B := fun w ⟨hwC, hwc⟩ =>
        (hpt w (hC ▸ hwC).1 hwc).mpr hwC
      have : z ∈ closure (chartIncidence q (μ x₀ h₀O h₀) β) := subset_closure hz
      rw [← JacobsonSpace.closure_inter_closedPoints_eq_closure hlc] at this
      exact closure_mono hsub this
  -- membership of a closed point over `O`
  have hmem : ∀ z, IsClosed {z} → fst z ∈ O → ∀ a : Fin (n + 1) → k, a ≠ 0 →
      Represents a (snd z) → (z ∈ Z ↔ a ∈ K (fst z)) := by
    intro z hz hzO a ha hra
    refine ⟨fun hzZ => ?_, fun hK => subset_closure ⟨⟨hz, a, ha, hra, hK⟩, hzO⟩⟩
    obtain ⟨hfz, -, -⟩ := incidenceAmbient_closedPoint q z hz
    obtain ⟨β, hβ⟩ := Function.ne_iff.mp ha
    have hzW : z ∈ incidenceChart q (V (fst z) hzO hfz) β :=
      ⟨hxV _ hzO hfz, (represents_mem_basicOpen_iff hra ha β).mpr hβ⟩
    have hzC : z ∈ chartIncidence q (μ (fst z) hzO hfz) β := hchart _ hzO hfz β ▸ ⟨hzZ, hzW⟩
    exact (hiff _ hzO hfz (fst z) (hxV _ hzO hfz) hfz a).mpr
      ((mem_chartIncidence_iff q _ β hzW ha hra).mp hzC)
  -- `Z` lies on the universal hyperplane
  have hZU : Z ⊆ universalHyperplane φ := by
    refine closure_minimal ?_ (isClosed_universalHyperplane φ)
    rintro z ⟨⟨hz, a, ha, hra, hK⟩, hzO⟩
    obtain ⟨hfz, -, -⟩ := incidenceAmbient_closedPoint q z hz
    have : IsRegularLocalRing (X.presheaf.stalk (fst z)) := hreg _ hzO hfz
    exact (mem_universalHyperplane_iff φ ha hra).mpr
      (mem_support_of_isBadHyperplaneAt φ ((mem_badHyperplaneSubspace_iff φ (fst z) a).mp hK))
  -- the bad subspace has vectors with a prescribed coordinate outside `J` nonzero
  have hcardJ : ∀ x₀ h₀O h₀, Fintype.card {j // j ∉ Set.range (J x₀ h₀O h₀)} = n - r := by
    intro x₀ h₀O h₀
    rw [Fintype.card_subtype_compl, Set.card_range_of_injective (J x₀ h₀O h₀).injective,
      Fintype.card_fin, Fintype.card_fin]
    omega
  have hexists : ∀ x₀ h₀O h₀ β, β ∉ Set.range (J x₀ h₀O h₀) →
      ∀ x (hx : x ∈ V x₀ h₀O h₀), IsClosed {x} → ∃ a ∈ K x, a β ≠ 0 := by
    intro x₀ h₀O h₀ β hβ x hx hxc
    let ρ : K x →ₗ[k] ({j // j ∉ Set.range (J x₀ h₀O h₀)} → k) :=
      (LinearMap.funLeft k k Subtype.val).comp (K x).subtype
    have hinj : Function.Injective ρ := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro a ha
      apply Subtype.ext
      refine eq_zero_of_local_equations φ (μ x₀ h₀O h₀) (J x₀ h₀O h₀) (hdet x₀ h₀O h₀) hx
        ((hiff x₀ h₀O h₀ x hx hxc a).mp a.2) fun j hj => ?_
      exact congrFun ha ⟨j, hj⟩
    have hsurj : Function.Surjective ρ := by
      refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj
      rw [finrank_badHyperplaneSubspace_of_isRegularAt φ hr x hxc
          (hreg x (hVO x₀ h₀O h₀ hx) hxc), Module.finrank_fintype_fun_eq_card, hcardJ]
    obtain ⟨a, ha⟩ := hsurj (Pi.single ⟨β, hβ⟩ 1)
    refine ⟨a, a.2, ?_⟩
    have := congrFun ha ⟨β, hβ⟩
    simp only [Pi.single_eq_same] at this
    change (a : Fin (n + 1) → k) β = 1 at this
    rw [this]
    exact one_ne_zero
  -- the charts
  let ι := Σ' (x₀ : X) (h₀O : x₀ ∈ O) (h₀ : IsClosed {x₀}) (β : Fin (n + 1)),
    β ∉ Set.range (J x₀ h₀O h₀)
  let W : ι → Set P := fun i => incidenceChart q (V i.1 i.2.1 i.2.2.1) i.2.2.2.1
  have hWopen : ∀ i, IsOpen (W i) := fun i => (incidenceChart q _ _).isOpen
  set Z' := Z ∩ fst ⁻¹' O
  have hZ'W : ∀ i, Z' ∩ W i = Z ∩ W i := by
    intro i
    ext z
    refine ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, ?_⟩, h.2⟩⟩
    exact hVO _ _ _ (incidenceChart_le_fst q _ _ h.2)
  have hpiece : ∀ i, IsIrreducible (Z' ∩ W i) ∧
      topologicalKrullDim (Z' ∩ W i : Set P) = ((n - 1 : ℕ) : WithBot ℕ∞) := by
    intro i
    rw [hZ'W]
    obtain ⟨x₀, h₀O, h₀, β, hβ⟩ := i
    have : Nonempty (V x₀ h₀O h₀) := ⟨⟨x₀, hxV x₀ h₀O h₀⟩⟩
    change IsIrreducible (Z ∩ (incidenceChart q (V x₀ h₀O h₀) β : Set P)) ∧ _
    rw [hchart x₀ h₀O h₀ β]
    exact chartIncidence_isIrreducible_and_topologicalKrullDim q (μ x₀ h₀O h₀) β hqft
      (hV x₀ h₀O h₀) hr hrn (J x₀ h₀O h₀) (hdet x₀ h₀O h₀) hβ
  -- a closed point of `Z` over `O` lies in a chart
  have hcovc : ∀ z ∈ Z, fst z ∈ O → IsClosed {z} → ∃ i, z ∈ W i := by
    intro z hzZ hzO hz
    obtain ⟨hfz, -, a, ha, hra⟩ := incidenceAmbient_closedPoint q z hz
    have hK := (hmem z hz hzO a ha hra).mp hzZ
    have hloc := (hiff _ hzO hfz (fst z) (hxV _ hzO hfz) hfz a).mp hK
    obtain ⟨β, hβJ, hβ⟩ : ∃ β, β ∉ Set.range (J _ hzO hfz) ∧ a β ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact ha (eq_zero_of_local_equations φ (μ _ hzO hfz) (J _ hzO hfz) (hdet _ hzO hfz)
        (hxV _ hzO hfz) hloc hcon)
    exact ⟨⟨fst z, hzO, hfz, β, hβJ⟩, hxV _ hzO hfz, (represents_mem_basicOpen_iff hra ha β).mpr hβ⟩
  have hcov : Z' ⊆ ⋃ i, W i := by
    rintro z ⟨hzZ, hzO⟩
    obtain ⟨z', ⟨hz'z, hz'O⟩, hz'c⟩ := nonempty_inter_closedPoints
      (Z := closure {z} ∩ fst ⁻¹' O) ⟨z, subset_closure rfl, hzO⟩
      (isClosed_closure.isLocallyClosed.inter hfO.isLocallyClosed)
    have hz'Z : z' ∈ Z := closure_minimal (Set.singleton_subset_iff.mpr hzZ) isClosed_closure hz'z
    obtain ⟨i, hi⟩ := hcovc z' hz'Z hz'O hz'c
    obtain ⟨w, hw, rfl⟩ := mem_closure_iff.mp hz'z _ (hWopen i) hi
    exact Set.mem_iUnion.mpr ⟨i, hw⟩
  -- a closed point of `B` over a closed point `x`, in two prescribed charts
  have hmeet : ∀ i j, (Z' ∩ W i ∩ W j).Nonempty := by
    rintro ⟨x₀, h₀O, h₀, β, hβ⟩ ⟨x₁, h₁O, h₁, γ, hγ⟩
    obtain ⟨y, hy0, hy1⟩ := nonempty_preirreducible_inter (V x₀ h₀O h₀).isOpen
      (V x₁ h₁O h₁).isOpen ⟨x₀, hxV x₀ h₀O h₀⟩ ⟨x₁, hxV x₁ h₁O h₁⟩
    obtain ⟨x, ⟨hx0, hx1⟩, hxc⟩ := nonempty_inter_closedPoints (X := X)
      (Z := (V x₀ h₀O h₀ : Set X) ∩ V x₁ h₁O h₁) ⟨y, hy0, hy1⟩
      ((V x₀ h₀O h₀).isOpen.inter (V x₁ h₁O h₁).isOpen).isLocallyClosed
    obtain ⟨u, hu, huβ⟩ := hexists x₀ h₀O h₀ β hβ x hx0 hxc
    obtain ⟨v, hv, hvγ⟩ := hexists x₁ h₁O h₁ γ hγ x hx1 hxc
    obtain ⟨w, hw, hwβ, hwγ⟩ : ∃ w ∈ K x, w β ≠ 0 ∧ w γ ≠ 0 := by
      by_cases huγ : u γ ≠ 0
      · exact ⟨u, hu, huβ, huγ⟩
      by_cases hvβ : v β ≠ 0
      · exact ⟨v, hv, hvβ, hvγ⟩
      push Not at huγ hvβ
      refine ⟨u + v, add_mem hu hv, ?_, ?_⟩
      · simpa [hvβ] using huβ
      · simpa [huγ] using hvγ
    have hw0 : w ≠ 0 := fun h => hwβ (by rw [h, Pi.zero_apply])
    obtain ⟨z, hz, hzx, hzr⟩ := incidenceAmbient_exists_closedPoint q x hxc hw0
    have hzO : fst z ∈ O := by rw [hzx]; exact hVO x₀ h₀O h₀ hx0
    have hzB : z ∈ B := ⟨⟨hz, w, hw0, hzr, by rw [hzx]; exact hw⟩, hzO⟩
    refine ⟨z, ⟨⟨subset_closure hzB, hzO⟩, ?_⟩, ?_⟩
    · exact ⟨show fst z ∈ V x₀ h₀O h₀ by rw [hzx]; exact hx0,
        (represents_mem_basicOpen_iff hzr hw0 β).mpr hwβ⟩
    · exact ⟨show fst z ∈ V x₁ h₁O h₁ by rw [hzx]; exact hx1,
        (represents_mem_basicOpen_iff hzr hw0 γ).mpr hwγ⟩
  refine ⟨Z, isClosed_closure, hZU, ?_, fun z hz hzO a ha hra => ?_⟩
  · rcases Z'.eq_empty_or_nonempty with hZ'e | hZ'ne
    · have hZe : Z = ∅ := by
        have hB : B = ∅ := Set.eq_empty_of_subset_empty fun z hz =>
          hZ'e ▸ ⟨subset_closure hz, hz.2⟩
        change closure B = ∅
        rw [hB, closure_empty]
      rw [hZe]
      have : IsEmpty (IrreducibleCloseds (∅ : Set P)) :=
        ⟨fun T => by obtain ⟨⟨x, hx⟩, -⟩ := T.isIrreducible.nonempty; exact hx⟩
      rw [topologicalKrullDim, Order.krullDim_eq_bot]
      exact bot_le
    · have hZ'irr : IsIrreducible Z' :=
        isIrreducible_of_isOpen_cover W hWopen hcov (fun i _ => (hpiece i).1)
          (fun i j _ _ => hmeet i j) hZ'ne
      have hZcl : closure Z' = Z := by
        refine le_antisymm (closure_minimal Set.inter_subset_left isClosed_closure) ?_
        exact closure_mono fun z hz => ⟨subset_closure hz, hz.2⟩
      have hZirr : IsIrreducible Z := hZcl ▸ hZ'irr.closure
      refine (topologicalKrullDim_le_inter_of_isIrreducible (fst ≫ q) ⟨inferInstance,
        inferInstance⟩ isClosed_closure hZirr hfO hZ'ne).trans ?_
      refine BaseExtensionComponentDimension.topologicalKrullDim_le_of_forall_isOpenEmbedding _
        fun y => ?_
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov y.2)
      refine ⟨(Z' ∩ W i : Set P), inferInstance, Set.inclusion Set.inter_subset_left,
        isOpenEmbedding_inclusion_inter (hWopen i), ⟨⟨y.1, y.2, hi⟩, rfl⟩, (hpiece i).2.le⟩
  · obtain ⟨hfz, -, -⟩ := incidenceAmbient_closedPoint q z hz
    have : IsRegularLocalRing (X.presheaf.stalk (fst z)) := hreg _ hzO hfz
    rw [hmem z hz hzO a ha hra]
    exact mem_badHyperplaneSubspace_iff φ (fst z) a

/-! ### Good hyperplanes on a scheme with finitely many singular points -/

/-- Let `X` be a nonempty locally Noetherian scheme with a closed immersion `φ : X ⟶ ℙⁿ_k`. The
hyperplane `H_a` is bad at no closed point of `X` exactly when it does not contain `X` and
`H_a ∩ X` is regular: singular points of `H_a ∩ X` specialize to closed singular points. -/
theorem forall_not_isBadHyperplaneAt_iff_of_isLocallyNoetherian [IsClosedImmersion φ] [Nonempty X]
    [IsLocallyNoetherian X] (a : Fin (n + 1) → k) :
    (∀ x : X, IsClosed {x} → ¬ IsBadHyperplaneAt φ a x) ↔
      (∃ x : X, x ∉ (hyperplaneSectionIdeal φ a).support) ∧
        (hyperplaneSectionIdeal φ a).subscheme.IsRegular := by
  have : IsProper (projectiveSpaceOverSchemeProjection n (Spec (CommRingCat.of k))) :=
    projectiveSpaceOverSchemeProjection_isProper n _
  set I := hyperplaneSectionIdeal φ a
  constructor
  · intro h
    have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (qφ)
    have : JacobsonSpace I.subscheme := LocallyOfFiniteType.jacobsonSpace (I.subschemeι ≫ qφ)
    obtain ⟨x₀, -, hx₀⟩ := nonempty_inter_closedPoints (X := X) (Z := Set.univ)
      Set.univ_nonempty isClosed_univ.isLocallyClosed
    refine ⟨?_, LocallyOfFiniteType.isLocallyNoetherian I.subschemeι, fun y => ?_⟩
    · by_contra hcon
      push Not at hcon
      exact h x₀ hx₀ (Or.inl hcon)
    obtain ⟨y', hy'y, hy'c⟩ := nonempty_inter_closedPoints (Set.singleton_nonempty y).closure
      isClosed_closure.isLocallyClosed
    refine isRegularAt_of_specializes (specializes_iff_mem_closure.mpr hy'y) ?_
    have hxc : IsClosed {I.subschemeι y'} := by
      rw [← Set.image_singleton]
      exact I.subschemeι.isClosedEmbedding.isClosedMap _ hy'c
    by_contra hreg
    exact h _ hxc (Or.inr ⟨y', rfl, hreg⟩)
  · rintro ⟨⟨y, hy⟩, hreg⟩ x - (h | ⟨z, -, hz⟩)
    · exact hy (h y)
    · exact hz (hreg.2 z)

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

/-- **Bertini's theorem with finitely many singular points** (Hartshorne II, Remark 8.18.1). Let
`k` be algebraically closed and `φ : X ⟶ ℙⁿ_k` a closed immersion of an integral scheme, so that
`X` is a projective variety, and suppose `X` has only finitely many singular closed points. Then
there is a dense open subset `U` of `(ℙⁿ_k)^∨` whose closed points are exactly the hyperplanes
`H_a` (`a ≠ 0`) that contain none of the singular closed points of `X`, do not contain `X`, and
for which the hyperplane section `H_a ∩ X` is regular at every point. -/
theorem bertini_avoid_finite_singular_set [IsAlgClosed k] {X : Scheme.{u}}
    (φ : X ⟶ projectiveSpaceOverScheme n (Spec (CommRingCat.of k))) [IsClosedImmersion φ]
    [IsIntegral X] (hS : {x : X | IsClosed {x} ∧ ¬ X.IsRegularAt x}.Finite) :
    ∃ U : Set (projectiveSpaceScheme k n), IsOpen U ∧ Dense U ∧
      ∀ H : projectiveSpaceScheme k n, IsClosed {H} → ∀ a : Fin (n + 1) → k, a ≠ 0 →
        Represents a H →
        (H ∈ U ↔ (∀ x : X, IsClosed {x} → ¬ X.IsRegularAt x →
            x ∉ (hyperplaneSectionIdeal φ a).support) ∧
          (∃ x : X, x ∉ (hyperplaneSectionIdeal φ a).support) ∧
          (hyperplaneSectionIdeal φ a).subscheme.IsRegular) := by
  classical
  have : IsProper (projectiveSpaceOverSchemeProjection n (Spec (CommRingCat.of k))) :=
    projectiveSpaceOverSchemeProjection_isProper n _
  set q := φ ≫ projectiveSpaceOverSchemeProjection n (Spec (CommRingCat.of k))
  set g := dualProjectiveSpaceStructure k n
  have : JacobsonSpace (incidenceAmbient q n) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.fst q g ≫ q)
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian q
  have : IrreducibleSpace (projectiveSpaceScheme k n) :=
    projectiveSpace_irreducibleSpace (k := k) (n := n)
  set S := {x : X | IsClosed {x} ∧ ¬ X.IsRegularAt x}
  have hSc : ∀ x ∈ S, IsClosed {x} := fun x hx => hx.1
  have hSclosed : IsClosed S := by
    have := hS.isClosed_biUnion fun x hx => hSc x hx
    rwa [Set.biUnion_of_singleton] at this
  have hreg : ∀ x ∈ Sᶜ, IsClosed {x} → X.IsRegularAt x := by
    intro x hx hxc
    by_contra h
    exact hx ⟨hxc, h⟩
  obtain ⟨A, hAo, hAd, hA⟩ := exists_isOpen_dense_avoiding φ hS hSc
  -- for hyperplanes avoiding `S`, goodness only needs to be checked at closed points off `S`
  have key : ∀ a : Fin (n + 1) → k, (∀ x ∈ S, x ∉ (hyperplaneSectionIdeal φ a).support) →
      ((∃ x : X, x ∉ (hyperplaneSectionIdeal φ a).support) ∧
        (hyperplaneSectionIdeal φ a).subscheme.IsRegular ↔
      ∀ x : X, IsClosed {x} → x ∈ Sᶜ → ¬ IsBadHyperplaneAt φ a x) := by
    intro a havoid
    rw [← forall_not_isBadHyperplaneAt_iff_of_isLocallyNoetherian]
    refine ⟨fun h x hx _ => h x hx, fun h x hx hbad => ?_⟩
    by_cases hxS : x ∈ S
    · exact havoid x hxS (mem_support_of_isBadHyperplaneAt φ hbad)
    · exact h x hx hxS hbad
  have havoid_iff : ∀ a : Fin (n + 1) → k, (∀ x : X, IsClosed {x} → ¬ X.IsRegularAt x →
      x ∉ (hyperplaneSectionIdeal φ a).support) ↔
        ∀ x ∈ S, x ∉ (hyperplaneSectionIdeal φ a).support :=
    fun a => ⟨fun h x hx => h x hx.1 hx.2, fun h x hx hreg => h x ⟨hx, hreg⟩⟩
  obtain ⟨r, hr, -⟩ := exists_topologicalKrullDim_eq_trdeg q ⟨inferInstance, inferInstance⟩
  rcases lt_or_ge r n with hrn | hnr
  · obtain ⟨Z, hZc, hZU, hZdim, hZmem⟩ :=
      bertini_bad_hyperplane_incidence_of_isOpen φ hSclosed.isOpen_compl hreg hr hrn
    set T := pullback.snd q g '' Z
    have hTc : IsClosed T := isClosed_image_snd q Z hZc
    have hTdim : topologicalKrullDim T ≤ ((n - 1 : ℕ) : WithBot ℕ∞) :=
      (topologicalKrullDim_image_le (pullback.snd q g).continuous hZc
        fun C hC _ => isClosed_image_snd q C hC).trans hZdim
    have hTne : T ≠ Set.univ := by
      intro hT
      have hdim : topologicalKrullDim (Set.univ : Set (projectiveSpaceScheme k n)) = n := by
        rw [IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ _).isHomeomorph]
        exact topologicalKrullDim_projectiveSpace
      rw [hT, hdim] at hTdim
      have : n ≤ n - 1 := by exact_mod_cast hTdim
      omega
    have hTd : Dense Tᶜ := hTc.isOpen_compl.dense (Set.nonempty_compl.mpr hTne)
    refine ⟨Tᶜ ∩ A, hTc.isOpen_compl.inter hAo, hTd.inter_of_isOpen_left hAd hTc.isOpen_compl,
      fun H hH a ha hra => ?_⟩
    rw [Set.mem_inter_iff, hA H hH a ha hra, havoid_iff]
    constructor
    · rintro ⟨hT, havoid⟩
      refine ⟨havoid, (key a havoid).mpr fun x hx hxO hbad => hT ?_⟩
      obtain ⟨z, hzc, hzx, hzH⟩ := incidenceAmbient_exists_closedPoint_of_isClosed q x hx H hH
      exact ⟨z, (hZmem z hzc (hzx ▸ hxO) a ha (hzH ▸ hra)).mpr (hzx ▸ hbad), hzH⟩
    · rintro ⟨havoid, hgood⟩
      refine ⟨?_, havoid⟩
      rintro ⟨z₀, hz₀, hz₀H⟩
      obtain ⟨z, ⟨hzZ, hzH⟩, hzc⟩ := nonempty_inter_closedPoints (X := incidenceAmbient q n)
        (Z := Z ∩ pullback.snd q g ⁻¹' {H}) ⟨z₀, hz₀, hz₀H⟩
        (hZc.inter (hH.preimage (pullback.snd q g).continuous)).isLocallyClosed
      have hzH : pullback.snd q g z = H := hzH
      have hfz := (incidenceAmbient_closedPoint q z hzc).1
      by_cases hxS : pullback.fst q g z ∈ S
      · exact havoid _ hxS ((mem_universalHyperplane_iff φ ha (hzH ▸ hra)).mp (hZU hzZ))
      · exact (key a havoid).mp hgood _ hfz hxS
          ((hZmem z hzc hxS a ha (hzH ▸ hra)).mp hzZ)
  · refine ⟨A, hAo, hAd, fun H hH a ha hra => ?_⟩
    rw [hA H hH a ha hra, havoid_iff]
    refine ⟨fun havoid => ⟨havoid, (key a havoid).mpr fun x hx hxO hbad => ?_⟩, fun h => h.1⟩
    have : IsRegularLocalRing (X.presheaf.stalk x) := hreg x hxO hx
    have hmem := (mem_badHyperplaneSubspace_iff φ x a).mpr hbad
    have hfin := finrank_badHyperplaneSubspace_of_isRegularAt φ hr x hx (hreg x hxO hx)
    rw [Nat.sub_eq_zero_of_le hnr, Submodule.finrank_eq_zero] at hfin
    rw [hfin] at hmem
    exact ha ((Submodule.mem_bot k).mp hmem)

end Hartshorne.BertiniIncidence

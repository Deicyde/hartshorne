/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.Differentials.BertiniIncidenceLocalEquations
import Hartshorne.Scheme.Differentials.BertiniIncidenceChart
import Hartshorne.Scheme.BaseExtensionComponentDimension

/-!
# The bad-hyperplane incidence correspondence

Hartshorne, *Algebraic Geometry*, II.8, proof of Theorem 8.18 (pp. 179–180).

Let `k` be algebraically closed and `X ⊆ ℙⁿ_k` a nonsingular closed subvariety of dimension
`r < n`. For a closed point `x ∈ X`, the hyperplanes `H` which contain `X`, or for which `H ∩ X`
is not regular at `x`, form the projective linear subspace `B_x = ℙ(K_x)` of `|H| = (ℙⁿ_k)^∨`,
where `K_x ⊆ kⁿ⁺¹` is a subspace of dimension `n - r`. The set of pairs `(x, H)` with `H ∈ B_x`
is the set of closed points of a closed irreducible subset of `X ×_k (ℙⁿ_k)^∨` of dimension
`n - 1`.

## Proof

The incidence set `B` of closed points is the closure of its closed points intersected with each
chart. Near a closed point `x₀`, the subspaces `K_x` are the kernels of `r + 1` linear forms whose
coefficients are regular functions on an affine neighbourhood `V` and which have an invertible
`(r + 1)`-minor with columns `J` (`exists_local_incidence_equations`). On the chart
`V ×_k D₊(a_β)` the closure `Z` of `B` is therefore the common zero locus of these forms
(`chartIncidence`), and for `β ∉ J` that locus is irreducible of dimension `n - 1`
(`chartIncidence_isIrreducible_and_topologicalKrullDim`). These charts cover `Z`: the coordinates
outside `J` of a nonzero vector of `K_x` cannot all vanish. Any two of them meet, because two
nonempty opens of the irreducible `X` meet in a closed point `x`, and `K_x` contains vectors with
any two prescribed coordinates outside the respective `J`'s nonzero. Hence `Z` is irreducible of
dimension `n - 1`.

## Main result

* `Hartshorne.BertiniIncidence.bertini_bad_hyperplane_incidence`
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
  IsLocalRing Topology

namespace Hartshorne.BertiniIncidence

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### Topological gluing -/

section Glue

variable {T : Type u} [TopologicalSpace T]

/-- A set covered by open sets whose traces are irreducible and pairwise meet is irreducible. -/
theorem isIrreducible_of_isOpen_cover {Z : Set T} {ι : Type*} (W : ι → Set T)
    (hW : ∀ i, IsOpen (W i)) (hcov : Z ⊆ ⋃ i, W i)
    (hirr : ∀ i, (Z ∩ W i).Nonempty → IsIrreducible (Z ∩ W i))
    (hmeet : ∀ i j, (Z ∩ W i).Nonempty → (Z ∩ W j).Nonempty → (Z ∩ W i ∩ W j).Nonempty)
    (hne : Z.Nonempty) : IsIrreducible Z := by
  refine ⟨hne, fun U U' hU hU' ⟨u, huZ, huU⟩ ⟨u', hu'Z, hu'U'⟩ => ?_⟩
  obtain ⟨i, hui⟩ := Set.mem_iUnion.mp (hcov huZ)
  obtain ⟨j, hu'j⟩ := Set.mem_iUnion.mp (hcov hu'Z)
  have hi : (Z ∩ W i).Nonempty := ⟨u, huZ, hui⟩
  have hj : (Z ∩ W j).Nonempty := ⟨u', hu'Z, hu'j⟩
  obtain ⟨w, ⟨hwZ, hwi⟩, hwU, hwj⟩ := (hirr i hi).2 U (W j) hU (hW j) ⟨u, ⟨huZ, hui⟩, huU⟩
    (by obtain ⟨v, ⟨hvZ, hvi⟩, hvj⟩ := hmeet i j hi hj; exact ⟨v, ⟨hvZ, hvi⟩, hvj⟩)
  obtain ⟨v, ⟨hvZ, -⟩, hv⟩ := (hirr j hj).2 U U' hU hU' ⟨w, ⟨hwZ, hwj⟩, hwU⟩
    ⟨u', ⟨hu'Z, hu'j⟩, hu'U'⟩
  exact ⟨v, hvZ, hv⟩

/-- The inclusion of the trace of an open set into a subspace is an open embedding. -/
theorem isOpenEmbedding_inclusion_inter {Z W : Set T} (hW : IsOpen W) :
    IsOpenEmbedding (Set.inclusion (Set.inter_subset_left : Z ∩ W ⊆ Z)) := by
  refine ⟨IsEmbedding.inclusion _, ?_⟩
  have : Set.range (Set.inclusion (Set.inter_subset_left : Z ∩ W ⊆ Z)) =
      (Subtype.val : Z → T) ⁻¹' W := by
    ext z
    simp only [Set.range_inclusion, Set.mem_preimage, Set.mem_ofPred_eq]
    exact ⟨fun h => h.2, fun h => ⟨z.2, h⟩⟩
  rw [this]
  exact hW.preimage continuous_subtype_val

end Glue

/-! ### The incidence correspondence -/

section Incidence

variable {k : Type u} [Field k] {n : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ projectiveSpaceOverScheme n (Spec (CommRingCat.of k)))

/-- The incidence set: closed points `(x, H)` of `X ×_k (ℙⁿ_k)^∨` such that a coefficient vector
of `H` lies in the bad subspace at `x`. -/
def incidencePoints : Set (incidenceAmbient (φ ≫ projectiveSpaceOverSchemeProjection n _) n) :=
  {z | IsClosed {z} ∧ ∃ a : Fin (n + 1) → k, a ≠ 0 ∧
    Represents a (pullback.snd _ (dualProjectiveSpaceStructure k n) z) ∧
    a ∈ badHyperplaneSubspace φ (pullback.fst _ (dualProjectiveSpaceStructure k n) z)}

/-- Coordinates outside the invertible minor determine a solution of the local equations. -/
theorem eq_zero_of_local_equations {V : X.Opens} {r : ℕ} (μ : Fin (r + 1) → Fin (n + 1) → Γ(X, V))
    (J : Fin (r + 1) ↪ Fin (n + 1)) (hdet : IsUnit (Matrix.det (Matrix.of fun ℓ ℓ' => μ ℓ (J ℓ'))))
    {x : X} (hx : x ∈ V) {a : Fin (n + 1) → k}
    (ha : ∀ ℓ, X.presheaf.germ V x hx (∑ j, X.presheaf.map (homOfLE le_top).op
      (kConst (φ ≫ projectiveSpaceOverSchemeProjection n _) (a j)) * μ ℓ j) ∈
        maximalIdeal (X.presheaf.stalk x))
    (hout : ∀ j, j ∉ Set.range J → a j = 0) : a = 0 := by
  classical
  let ψ : Γ(X, V) →+* ResidueField (X.presheaf.stalk x) :=
    (residue (X.presheaf.stalk x)).comp (X.presheaf.germ V x hx).hom
  let c : k →+* Γ(X, V) := (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom.comp
    (kConst (φ ≫ projectiveSpaceOverSchemeProjection n _))
  have hc : ∀ t, c t = X.presheaf.map (homOfLE le_top).op
      (kConst (φ ≫ projectiveSpaceOverSchemeProjection n _) t) := fun _ => rfl
  let M : Matrix (Fin (r + 1)) (Fin (r + 1)) (ResidueField (X.presheaf.stalk x)) :=
    Matrix.of fun ℓ ℓ' => ψ (μ ℓ (J ℓ'))
  let v : Fin (r + 1) → ResidueField (X.presheaf.stalk x) := fun ℓ' => ψ (c (a (J ℓ')))
  have hM : M.det ≠ 0 := by
    have : M.det = ψ (Matrix.det (Matrix.of fun ℓ ℓ' => μ ℓ (J ℓ'))) := by
      rw [RingHom.map_det]; rfl
    rw [this]
    exact (hdet.map ψ).ne_zero
  have hMv : M.mulVec v = 0 := by
    funext ℓ
    have h0 : ψ (∑ j, c (a j) * μ ℓ j) = 0 := by
      simp only [hc]
      exact (residue_eq_zero_iff _).mpr (ha ℓ)
    have hsum : ∑ j, c (a j) * μ ℓ j = ∑ ℓ', c (a (J ℓ')) * μ ℓ (J ℓ') := by
      rw [← Finset.sum_map Finset.univ J (fun j => c (a j) * μ ℓ j)]
      refine (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_).symm
      have : j ∉ Set.range J := by
        rintro ⟨ℓ', rfl⟩
        exact hj (Finset.mem_map_of_mem _ (Finset.mem_univ ℓ'))
      rw [hout j this, map_zero, zero_mul]
    rw [hsum, map_sum] at h0
    simp only [Matrix.mulVec, dotProduct, M, v, Matrix.of_apply, Pi.zero_apply]
    rw [← h0]
    refine Finset.sum_congr rfl fun ℓ' _ => ?_
    rw [map_mul, mul_comm]
  have hv : v = 0 := Matrix.eq_zero_of_mulVec_eq_zero hM hMv
  funext j
  by_cases hj : j ∈ Set.range J
  · obtain ⟨ℓ', rfl⟩ := hj
    have := congrFun hv ℓ'
    exact (ψ.comp c).injective (by simpa [v] using this)
  · exact hout j hj

variable [IsAlgClosed k] [IsClosedImmersion φ] [IsIntegral X]

/-- **The bad-hyperplane incidence correspondence** (Hartshorne II, proof of Theorem 8.18). Let
`k` be algebraically closed and let `φ : X ⟶ ℙⁿ_k` be a closed immersion of a nonsingular integral
scheme of dimension `r < n`. Then:

* for every closed point `x`, the coefficient vectors `a` of the hyperplanes `H_a` that contain
  `X` or whose section `H_a ∩ X` is not regular at `x` form the subspace
  `badHyperplaneSubspace φ x` of `kⁿ⁺¹`, of dimension `n - r`; so these hyperplanes form a linear
  subspace `B_x` of `|H|` of dimension `n - r - 1`;
* there is a closed irreducible subset `Z` of `X ×_k (ℙⁿ_k)^∨` of dimension `n - 1` whose closed
  points are exactly the pairs `(x, H)` with `H ∈ B_x`: a closed point `z` lies in `Z` iff the
  hyperplane `H_a` with coefficient vector `a` representing the second component of `z` is bad
  at the first component of `z`. -/
theorem bertini_bad_hyperplane_incidence (hX : X.IsRegular) {r : ℕ}
    (hr : topologicalKrullDim X = r) (hrn : r < n) :
    (∀ x : X, IsClosed {x} → Module.finrank k (badHyperplaneSubspace φ x) = n - r ∧
      ∀ a, a ∈ badHyperplaneSubspace φ x ↔ IsBadHyperplaneAt φ a x) ∧
    ∃ Z : Set (incidenceAmbient (φ ≫ projectiveSpaceOverSchemeProjection n _) n),
      IsClosed Z ∧ IsIrreducible Z ∧ topologicalKrullDim Z = ((n - 1 : ℕ) : WithBot ℕ∞) ∧
      ∀ z, IsClosed {z} → ∀ a : Fin (n + 1) → k, a ≠ 0 →
        Represents a (pullback.snd _ (dualProjectiveSpaceStructure k n) z) →
        (z ∈ Z ↔
          IsBadHyperplaneAt φ a (pullback.fst _ (dualProjectiveSpaceStructure k n) z)) := by
  classical
  have : IsProper (projectiveSpaceOverSchemeProjection n (Spec (CommRingCat.of k))) :=
    projectiveSpaceOverSchemeProjection_isProper n _
  set q := φ ≫ projectiveSpaceOverSchemeProjection n (Spec (CommRingCat.of k)) with hq_def
  have hqft : FiniteType q := ⟨inferInstance, inferInstance⟩
  set P := incidenceAmbient q n
  set fst := pullback.fst q (dualProjectiveSpaceStructure k n)
  set snd := pullback.snd q (dualProjectiveSpaceStructure k n)
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace q
  have : JacobsonSpace P := LocallyOfFiniteType.jacobsonSpace (fst ≫ q)
  have hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) := hX.2
  set K := badHyperplaneSubspace φ
  refine ⟨fun x hx => ⟨finrank_badHyperplaneSubspace φ hX hr x hx,
    fun a => by have := hreg x; exact mem_badHyperplaneSubspace_iff φ x a⟩, ?_⟩
  -- local equations near each closed point
  choose V hV hxV μ J hdet hiff using fun (x₀ : X) (hx₀ : IsClosed {x₀}) =>
    exists_local_incidence_equations φ hX hr x₀ hx₀
  set B := incidencePoints φ
  set Z := closure B
  -- the closure of `B` on a chart
  have hchart : ∀ x₀ (h₀ : IsClosed {x₀}) β,
      Z ∩ (incidenceChart q (V x₀ h₀) β : Set P) = chartIncidence q (μ x₀ h₀) β := by
    intro x₀ h₀ β
    set W := incidenceChart q (V x₀ h₀) β
    have hpt : ∀ z ∈ W, IsClosed {z} → (z ∈ B ↔ z ∈ chartIncidence q (μ x₀ h₀) β) := by
      intro z hzW hz
      obtain ⟨hfz, -, a, ha, hra⟩ := incidenceAmbient_closedPoint q z hz
      constructor
      · rintro ⟨-, a', ha', hra', hK⟩
        rw [mem_chartIncidence_iff q (μ x₀ h₀) β hzW ha' hra']
        exact (hiff x₀ h₀ (fst z) (incidenceChart_le_fst q _ β hzW) hfz a').mp hK
      · intro hC
        exact ⟨hz, a, ha, hra, (hiff x₀ h₀ (fst z) (incidenceChart_le_fst q _ β hzW) hfz a).mpr
          ((mem_chartIncidence_iff q (μ x₀ h₀) β hzW ha hra).mp hC)⟩
    set U := ⋃ ℓ, (P.basicOpen (incidenceChartEquation q (μ x₀ h₀) β ℓ) : Set P)
    have hU : IsOpen U := isOpen_iUnion fun ℓ => (P.basicOpen _).isOpen
    have hC : chartIncidence q (μ x₀ h₀) β = (W : Set P) ∩ Uᶜ := Set.sdiff_eq _ _
    apply le_antisymm
    · rintro z ⟨hzZ, hzW⟩
      refine ⟨hzW, fun hzU => ?_⟩
      obtain ⟨b, ⟨hbU, hbW⟩, hbB⟩ := mem_closure_iff.mp hzZ _ (hU.inter W.isOpen) ⟨hzU, hzW⟩
      have := (hpt b hbW hbB.1).mp hbB
      rw [hC] at this
      exact this.2 hbU
    · intro z hz
      refine ⟨?_, (hC ▸ hz).1⟩
      have hlc : IsLocallyClosed (chartIncidence q (μ x₀ h₀) β) := by
        rw [hC]; exact W.isOpen.isLocallyClosed.inter hU.isClosed_compl.isLocallyClosed
      have hsub : chartIncidence q (μ x₀ h₀) β ∩ closedPoints P ⊆ B := fun w ⟨hwC, hwc⟩ =>
        (hpt w (hC ▸ hwC).1 hwc).mpr hwC
      have : z ∈ closure (chartIncidence q (μ x₀ h₀) β) := subset_closure hz
      rw [← JacobsonSpace.closure_inter_closedPoints_eq_closure hlc] at this
      exact closure_mono hsub this
  -- membership of a closed point
  have hmem : ∀ z, IsClosed {z} → ∀ a : Fin (n + 1) → k, a ≠ 0 → Represents a (snd z) →
      (z ∈ Z ↔ a ∈ K (fst z)) := by
    intro z hz a ha hra
    refine ⟨fun hzZ => ?_, fun hK => subset_closure ⟨hz, a, ha, hra, hK⟩⟩
    obtain ⟨hfz, -, -⟩ := incidenceAmbient_closedPoint q z hz
    obtain ⟨β, hβ⟩ := Function.ne_iff.mp ha
    have hzW : z ∈ incidenceChart q (V (fst z) hfz) β :=
      ⟨hxV _ hfz, (represents_mem_basicOpen_iff hra ha β).mpr hβ⟩
    have hzC : z ∈ chartIncidence q (μ (fst z) hfz) β := hchart _ hfz β ▸ ⟨hzZ, hzW⟩
    exact (hiff _ hfz (fst z) (hxV _ hfz) hfz a).mpr
      ((mem_chartIncidence_iff q _ β hzW ha hra).mp hzC)
  -- the bad subspace has vectors with a prescribed coordinate outside `J` nonzero
  have hcardJ : ∀ x₀ (h₀ : IsClosed {x₀}),
      Fintype.card {j // j ∉ Set.range (J x₀ h₀)} = n - r := by
    intro x₀ h₀
    rw [Fintype.card_subtype_compl, Set.card_range_of_injective (J x₀ h₀).injective,
      Fintype.card_fin, Fintype.card_fin]
    omega
  have hexists : ∀ x₀ (h₀ : IsClosed {x₀}) β, β ∉ Set.range (J x₀ h₀) →
      ∀ x (hx : x ∈ V x₀ h₀), IsClosed {x} → ∃ a ∈ K x, a β ≠ 0 := by
    intro x₀ h₀ β hβ x hx hxc
    let ρ : K x →ₗ[k] ({j // j ∉ Set.range (J x₀ h₀)} → k) :=
      (LinearMap.funLeft k k Subtype.val).comp (K x).subtype
    have hinj : Function.Injective ρ := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro a ha
      apply Subtype.ext
      refine eq_zero_of_local_equations φ (μ x₀ h₀) (J x₀ h₀) (hdet x₀ h₀) hx
        ((hiff x₀ h₀ x hx hxc a).mp a.2) fun j hj => ?_
      exact congrFun ha ⟨j, hj⟩
    have hsurj : Function.Surjective ρ := by
      refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj
      rw [finrank_badHyperplaneSubspace φ hX hr x hxc, Module.finrank_fintype_fun_eq_card,
        hcardJ]
    obtain ⟨a, ha⟩ := hsurj (Pi.single ⟨β, hβ⟩ 1)
    refine ⟨a, a.2, ?_⟩
    have := congrFun ha ⟨β, hβ⟩
    simp only [Pi.single_eq_same] at this
    change (a : Fin (n + 1) → k) β = 1 at this
    rw [this]
    exact one_ne_zero
  -- the charts
  let ι := Σ' (x₀ : X) (h₀ : IsClosed {x₀}) (β : Fin (n + 1)), β ∉ Set.range (J x₀ h₀)
  let W : ι → Set P := fun i => incidenceChart q (V i.1 i.2.1) i.2.2.1
  have hWopen : ∀ i, IsOpen (W i) := fun i => (incidenceChart q _ _).isOpen
  have hpiece : ∀ i, IsIrreducible (Z ∩ W i) ∧
      topologicalKrullDim (Z ∩ W i : Set P) = ((n - 1 : ℕ) : WithBot ℕ∞) := by
    intro i
    obtain ⟨x₀, h₀, β, hβ⟩ := i
    have : Nonempty (V x₀ h₀) := ⟨⟨x₀, hxV x₀ h₀⟩⟩
    change IsIrreducible (Z ∩ (incidenceChart q (V x₀ h₀) β : Set P)) ∧ _
    rw [hchart x₀ h₀ β]
    exact chartIncidence_isIrreducible_and_topologicalKrullDim q (μ x₀ h₀) β hqft (hV x₀ h₀) hr
      hrn (J x₀ h₀) (hdet x₀ h₀) hβ
  -- a closed point of `Z` lies in a chart
  have hcovc : ∀ z ∈ Z, IsClosed {z} → ∃ i, z ∈ W i := by
    intro z hzZ hz
    obtain ⟨hfz, -, a, ha, hra⟩ := incidenceAmbient_closedPoint q z hz
    have hK := (hmem z hz a ha hra).mp hzZ
    have hloc := (hiff _ hfz (fst z) (hxV _ hfz) hfz a).mp hK
    obtain ⟨β, hβJ, hβ⟩ : ∃ β, β ∉ Set.range (J _ hfz) ∧ a β ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact ha (eq_zero_of_local_equations φ (μ _ hfz) (J _ hfz) (hdet _ hfz) (hxV _ hfz)
        hloc hcon)
    exact ⟨⟨fst z, hfz, β, hβJ⟩, hxV _ hfz, (represents_mem_basicOpen_iff hra ha β).mpr hβ⟩
  have hcov : Z ⊆ ⋃ i, W i := by
    intro z hzZ
    obtain ⟨z', ⟨hz'z, hz'c⟩⟩ := nonempty_inter_closedPoints (Set.singleton_nonempty z).closure
      isClosed_closure.isLocallyClosed
    have hz'Z : z' ∈ Z := closure_minimal (Set.singleton_subset_iff.mpr hzZ) isClosed_closure hz'z
    obtain ⟨i, hi⟩ := hcovc z' hz'Z hz'c
    obtain ⟨w, hw, rfl⟩ := mem_closure_iff.mp hz'z _ (hWopen i) hi
    exact Set.mem_iUnion.mpr ⟨i, hw⟩
  -- a closed point of `B` over a closed point `x`, in two prescribed charts
  have hmeet : ∀ i j, (Z ∩ W i ∩ W j).Nonempty := by
    rintro ⟨x₀, h₀, β, hβ⟩ ⟨x₁, h₁, γ, hγ⟩
    obtain ⟨y, hy0, hy1⟩ := nonempty_preirreducible_inter (V x₀ h₀).isOpen (V x₁ h₁).isOpen
      ⟨x₀, hxV x₀ h₀⟩ ⟨x₁, hxV x₁ h₁⟩
    obtain ⟨x, ⟨hx0, hx1⟩, hxc⟩ := nonempty_inter_closedPoints (X := X)
      (Z := (V x₀ h₀ : Set X) ∩ V x₁ h₁) ⟨y, hy0, hy1⟩
      ((V x₀ h₀).isOpen.inter (V x₁ h₁).isOpen).isLocallyClosed
    obtain ⟨u, hu, huβ⟩ := hexists x₀ h₀ β hβ x hx0 hxc
    obtain ⟨v, hv, hvγ⟩ := hexists x₁ h₁ γ hγ x hx1 hxc
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
    have hzB : z ∈ B := ⟨hz, w, hw0, hzr, by rw [hzx]; exact hw⟩
    refine ⟨z, ⟨subset_closure hzB, ?_⟩, ?_⟩
    · exact ⟨show fst z ∈ V x₀ h₀ by rw [hzx]; exact hx0,
        (represents_mem_basicOpen_iff hzr hw0 β).mpr hwβ⟩
    · exact ⟨show fst z ∈ V x₁ h₁ by rw [hzx]; exact hx1,
        (represents_mem_basicOpen_iff hzr hw0 γ).mpr hwγ⟩
  -- `Z` is nonempty
  obtain ⟨x₀, -, hx₀⟩ := nonempty_inter_closedPoints (X := X) (Z := Set.univ) Set.univ_nonempty
    isClosed_univ.isLocallyClosed
  obtain ⟨β, hβ⟩ : ∃ β, β ∉ Set.range (J x₀ hx₀) := by
    by_contra hcon
    push Not at hcon
    have h0 := hcardJ x₀ hx₀
    have : IsEmpty {j // j ∉ Set.range (J x₀ hx₀)} := ⟨fun j => j.2 (hcon j.1)⟩
    rw [Fintype.card_eq_zero] at h0
    omega
  let i₀ : ι := ⟨x₀, hx₀, β, hβ⟩
  have hne : (Z ∩ W i₀).Nonempty := by
    obtain ⟨z, hz⟩ := hmeet i₀ i₀
    exact ⟨z, hz.1⟩
  refine ⟨Z, isClosed_closure, ?_, ?_, fun z hz a ha hra => ?_⟩
  · exact isIrreducible_of_isOpen_cover W hWopen hcov (fun i _ => (hpiece i).1)
      (fun i j _ _ => hmeet i j) (hne.mono Set.inter_subset_left)
  · refine le_antisymm ?_ ?_
    · refine BaseExtensionComponentDimension.topologicalKrullDim_le_of_forall_isOpenEmbedding _
        fun y => ?_
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov y.2)
      refine ⟨(Z ∩ W i : Set P), inferInstance, Set.inclusion Set.inter_subset_left,
        isOpenEmbedding_inclusion_inter (hWopen i), ⟨⟨y.1, y.2, hi⟩, rfl⟩, (hpiece i).2.le⟩
    · rw [← (hpiece i₀).2]
      exact (IsEmbedding.inclusion
        (Set.inter_subset_left : Z ∩ W i₀ ⊆ Z)).isInducing.topologicalKrullDim_le
  · obtain ⟨hfz, -, -⟩ := incidenceAmbient_closedPoint q z hz
    have := hreg (fst z)
    rw [hmem z hz a ha hra]
    exact mem_badHyperplaneSubspace_iff φ (fst z) a

end Incidence

end Hartshorne.BertiniIncidence

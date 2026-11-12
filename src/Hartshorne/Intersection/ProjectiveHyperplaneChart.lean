/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.ProjectiveLinearSubspaceCycle
import Hartshorne.Scheme.ProjPartialMap
import Hartshorne.Scheme.ProjSurjectionClosedImmersion
import Hartshorne.Scheme.ProjectiveSpaceChart

/-!
# The hyperplane `V(x_{N+1})` and its complement in projective space

Let `ℙ^{N+1}_k = Proj k[x₀, …, x_{N+1}]`. The surjective graded homomorphism
`k[x₀, …, x_{N+1}] → k[x₀, …, x_N]`, `x_{N+1} ↦ 0` (`hyperplaneRestrictHom`), induces a closed
immersion `ℙ^N_k ⟶ ℙ^{N+1}_k` over `k` (`hyperplaneEmbedding`) whose image is the hyperplane
`H = V(x_{N+1})` (`mem_range_hyperplaneEmbedding_of_X_last_mem`) and which maps the linear
subspace `L_m` of `ℙ^N_k` to the linear subspace `L_m` of `ℙ^{N+1}_k`
(`hyperplaneEmbedding_linearSubspacePoint`). The complement `D₊(x_{N+1})` of `H` is isomorphic to
affine space `Spec k[y₀, …, y_N]` (`hyperplaneComplementIso`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial Order TopologicalSpace

namespace Hartshorne

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] (N : ℕ)

/-- The `k`-algebra map `k[x₀, …, x_{N+1}] → k[x₀, …, x_N]` sending `x_{N+1}` to `0` and
`x_i` to `x_i` for `i ≤ N`. -/
def hyperplaneRestrict : MvPolynomial (Fin (N + 1 + 1)) k →ₐ[k] MvPolynomial (Fin (N + 1)) k :=
  aeval (Fin.lastCases 0 X)

theorem hyperplaneRestrict_rename_castSucc (f : MvPolynomial (Fin (N + 1)) k) :
    hyperplaneRestrict N (rename Fin.castSucc f) = f := by
  rw [← AlgHom.comp_apply]
  conv_rhs => rw [← AlgHom.id_apply (R := k) f]
  congr 1
  ext i
  simp [hyperplaneRestrict]

theorem hyperplaneRestrict_surjective : Function.Surjective (hyperplaneRestrict (k := k) N) :=
  fun f => ⟨_, hyperplaneRestrict_rename_castSucc N f⟩

/-- `x_i ↦ x_i` for `i ≤ N` and `x_{N+1} ↦ 0`, as an endomorphism of `k[x₀, …, x_{N+1}]`, is
`hyperplaneRestrict` followed by the inclusion. -/
theorem rename_castSucc_hyperplaneRestrict :
    (rename Fin.castSucc).comp (hyperplaneRestrict (k := k) N) =
      aeval fun i : Fin (N + 1 + 1) =>
        if i ∈ ({Fin.last (N + 1)} : Set (Fin (N + 1 + 1))) then 0 else X i := by
  ext i : 1
  induction i using Fin.lastCases with
  | last => simp [hyperplaneRestrict]
  | cast i => simp [hyperplaneRestrict, Fin.castSucc_ne_last]

theorem ker_hyperplaneRestrict :
    RingHom.ker (hyperplaneRestrict (k := k) N).toRingHom =
      Ideal.span {(X (Fin.last (N + 1)) : MvPolynomial (Fin (N + 1 + 1)) k)} := by
  classical
  have h := ker_aeval_ite_eq_span_X_image (R := k) ({Fin.last (N + 1)} : Set (Fin (N + 1 + 1)))
  rw [Set.image_singleton] at h
  rw [← h, ← rename_castSucc_hyperplaneRestrict]
  ext f
  simp only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.comp_apply]
  constructor
  · intro hf
    rw [hf, map_zero]
  · intro hf
    exact rename_injective _ (Fin.castSucc_injective _) (by rw [hf, map_zero])

/-- `hyperplaneRestrict` as a graded ring homomorphism. -/
def hyperplaneRestrictHom :
    homogeneousSubmodule (Fin (N + 1 + 1)) k →+*ᵍ homogeneousSubmodule (Fin (N + 1)) k where
  toRingHom := (hyperplaneRestrict N).toRingHom
  map_mem {d x} hx := by
    rw [mem_homogeneousSubmodule] at hx ⊢
    have := hx.eval₂ (algebraMap k _) (Fin.lastCases 0 X) (fun r => isHomogeneous_C _ r)
      (fun i => by
        induction i using Fin.lastCases with
        | last => simpa using isHomogeneous_zero (Fin (N + 1)) k 1
        | cast i => simpa using isHomogeneous_X k i)
    rw [one_mul] at this
    change IsHomogeneous (aeval (Fin.lastCases 0 X) x) d
    rw [aeval_def]
    exact this

theorem hyperplaneRestrictHom_apply (f : MvPolynomial (Fin (N + 1 + 1)) k) :
    hyperplaneRestrictHom N f = hyperplaneRestrict N f :=
  rfl

theorem irrelevant_le_map_hyperplaneRestrictHom :
    HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin (N + 1)) k) ≤
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin (N + 1 + 1)) k)).map
        (hyperplaneRestrictHom N) := by
  change _ ≤ Ideal.map _ _
  refine (irrelevant_le_span_range_X k).trans (Ideal.span_le.mpr ?_)
  rintro _ ⟨i, rfl⟩
  have h : hyperplaneRestrictHom N (X (Fin.castSucc i)) = (X i : MvPolynomial (Fin (N + 1)) k) := by
    simp [hyperplaneRestrictHom_apply, hyperplaneRestrict]
  rw [SetLike.mem_coe, ← h]
  exact Ideal.mem_map_of_mem _ (X_mem_irrelevant_projectiveSpace _)

/-- **The hyperplane embedding** `ℙ^N_k ⟶ ℙ^{N+1}_k` onto `V(x_{N+1})`. -/
def hyperplaneEmbedding :
    Proj (homogeneousSubmodule (Fin (N + 1)) k) ⟶ Proj (homogeneousSubmodule (Fin (N + 1 + 1)) k) :=
  Proj.map (hyperplaneRestrictHom N) (irrelevant_le_map_hyperplaneRestrictHom N)

theorem hyperplaneEmbedding_asHomogeneousIdeal (x : Proj (homogeneousSubmodule (Fin (N + 1)) k)) :
    (hyperplaneEmbedding N x).asHomogeneousIdeal =
      x.asHomogeneousIdeal.comap (hyperplaneRestrictHom N) :=
  rfl

instance : IsClosedImmersion (hyperplaneEmbedding (k := k) N) := by
  have hsurj : Function.Surjective (hyperplaneRestrictHom (k := k) N) :=
    hyperplaneRestrict_surjective N
  have h := isClosedImmersion_projPartialMap_comp_top_of_surjective hsurj
  rw [projPartialMap_eq_map (irrelevant_le_map_hyperplaneRestrictHom N)] at h
  have e : (Proj (homogeneousSubmodule (Fin (N + 1)) k)).topIso.inv ≫
      (Proj (homogeneousSubmodule (Fin (N + 1)) k)).homOfLE
        (projPartialDomain_eq_top_of_surjective hsurj).ge ≫
      (projPartialDomain (hyperplaneRestrictHom N)).ι = 𝟙 _ := by
    rw [Scheme.homOfLE_ι]
    simp
  rw [← Category.assoc, ← Category.assoc, Category.assoc _ _ (projPartialDomain _).ι, e,
    Category.id_comp] at h
  exact h

/-- The hyperplane embedding is a morphism over `k`. -/
theorem hyperplaneEmbedding_comp_structureMorphism :
    hyperplaneEmbedding N ≫ projectiveSpaceStructureMorphism (k := k) (n := N + 1) =
      projectiveSpaceStructureMorphism (k := k) (n := N) := by
  rw [hyperplaneEmbedding, projectiveSpaceStructureMorphism, ← Category.assoc,
    projMap_toSpecZero, Category.assoc, projectiveSpaceStructureMorphism, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  apply Subtype.ext
  change hyperplaneRestrict N (algebraMap k _ a) = algebraMap k _ a
  exact (hyperplaneRestrict N).commutes a

/-- The hyperplane embedding maps the linear subspace `L_m` of `ℙ^N_k` to the linear subspace
`L_m` of `ℙ^{N+1}_k`, for `m ≤ N`. -/
theorem hyperplaneEmbedding_linearSubspacePoint {m : ℕ} (hm : m ≤ N) :
    hyperplaneEmbedding N (linearSubspacePoint (k := k) (n := N) m) =
      linearSubspacePoint (k := k) (n := N + 1) m := by
  classical
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.toIdeal_injective
  rw [hyperplaneEmbedding_asHomogeneousIdeal, linearSubspacePoint_asHomogeneousIdeal,
    linearSubspacePoint_asHomogeneousIdeal, HomogeneousIdeal.toIdeal_comap,
    linearSubspaceIdeal_toIdeal, linearSubspaceIdeal_toIdeal,
    ← ker_aeval_ite_eq_span_X_image, ← ker_aeval_ite_eq_span_X_image]
  set s : Set (Fin (N + 1 + 1)) := {i | m < (i : ℕ)}
  set s' : Set (Fin (N + 1)) := {i | m < (i : ℕ)}
  have hfac : (aeval fun i : Fin (N + 1 + 1) => if i ∈ s then (0 : MvPolynomial (Fin (N + 1 + 1)) k)
      else X i) = (rename Fin.castSucc).comp ((aeval fun i : Fin (N + 1) =>
        if i ∈ s' then (0 : MvPolynomial (Fin (N + 1)) k) else X i).comp
          (hyperplaneRestrict N)) := by
    ext i : 1
    induction i using Fin.lastCases with
    | last =>
      have : Fin.last (N + 1) ∈ s := by
        change m < ((Fin.last (N + 1) : Fin (N + 1 + 1)) : ℕ)
        rw [Fin.val_last]
        omega
      simp [this, hyperplaneRestrict]
    | cast j =>
      have hj : (Fin.castSucc j ∈ s) ↔ j ∈ s' := by
        change m < ((Fin.castSucc j : Fin (N + 1 + 1)) : ℕ) ↔ m < (j : ℕ)
        rw [Fin.val_castSucc]
      by_cases h : j ∈ s'
      · simp [hyperplaneRestrict, h, hj.mpr h]
      · simp [hyperplaneRestrict, h, mt hj.mp h]
  ext f
  simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  rw [hfac, AlgHom.comp_apply, AlgHom.comp_apply]
  change _ ↔ rename Fin.castSucc _ = 0
  constructor
  · intro h
    rw [hyperplaneRestrictHom_apply] at h
    rw [h, map_zero]
  · intro h
    rw [hyperplaneRestrictHom_apply]
    exact rename_injective _ (Fin.castSucc_injective _) (by rw [h, map_zero])

/-- Every point of `V(x_{N+1})` lies in the image of the hyperplane embedding. -/
theorem mem_range_hyperplaneEmbedding_of_X_last_mem
    (x : Proj (homogeneousSubmodule (Fin (N + 1 + 1)) k))
    (hx : (X (Fin.last (N + 1)) : MvPolynomial (Fin (N + 1 + 1)) k) ∈ x.asHomogeneousIdeal) :
    x ∈ Set.range (hyperplaneEmbedding (k := k) N) := by
  let φ := hyperplaneRestrictHom (k := k) N
  have hsurj : Function.Surjective φ := hyperplaneRestrict_surjective N
  have hker : RingHom.ker φ.toRingHom ≤ x.asHomogeneousIdeal.toIdeal := by
    change RingHom.ker (hyperplaneRestrict (k := k) N).toRingHom ≤ _
    rw [ker_hyperplaneRestrict, Ideal.span_le, Set.singleton_subset_iff]
    exact hx
  have hcomap : (x.asHomogeneousIdeal.map φ).toIdeal.comap φ.toRingHom =
      x.asHomogeneousIdeal.toIdeal := by
    rw [HomogeneousIdeal.toIdeal_map]
    exact Ideal.comap_map_of_surjective' _ hsurj _ |>.trans (sup_eq_left.mpr hker)
  have : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
  have hprime : (x.asHomogeneousIdeal.map φ).toIdeal.IsPrime := by
    rw [HomogeneousIdeal.toIdeal_map]
    exact Ideal.map_isPrime_of_surjective hsurj hker
  let y : Proj (homogeneousSubmodule (Fin (N + 1)) k) :=
    ⟨x.asHomogeneousIdeal.map φ, hprime, fun hle => x.not_irrelevant_le (by
      intro a ha
      have h1 : a ∈ (x.asHomogeneousIdeal.map φ).toIdeal.comap φ.toRingHom := by
        change φ a ∈ (x.asHomogeneousIdeal.map φ).toIdeal
        apply hle
        rw [HomogeneousIdeal.mem_irrelevant_iff] at ha ⊢
        rw [GradedRing.proj_apply, ← GradedRingHom.map_directSumDecompose, ← GradedRing.proj_apply,
          ha, map_zero]
      rw [hcomap] at h1
      exact h1)⟩
  refine ⟨y, ProjectiveSpectrum.ext (HomogeneousIdeal.toIdeal_injective ?_)⟩
  rw [hyperplaneEmbedding_asHomogeneousIdeal, HomogeneousIdeal.toIdeal_comap]
  exact hcomap

/-- The complement `D₊(x_{N+1})` of the hyperplane `V(x_{N+1})`. -/
def hyperplaneComplement : (Proj (homogeneousSubmodule (Fin (N + 1 + 1)) k)).Opens :=
  Proj.basicOpen _ (X (Fin.last (N + 1)))

/-- Every point outside `D₊(x_{N+1})` lies on the image of the hyperplane embedding. -/
theorem mem_range_hyperplaneEmbedding_of_notMem
    (x : Proj (homogeneousSubmodule (Fin (N + 1 + 1)) k))
    (hx : x ∉ hyperplaneComplement (k := k) N) :
    x ∈ Set.range (hyperplaneEmbedding (k := k) N) := by
  refine mem_range_hyperplaneEmbedding_of_X_last_mem N x ?_
  by_contra h
  exact hx ((Proj.mem_basicOpen _ _ _).mpr h)

/-- The ring of the chart `D₊(x_{N+1})` is a polynomial ring in `N + 1` variables. -/
def hyperplaneComplementRingEquiv :
    HomogeneousLocalization.Away (homogeneousSubmodule (Fin (N + 1 + 1)) k)
      (X (Fin.last (N + 1))) ≃+* MvPolynomial (Option (Fin N)) k :=
  (chartAwayEquiv k (Fin.last (N + 1))).trans
    (renameEquiv k ((finSuccAboveEquiv (Fin.last (N + 1))).symm.trans (finSuccEquiv N))).toRingEquiv

/-- **The complement of the hyperplane is affine space**: an isomorphism
`Spec k[y₀, …, y_N] ≅ D₊(x_{N+1})`. -/
def hyperplaneComplementIso :
    Spec (.of (MvPolynomial (Option (Fin N)) k)) ≅ (hyperplaneComplement (k := k) N : Scheme) :=
  Scheme.Spec.mapIso (hyperplaneComplementRingEquiv N).toCommRingCatIso.op ≪≫
    (Proj.basicOpenIsoSpec _ (X (Fin.last (N + 1))) (X_mem_homogeneousSubmodule_one k _)
      zero_lt_one).symm

instance : Nonempty (hyperplaneComplement (k := k) N) :=
  ⟨(hyperplaneComplementIso N).hom (⊥ : PrimeSpectrum (MvPolynomial (Option (Fin N)) k))⟩

instance : IsIntegral (hyperplaneComplement (k := k) N : Scheme) :=
  isIntegral_of_isOpenImmersion (hyperplaneComplement N).ι

end Hartshorne

/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ProjPartialMap
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Proj is invariant under an eventual graded isomorphism

Hartshorne, *Algebraic Geometry*, II, Exercise 2.14(c).

Let `φ : S →+*ᵍ T` be a degree-preserving homomorphism of `ℕ`-graded rings such
that `φ_d : S_d → T_d` is bijective for every `d ≥ d₀`. Then the natural domain
`U = {𝔭 ∈ Proj T | 𝔭 ⊉ φ(S₊)}` of the partial Proj morphism is all of `Proj T`,
and the induced morphism `Proj T ⟶ Proj S` is an isomorphism.

The proof uses high powers of homogeneous elements: a relevant homogeneous prime
of `T` misses some homogeneous `t` of positive degree, hence misses
`t ^ (d₀ + 1) = φ(s)`, so it lies in `U`. For homogeneous `r ∈ S` of degree
`≥ d₀`, every fraction of `S_(r)` or `T_(φ r)` can be written with numerator in
degree `≥ d₀`, so `S_(r) → T_(φ r)` is a ring isomorphism; therefore the partial
morphism restricted over `D₊(r)` is an isomorphism. These `D₊(r)` cover `Proj S`
and being an isomorphism is local on the target.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open HomogeneousIdeal HomogeneousLocalization TopologicalSpace
open AlgebraicGeometry

universe u

namespace Hartshorne

namespace ProjTail

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜]

/-- A relevant homogeneous prime misses a homogeneous element of positive degree. -/
theorem exists_homogeneous_not_mem (x : ProjectiveSpectrum 𝒜) :
    ∃ (e : ℕ) (t : A), 0 < e ∧ t ∈ 𝒜 e ∧ t ∉ x.asHomogeneousIdeal := by
  classical
  obtain ⟨y, hy, hyx⟩ := Set.not_subset.mp x.not_irrelevant_le
  by_contra! H
  apply hyx
  rw [← DirectSum.sum_support_decompose 𝒜 y]
  refine Ideal.sum_mem _ fun i _ => ?_
  by_cases hi : i = 0
  · subst hi
    have h0 : (DirectSum.decompose 𝒜 y 0 : A) = 0 := (mem_irrelevant_iff 𝒜 y).mp hy
    rw [h0]
    exact zero_mem _
  · exact H i _ (Nat.pos_of_ne_zero hi) (SetLike.coe_mem _)

/-- A relevant homogeneous prime misses a homogeneous element of positive degree at
least `d₀`. -/
theorem exists_homogeneous_not_mem_of_le (d₀ : ℕ) (x : ProjectiveSpectrum 𝒜) :
    ∃ (e : ℕ) (t : A), 0 < e ∧ d₀ ≤ e ∧ t ∈ 𝒜 e ∧ t ∉ x.asHomogeneousIdeal := by
  obtain ⟨e, t, he, ht, htx⟩ := exists_homogeneous_not_mem x
  refine ⟨(d₀ + 1) • e, t ^ (d₀ + 1), ?_, ?_, SetLike.pow_mem_graded _ ht, fun h => htx ?_⟩
  · rw [smul_eq_mul]
    positivity
  · rw [smul_eq_mul]
    nlinarith
  · exact x.isPrime.mem_of_pow_mem _ h

/-- Positive-degree homogeneous elements of degree at least `d₀`. -/
abbrev TailIndex (𝒜 : ℕ → σ) (d₀ : ℕ) := Σ' (i : ℕ) (r : A), 0 < i ∧ d₀ ≤ i ∧ r ∈ 𝒜 i

/-- The standard opens `D₊(r)` with `r` homogeneous of positive degree `≥ d₀` cover
`Proj S`. -/
theorem iSup_basicOpen_tail_eq_top (d₀ : ℕ) :
    ⨆ r : TailIndex 𝒜 d₀, Proj.basicOpen 𝒜 r.2.1 = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨e, t, he, hd, ht, htx⟩ := exists_homogeneous_not_mem_of_le d₀ x
  exact Opens.mem_iSup.mpr ⟨⟨e, t, he, hd, ht⟩, (Proj.mem_basicOpen _ _ _).mpr htx⟩

end ProjTail

open ProjTail

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] {f : 𝒜 →+*ᵍ ℬ} {d₀ : ℕ}

omit [GradedRing 𝒜] [GradedRing ℬ] in
theorem ProjTail.exists_preimage (hf : ∀ d, d₀ ≤ d → Function.Bijective (f.gradedAddHom d))
    {d : ℕ} (hd : d₀ ≤ d) {b : B} (hb : b ∈ ℬ d) : ∃ a ∈ 𝒜 d, f a = b := by
  obtain ⟨a, ha⟩ := (hf d hd).2 ⟨b, hb⟩
  exact ⟨a, a.2, congrArg Subtype.val ha⟩

omit [GradedRing 𝒜] [GradedRing ℬ] in
theorem ProjTail.eq_zero (hf : ∀ d, d₀ ≤ d → Function.Bijective (f.gradedAddHom d))
    {d : ℕ} (hd : d₀ ≤ d) {a : A} (ha : a ∈ 𝒜 d) (h : f a = 0) : a = 0 := by
  have := (hf d hd).1 (a₁ := ⟨a, ha⟩) (a₂ := 0) (Subtype.ext (by simpa using h))
  simpa using congrArg Subtype.val this

/-- **Hartshorne II, Exercise 2.14(c), domain.** If `φ_d` is bijective for all
`d ≥ d₀`, the natural domain of the partial Proj morphism is all of `Proj T`. -/
theorem projPartialDomain_eq_top_of_bijective
    (hf : ∀ d, d₀ ≤ d → Function.Bijective (f.gradedAddHom d)) :
    projPartialDomain f = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨e, t, he, hd, ht, htx⟩ := exists_homogeneous_not_mem_of_le d₀ x
  obtain ⟨a, ha, hfa⟩ := ProjTail.exists_preimage hf hd ht
  rw [mem_projPartialDomain_iff]
  intro h
  exact htx (hfa ▸ h ⟨a, mem_irrelevant_of_mem 𝒜 he ha, rfl⟩)

/-- For `r` homogeneous of degree `≥ d₀`, the map of degree-zero localizations
`S_(r) → T_(φ r)` is bijective. -/
theorem ProjTail.bijective_awayMap
    (hf : ∀ d, d₀ ≤ d → Function.Bijective (f.gradedAddHom d))
    {i : ℕ} {r : A} (hr : r ∈ 𝒜 i) (hd : d₀ ≤ i) : Function.Bijective (Away.map f r) := by
  constructor
  · refine (injective_iff_map_eq_zero _).mpr fun z hz => ?_
    obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hr z
    rw [Away.map_mk, ext_iff_val, Away.val_mk, val_zero, Localization.mk_eq_mk',
      IsLocalization.mk'_eq_zero_iff] at hz
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := hz
    have h0 : r ^ (k + 1) * a = 0 := by
      refine ProjTail.eq_zero hf (d := (k + 1) • i + n • i) ?_
        (SetLike.mul_mem_graded (SetLike.pow_mem_graded _ hr) ha) ?_
      · rw [smul_eq_mul]
        nlinarith
      · simp only [map_mul, map_pow] at hk ⊢
        rw [pow_succ, mul_comm _ (f r), mul_assoc, hk, mul_zero]
    rw [ext_iff_val, Away.val_mk, val_zero, Localization.mk_eq_mk',
      IsLocalization.mk'_eq_zero_iff]
    exact ⟨⟨_, k + 1, rfl⟩, h0⟩
  · intro w
    obtain ⟨n, b, hb, rfl⟩ := Away.mk_surjective ℬ (f.map_mem hr) w
    have hb' : b * f r ∈ ℬ ((n + 1) • i) := by
      rw [succ_nsmul]
      exact SetLike.mul_mem_graded hb (f.map_mem hr)
    obtain ⟨a, ha, hfa⟩ := ProjTail.exists_preimage hf
      (by rw [smul_eq_mul]; nlinarith : d₀ ≤ (n + 1) • i) hb'
    refine ⟨Away.mk 𝒜 hr (n + 1) a ha, ?_⟩
    rw [Away.map_mk, ext_iff_val, Away.val_mk, Away.val_mk, Localization.mk_eq_mk_iff,
      Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [hfa, OneMemClass.coe_one, one_mul]
    change f r ^ n * (b * f r) = f r ^ (n + 1) * b
    ring

/-- Over a standard open `D₊(r)` with `deg r ≥ d₀`, the partial Proj morphism is an
isomorphism. -/
theorem ProjTail.isIso_morphismRestrict
    (hf : ∀ d, d₀ ≤ d → Function.Bijective (f.gradedAddHom d))
    {i : ℕ} {r : A} (hr : r ∈ 𝒜 i) (hi : 0 < i) (hd : d₀ ≤ i) :
    IsIso (projPartialMap f ∣_ Proj.basicOpen 𝒜 r) := by
  have : IsIso (CommRingCat.ofHom (Away.map f r)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (ProjTail.bijective_awayMap hf hr hd)
  set W := (projPartialDomain f).ι ⁻¹ᵁ Proj.basicOpen ℬ (f r)
  have hW : projPartialMap f ⁻¹ᵁ Proj.basicOpen 𝒜 r = W := projPartialMap_preimage_basicOpen f r
  have key : projPartialMap f ∣_ Proj.basicOpen 𝒜 r =
      (Scheme.isoOfEq _ hW).hom ≫
        (projPartialDomain f).ι.resLE (Proj.basicOpen ℬ (f r)) W le_rfl ≫
        (Proj.basicOpenIsoSpec ℬ (f r) (f.map_mem hr) hi).hom ≫
        Spec.map (CommRingCat.ofHom (Away.map f r)) ≫
        (Proj.basicOpenIsoSpec 𝒜 r hr hi).inv := by
    rw [← cancel_mono (Proj.basicOpen 𝒜 r).ι, morphismRestrict_ι,
      ← Scheme.isoOfEq_hom_ι _ hW, Category.assoc]
    simp only [Category.assoc, Proj.basicOpenIsoSpec_inv_ι, Proj.basicOpenIsoSpec_hom]
    congr 1
    exact projPartialCover_f_projPartialMap f r hr hi
  have hres : IsIso ((projPartialDomain f).ι.resLE (Proj.basicOpen ℬ (f r)) W le_rfl) := by
    have : IsOpenImmersion ((projPartialDomain f).ι.resLE (Proj.basicOpen ℬ (f r)) W le_rfl ≫
        (Proj.basicOpen ℬ (f r)).ι) := by
      rw [Scheme.Hom.resLE_comp_ι]
      infer_instance
    have : IsOpenImmersion ((projPartialDomain f).ι.resLE (Proj.basicOpen ℬ (f r)) W le_rfl) :=
      IsOpenImmersion.of_comp _ (Proj.basicOpen ℬ (f r)).ι
    rw [isIso_iff_isOpenImmersion_and_surjective]
    refine ⟨inferInstance, ⟨fun y => ?_⟩⟩
    have hyU : y.1 ∈ projPartialDomain f :=
      basicOpen_le_projPartialDomain f hi hr y.2
    refine ⟨⟨⟨y.1, hyU⟩, y.2⟩, ?_⟩
    apply (Proj.basicOpen ℬ (f r)).ι.isOpenEmbedding.injective
    change ((projPartialDomain f).ι.resLE (Proj.basicOpen ℬ (f r)) W le_rfl ≫
      (Proj.basicOpen ℬ (f r)).ι) _ = _
    rw [Scheme.Hom.resLE_comp_ι]
    rfl
  rw [key]
  infer_instance

/-- **Hartshorne II, Exercise 2.14(c), isomorphism.** If `φ_d` is bijective for all
`d ≥ d₀`, the partial Proj morphism `U ⟶ Proj S` is an isomorphism (and
`U = Proj T` by `projPartialDomain_eq_top_of_bijective`). -/
theorem isIso_projPartialMap_of_bijective
    (hf : ∀ d, d₀ ≤ d → Function.Bijective (f.gradedAddHom d)) :
    IsIso (projPartialMap f) := by
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    (f := projPartialMap f) _ (iSup_basicOpen_tail_eq_top (𝒜 := 𝒜) d₀)).mpr ?_
  rintro ⟨i, r, hi, hd, hr⟩
  exact ProjTail.isIso_morphismRestrict hf hr hi hd

/-- **Hartshorne II, Exercise 2.14(c).** If `φ_d : S_d → T_d` is bijective for all
`d ≥ d₀`, the induced morphism `Proj T ⟶ Proj S`, namely the partial Proj
morphism on its natural domain, which is all of `Proj T`, is an isomorphism. -/
theorem isIso_projPartialMap_comp_top_of_bijective
    (hf : ∀ d, d₀ ≤ d → Function.Bijective (f.gradedAddHom d)) :
    IsIso ((Proj ℬ).topIso.inv ≫
      (Proj ℬ).homOfLE (projPartialDomain_eq_top_of_bijective hf).ge ≫ projPartialMap f) := by
  have := isIso_projPartialMap_of_bijective hf
  have : ∀ (V : (Proj ℬ).Opens) (h : ⊤ ≤ V), IsIso ((Proj ℬ).homOfLE h) := by
    intro V h
    obtain rfl : V = ⊤ := top_le_iff.mp h
    rw [Scheme.homOfLE_rfl]
    infer_instance
  have := this _ (projPartialDomain_eq_top_of_bijective hf).ge
  infer_instance

end Hartshorne

/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.RelativeHomogeneousCoordinateAlgebra

/-!
# The uniform bound on every affine open

Hartshorne, *Algebraic Geometry*, II, proof of Theorem 7.17, Step 2 (pp. 166–167).

Let `T(U) = Γ(X, U)[x₀, …, xᵣ] / I_U` be the relative homogeneous coordinate algebra of a closed
subscheme `Z ⊆ ℙʳ_X` (`SectionAlgebraModel.coordinateAlgebra`). Over each affine open `U`,
`T(U)_n → Γ(f⁻¹(U), L^n)` is bijective for `n` large (Exercise 5.9), but the bound depends on `U`.
Hartshorne's Step 2 needs one bound for all `U`. This file obtains it from a finite affine cover.

The surjectivity of `T_n → Γ(Proj T, 𝒪(n))` for a graded domain `T` is equivalent to an algebraic
condition (`SectionAlgebraModel.ChartGood`, `SectionAlgebraModel.bijective_twistSection_iff_chartGood`):
every fraction `a / s` such that each `xᵢ^j a / s` lies in `T_{j+n}` lies in `T_n`. This condition
passes to localizations `T[1/g]`, `g ∈ T₀` (`SectionAlgebraModel.chartGood_of_isLocalizationAway`),
and descends from a cover `T[1/gⱼ]` with `(gⱼ) = 1`
(`SectionAlgebraModel.chartGood_of_forall_exists_pow_mul`,
`SectionAlgebraModel.exists_pow_mul_of_chartGood`). Every affine open is covered by opens that are
basic both in it and in a member of the finite cover, so the bound of the finite cover works for all
affine opens (`SectionAlgebraModel.exists_bound_bijective_twistSection`).

* `SectionAlgebraModel.exists_bound_addEquiv_sections_veronese`: a `d₀` such that for every affine
  open `U ⊆ X`, `d ≥ d₀` and `m ≥ 1`, the degree-`m` part of `T(U)^{(d)}` is the group of sections
  of `L^{md}` over `f⁻¹(U)`.
* `SectionAlgebraModel.exists_sectionAlgebraModel`: the section-algebra model with the
  identification of the graded pieces on every affine open.
-/

universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Hartshorne

open AlgebraicGeometry CategoryTheory Opposite GradedGlobalSections

namespace SectionAlgebraModel

/-! ### The chart condition under localization on `Spec T₀` -/

section Algebra

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

private theorem mem_of_zero_mul {a b : A} {d : ℕ} (ha : a ∈ 𝒜 0) (hb : b ∈ 𝒜 d) :
    a * b ∈ 𝒜 d := by
  simpa using SetLike.mul_mem_graded ha hb

private theorem pow_mem_zero {a : A} (ha : a ∈ 𝒜 0) (m : ℕ) : a ^ m ∈ 𝒜 0 := by
  simpa using SetLike.pow_mem_graded m ha

/-- In an `ℕ`-graded ring the inverse of a unit of degree zero can be taken of degree zero. -/
private theorem exists_mem_zero_mul_eq_one {u v : B} (hu : u ∈ ℬ 0) (huv : u * v = 1) :
    ∃ w ∈ ℬ 0, u * w = 1 := by
  refine ⟨DirectSum.decompose ℬ v 0, (DirectSum.decompose ℬ v 0).2, ?_⟩
  have e := DirectSum.coe_decompose_mul_of_left_mem_zero (𝒜 := ℬ) (b := v) (j := 0) hu
  rw [huv] at e
  rw [← e]
  exact DirectSum.decompose_of_mem_same ℬ SetLike.GradedOne.one_mem

variable (φ : A →+* B) (hφ : ∀ (d : ℕ) (a : A), a ∈ 𝒜 d → φ a ∈ ℬ d) {g : A} (hg : g ∈ 𝒜 0)
  (hloc : letI := φ.toAlgebra; IsLocalization.Away g B)

include hφ hg hloc in
/-- A homogeneous element of `B = A[1/g]` (`g ∈ A₀`) is the image of a homogeneous element of the
same degree, up to a power of `g`. -/
private theorem exists_mem_map_eq_pow_mul {d : ℕ} {b : B} (hb : b ∈ ℬ d) :
    ∃ (m : ℕ) (c : A), c ∈ 𝒜 d ∧ φ c = φ g ^ m * b := by
  let := φ.toAlgebra
  obtain ⟨⟨a, ⟨_, m, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers g) b
  let ψ : 𝒜 →+*ᵍ ℬ := { φ with map_mem := fun h => hφ _ _ h }
  refine ⟨m, DirectSum.decompose 𝒜 a d, (DirectSum.decompose 𝒜 a d).2, ?_⟩
  have e₀ : ψ (DirectSum.decompose 𝒜 a d) = DirectSum.decompose ℬ (ψ a) d :=
    GradedRingHom.map_directSumDecompose (𝒜 := 𝒜) (ℬ := ℬ) ψ
  have e : φ (DirectSum.decompose 𝒜 a d) = DirectSum.decompose ℬ (φ a) d := e₀
  have hb' : φ g ^ m * b ∈ ℬ d := mem_of_zero_mul (pow_mem_zero (hφ _ _ hg) m) hb
  have hφa : φ a = φ g ^ m * b := by
    rw [mul_comm, ← map_pow]
    exact h.symm
  rw [e, hφa]
  exact DirectSum.decompose_of_mem_same ℬ hb'

include hφ hg hloc in
/-- **The chart condition passes to `A[1/g]`**, `g ∈ A₀`, for a graded domain `A` and finitely many
coordinates. -/
theorem chartGood_of_isLocalizationAway [IsDomain A] {ι : Type*} [Fintype ι] (x : ι → A) {n : ℕ}
    (h : ChartGood 𝒜 x n) : ChartGood ℬ (φ ∘ x) n := by
  classical
  let := φ.toAlgebra
  intro a' s' hs' hcond
  have hu : IsUnit (φ g) := IsLocalization.Away.algebraMap_isUnit (S := B) g
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [map_zero, isUnit_zero_iff] at hu
    exact hs' (by rw [← mul_one s', ← hu, mul_zero])
  have hinj : Function.Injective φ :=
    IsLocalization.injective (M := Submonoid.powers g) B
      (powers_le_nonZeroDivisors_of_noZeroDivisors hg0)
  obtain ⟨⟨a, ⟨_, k, rfl⟩⟩, ha⟩ := IsLocalization.surj (Submonoid.powers g) a'
  obtain ⟨⟨s, ⟨_, l, rfl⟩⟩, hs⟩ := IsLocalization.surj (Submonoid.powers g) s'
  change a' * φ (g ^ k) = φ a at ha
  change s' * φ (g ^ l) = φ s at hs
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [map_zero] at hs
    exact hs' ((hu.pow l).mul_left_eq_zero.mp (by rw [← map_pow]; exact hs))
  -- Lift the chart condition to `A`.
  have hlift : ∀ i, ∃ (j m : ℕ) (c : A), c ∈ 𝒜 (j + n) ∧
      c * (s * g ^ k) = g ^ (m + l) * x i ^ j * a := fun i => by
    obtain ⟨j, c', hc', hcs'⟩ := hcond i
    obtain ⟨m, c, hc, hcc'⟩ := exists_mem_map_eq_pow_mul φ hφ hg hloc hc'
    refine ⟨j, m, c, hc, hinj ?_⟩
    simp only [map_mul, map_pow, Function.comp_apply] at hcc' hcs' ha hs ⊢
    rw [hcc', ← hs, ← ha]
    linear_combination (φ g ^ m * φ g ^ l * φ g ^ k) * hcs'
  choose j m c hc hcs using hlift
  let M := ∑ i, m i
  have hmM : ∀ i, m i ≤ M := fun i =>
    Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  obtain ⟨c₀, hc₀, hc₀s⟩ := h (g ^ (M + l) * a) (s * g ^ k)
    (mul_ne_zero hs0 (pow_ne_zero k hg0)) fun i => by
      refine ⟨j i, g ^ (M - m i) * c i, mem_of_zero_mul (pow_mem_zero hg _) (hc i), ?_⟩
      rw [mul_assoc, hcs i, show g ^ (M + l) = g ^ (M - m i) * g ^ (m i + l) by
        rw [← pow_add]; congr 1; have := hmM i; omega]
      ring
  -- Divide by the unit `g ^ M` in `B`.
  obtain ⟨v, hv, huv⟩ : ∃ v ∈ ℬ 0, φ g * v = 1 := by
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    exact exists_mem_zero_mul_eq_one (hφ _ _ hg) hw
  refine ⟨v ^ M * φ c₀, mem_of_zero_mul (pow_mem_zero hv M) (hφ _ _ hc₀), ?_⟩
  have e := congrArg φ hc₀s
  simp only [map_mul, map_pow] at e hs ha
  rw [← hs, ← ha, pow_add] at e
  have hk : IsUnit (φ g ^ k * φ g ^ l) := (hu.pow k).mul (hu.pow l)
  apply hk.mul_left_cancel
  calc φ g ^ k * φ g ^ l * (v ^ M * φ c₀ * s') = v ^ M * (φ c₀ * (s' * φ g ^ l * φ g ^ k)) := by
        ring
    _ = v ^ M * (φ g ^ M * φ g ^ l * (a' * φ g ^ k)) := by rw [e]
    _ = (φ g * v) ^ M * (φ g ^ k * φ g ^ l * a') := by ring
    _ = φ g ^ k * φ g ^ l * a' := by rw [huv, one_pow, one_mul]

include hφ hg hloc in
/-- **The chart condition on `A[1/g]` gives it on `A` up to a power of `g`.** -/
theorem exists_pow_mul_of_chartGood [IsDomain A] {ι : Type*} (x : ι → A) {n : ℕ}
    (h : ChartGood ℬ (φ ∘ x) n) (a s : A) (hs : s ≠ 0)
    (hcond : ∀ i, ∃ (j : ℕ) (c : A), c ∈ 𝒜 (j + n) ∧ c * s = x i ^ j * a) :
    ∃ (N : ℕ) (c : A), c ∈ 𝒜 n ∧ c * s = g ^ N * a := by
  let := φ.toAlgebra
  by_cases hφs : φ s = 0
  · obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers g) B s).1 hφs
    have hgk : g ^ k = 0 := (mul_eq_zero.1 hk).resolve_right hs
    exact ⟨k, 0, zero_mem _, by rw [hgk, zero_mul, zero_mul]⟩
  · obtain ⟨c', hc', hcs'⟩ := h (φ a) (φ s) hφs fun i => by
      obtain ⟨j, c, hc, hcs⟩ := hcond i
      exact ⟨j, φ c, hφ _ _ hc, by rw [Function.comp_apply, ← map_pow, ← map_mul, ← map_mul, hcs]⟩
    obtain ⟨m, c, hc, hcc'⟩ := exists_mem_map_eq_pow_mul φ hφ hg hloc hc'
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers g) (S := B)
      (x := c * s) (y := g ^ m * a) (by
        change φ (c * s) = φ (g ^ m * a)
        rw [map_mul, hcc', map_mul, map_pow, mul_assoc, hcs'])
    refine ⟨k + m, g ^ k * c, mem_of_zero_mul (pow_mem_zero hg k) hc, ?_⟩
    change g ^ k * (c * s) = g ^ k * (g ^ m * a) at hk
    rw [pow_add, mul_assoc, hk]
    ring

/-- **The chart condition descends from a cover of `Spec A₀`**: if `(gⱼ) = 1` with `gⱼ ∈ A₀` and,
for each `j`, every fraction satisfying the chart condition lies in `A_n` up to a power of `gⱼ`,
then `A` satisfies the chart condition in degree `n`. -/
theorem chartGood_of_forall_exists_pow_mul {ι κ : Type*} [Fintype κ] (x : ι → A) {n : ℕ}
    (g : κ → A) (hg : ∀ j, g j ∈ 𝒜 0)
    (hspan : ∀ N : ℕ, ∃ e : κ → A, (∀ j, e j ∈ 𝒜 0) ∧ ∑ j, e j * g j ^ N = 1)
    (hloc : ∀ j, ∀ a s : A, s ≠ 0 →
      (∀ i, ∃ (j : ℕ) (c : A), c ∈ 𝒜 (j + n) ∧ c * s = x i ^ j * a) →
        ∃ (N : ℕ) (c : A), c ∈ 𝒜 n ∧ c * s = g j ^ N * a) :
    ChartGood 𝒜 x n := by
  intro a s hs hcond
  choose N c hc hcs using fun j => hloc j a s hs hcond
  let M := ∑ j, N j
  have hNM : ∀ j, N j ≤ M := fun j =>
    Finset.single_le_sum (f := N) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  obtain ⟨e, he, hsum⟩ := hspan M
  refine ⟨∑ j, e j * (g j ^ (M - N j) * c j), sum_mem fun j _ =>
    mem_of_zero_mul (he j) (mem_of_zero_mul (pow_mem_zero (hg j) _) (hc j)), ?_⟩
  rw [Finset.sum_mul]
  calc ∑ j, e j * (g j ^ (M - N j) * c j) * s = ∑ j, e j * g j ^ M * a := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_assoc, mul_assoc, hcs j]
        rw [show g j ^ M = g j ^ (M - N j) * g j ^ N j by
          rw [← pow_add]; congr 1; have := hNM j; omega]
        ring
    _ = a := by rw [← Finset.sum_mul, hsum, one_mul]

end Algebra

/-! ### The relative homogeneous coordinate algebra -/

section Application

open Scheme.AffineZariskiSite

attribute [local instance] MvPolynomial.gradedAlgebra

variable {r : ℕ} {X Z : Scheme.{u}} (i : Z ⟶ projectiveSpaceOverScheme r X) [IsClosedImmersion i]
  [IsIntegral Z]

omit [IsClosedImmersion i] in
private theorem subsingleton_of_not_mem {U : X.AffineZariskiSite}
    (hη : genericPoint Z ∉ (i ≫ projectiveSpaceOverSchemeProjection r X) ⁻¹ᵁ U.1) :
    Subsingleton ((coordinateAlgebra i).obj.obj (op U)) :=
  Ideal.Quotient.subsingleton_iff.mpr (by rw [chartIdeal_of_not_mem i U.2 hη]; rfl)

omit [IsClosedImmersion i] in
private theorem isDomain_of_mem {U : X.AffineZariskiSite}
    (hη : genericPoint Z ∈ (i ≫ projectiveSpaceOverSchemeProjection r X) ⁻¹ᵁ U.1) :
    IsDomain ((coordinateAlgebra i).obj.obj (op U)) := by
  have : (chartIdeal i U.1 U.2).toIdeal.IsPrime := by
    rw [chartIdeal_of_mem i U.2 hη]
    exact (chartPoint i U.2 ⟨_, hη⟩).isPrime
  exact Ideal.Quotient.isDomain _

omit [IsClosedImmersion i] in
private theorem chartGood_of_not_mem {U : X.AffineZariskiSite}
    (hη : genericPoint Z ∉ (i ≫ projectiveSpaceOverSchemeProjection r X) ⁻¹ᵁ U.1) (n : ℕ) :
    ChartGood ((coordinateAlgebra i).grading U) (coordGen i U) n := by
  have := subsingleton_of_not_mem i hη
  intro a s hs
  exact absurd (Subsingleton.elim s 0) hs

private theorem not_irrelevant_le_bot {U : X.AffineZariskiSite}
    (hη : genericPoint Z ∈ (i ≫ projectiveSpaceOverSchemeProjection r X) ⁻¹ᵁ U.1) :
    ¬HomogeneousIdeal.irrelevant ((coordinateAlgebra i).grading U) ≤ ⊥ := fun hle =>
  ((chartIso i U.1 U.2).hom ⟨_, hη⟩).not_irrelevant_le (hle.trans bot_le)

/-- Over an affine open `U` with `f⁻¹(U)` nonempty, `T(U)_n → Γ(Proj T(U), 𝒪(n))` is bijective
exactly when `T(U)` satisfies the chart condition in degree `n`. -/
private theorem bijective_iff_chartGood {U : X.AffineZariskiSite}
    (hη : genericPoint Z ∈ (i ≫ projectiveSpaceOverSchemeProjection r X) ⁻¹ᵁ U.1) (n : ℕ) :
    Function.Bijective (fun a : gradedQuotient (MvPolynomial.homogeneousSubmodule (Fin (r + 1))
        Γ(X, U.1)) (chartIdeal i U.1 U.2) n => twistSection n a (op ⊤)) ↔
      ChartGood ((coordinateAlgebra i).grading U) (coordGen i U) n := by
  have := isDomain_of_mem i hη
  exact bijective_twistSection_iff_chartGood (coordGen i U) (coordGen_mem i U)
    (exists_coord_notMem_of_quotient _) (not_irrelevant_le_bot i hη) n

/-- In a degree where `T(U)` satisfies the chart condition, `T(U)_n → Γ(Proj T(U), 𝒪(n))` is
bijective. -/
private theorem bijective_of_chartGood {U : X.AffineZariskiSite} {n : ℕ}
    (h : ChartGood ((coordinateAlgebra i).grading U) (coordGen i U) n) :
    Function.Bijective (fun a : gradedQuotient (MvPolynomial.homogeneousSubmodule (Fin (r + 1))
      Γ(X, U.1)) (chartIdeal i U.1 U.2) n => twistSection n a (op ⊤)) := by
  by_cases hη : genericPoint Z ∈ (i ≫ projectiveSpaceOverSchemeProjection r X) ⁻¹ᵁ U.1
  · exact (bijective_iff_chartGood i hη n).2 h
  · have := subsingleton_of_not_mem i hη
    refine ⟨fun a b _ => Subtype.ext (Subsingleton.elim _ _), fun σ => ⟨0, ?_⟩⟩
    apply ProjGradedModuleSheaf.section_ext
    intro x
    exact (x.1.isPrime.ne_top (Subsingleton.elim _ _)).elim

omit [IsClosedImmersion i] in
private theorem coordRestrict_comp_coordGen (U : X.AffineZariskiSite) (g : Γ(X, U.1)) :
    coordRestrict i (U.basicOpen g).2 U.2 (X.basicOpen_le g) ∘ coordGen i U =
      coordGen i (U.basicOpen g) := by
  funext j
  simp only [Function.comp_apply, coordGen, coordRestrict_mk, MvPolynomial.map_X]

omit [IsClosedImmersion i] in
private theorem coordRestrict_mem (U : X.AffineZariskiSite) (g : Γ(X, U.1)) (d : ℕ)
    (a : (coordinateAlgebra i).obj.obj (op U)) (ha : a ∈ (coordinateAlgebra i).grading U d) :
    coordRestrict i (U.basicOpen g).2 U.2 (X.basicOpen_le g) a ∈
      (coordinateAlgebra i).grading (U.basicOpen g) d := by
  obtain ⟨p, hp, rfl⟩ := mem_gradedQuotient_iff.mp ha
  rw [coordRestrict_mk]
  exact mk_mem_gradedQuotient ((polyMap (r := r) _).map_mem hp)

omit [IsClosedImmersion i] in
private theorem C_mem_grading_zero (U : X.AffineZariskiSite) (g : Γ(X, U.1)) :
    Ideal.Quotient.mk (chartIdeal i U.1 U.2).toIdeal (MvPolynomial.C g) ∈
      (coordinateAlgebra i).grading U 0 :=
  mk_mem_gradedQuotient ((MvPolynomial.mem_homogeneousSubmodule _ _).2
    (MvPolynomial.isHomogeneous_C _ g))

omit [IsClosedImmersion i] in
/-- The chart condition for `T(U)` passes to `T(D(g)) = T(U)[1/g]`. -/
private theorem chartGood_basicOpen {U : X.AffineZariskiSite} (g : Γ(X, U.1)) {n : ℕ}
    (h : ChartGood ((coordinateAlgebra i).grading U) (coordGen i U) n) :
    ChartGood ((coordinateAlgebra i).grading (U.basicOpen g)) (coordGen i (U.basicOpen g)) n := by
  by_cases hη : genericPoint Z ∈ (i ≫ projectiveSpaceOverSchemeProjection r X) ⁻¹ᵁ U.1
  · have := isDomain_of_mem i hη
    have := chartGood_of_isLocalizationAway (𝒜 := (coordinateAlgebra i).grading U)
      (ℬ := (coordinateAlgebra i).grading (U.basicOpen g))
      (coordRestrict i (U.basicOpen g).2 U.2 (X.basicOpen_le g)) (coordRestrict_mem i U g)
      (C_mem_grading_zero i U g) (coordinateAlgebra_isLocalizationAway i U g) (coordGen i U) h
    rwa [coordRestrict_comp_coordGen] at this
  · exact chartGood_of_not_mem i
      (fun h' => hη ((i ≫ projectiveSpaceOverSchemeProjection r X).preimage_mono
        (X.basicOpen_le g) h')) n

omit [IsClosedImmersion i] in
/-- The chart condition for `T(U)` follows from the chart condition for the `T(D(f))`, `f ∈ t`,
when `t` generates the unit ideal of `Γ(X, U)`. -/
private theorem chartGood_of_cover {U : X.AffineZariskiSite} (t : Finset Γ(X, U.1))
    (ht : Ideal.span (t : Set Γ(X, U.1)) = ⊤) {n : ℕ}
    (h : ∀ f ∈ t, ChartGood ((coordinateAlgebra i).grading (U.basicOpen f))
      (coordGen i (U.basicOpen f)) n) :
    ChartGood ((coordinateAlgebra i).grading U) (coordGen i U) n := by
  classical
  by_cases hη : genericPoint Z ∈ (i ≫ projectiveSpaceOverSchemeProjection r X) ⁻¹ᵁ U.1
  · have := isDomain_of_mem i hη
    refine chartGood_of_forall_exists_pow_mul (coordGen i U)
      (fun f : {x // x ∈ t} => Ideal.Quotient.mk (chartIdeal i U.1 U.2).toIdeal
        (MvPolynomial.C f.1)) (fun f => C_mem_grading_zero i U f.1) (fun N => ?_)
      (fun f a s hs hcond => ?_)
    · have h1 : (1 : Γ(X, U.1)) ∈ Ideal.span (Set.range fun f : {x // x ∈ t} => f.1 ^ N) := by
        have := Ideal.span_range_pow_eq_top (t : Set Γ(X, U.1)) ht (fun _ => N)
        rw [Ideal.eq_top_iff_one] at this
        exact this
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun Γ(X, U.1)).1 h1
      refine ⟨fun f => Ideal.Quotient.mk (chartIdeal i U.1 U.2).toIdeal (MvPolynomial.C (c f)),
        fun f => C_mem_grading_zero i U (c f), ?_⟩
      simp only [← map_pow, ← map_mul, ← map_sum]
      rw [show ∑ f : {x // x ∈ t}, c f * f.1 ^ N = 1 by simpa only [smul_eq_mul] using hc,
        map_one, map_one]
    · have hf := h f.1 f.2
      rw [← coordRestrict_comp_coordGen] at hf
      exact exists_pow_mul_of_chartGood (𝒜 := (coordinateAlgebra i).grading U)
        (ℬ := (coordinateAlgebra i).grading (U.basicOpen f.1))
        (coordRestrict i (U.basicOpen f.1).2 U.2 (X.basicOpen_le f.1))
        (coordRestrict_mem i U f.1) (C_mem_grading_zero i U f.1)
        (coordinateAlgebra_isLocalizationAway i U f.1) (coordGen i U) hf a s hs hcond
  · exact chartGood_of_not_mem i hη n

/-- **The uniform bound** (Hartshorne II, proof of Theorem 7.17, Step 2). Let `X` be quasi-compact
and locally of finite type over a field `k`. There is a `d₀` such that for every affine open
`U ⊆ X` and every `n ≥ d₀`, `T(U)_n → Γ(Proj T(U), 𝒪(n))`, `s ↦ s / 1`, is bijective. -/
theorem exists_bound_bijective_twistSection (k : Type u) [Field k] [CompactSpace X]
    (pX : X ⟶ Spec (.of k)) [LocallyOfFiniteType pX] :
    ∃ d₀ : ℕ, ∀ (U : X.AffineZariskiSite) (n : ℕ), d₀ ≤ n →
      Function.Bijective (fun a : gradedQuotient (MvPolynomial.homogeneousSubmodule (Fin (r + 1))
        Γ(X, U.1)) (chartIdeal i U.1 U.2) n => twistSection n a (op ⊤)) := by
  classical
  have hbound : ∀ U : X.AffineZariskiSite, ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ChartGood ((coordinateAlgebra i).grading U) (coordGen i U) n := fun U => by
    obtain ⟨_, _⟩ := exists_algebra_finiteType_of_locallyOfFiniteType k pX U.2
    obtain ⟨n₀, hn₀⟩ := exists_bijective_twistSection_quotient k (chartIdeal i U.1 U.2)
    refine ⟨n₀, fun n hn => ?_⟩
    by_cases hη : genericPoint Z ∈ (i ≫ projectiveSpaceOverSchemeProjection r X) ⁻¹ᵁ U.1
    · exact (bijective_iff_chartGood i hη n).1 (hn₀ n hn)
    · exact chartGood_of_not_mem i hη n
  let n₀ : X.AffineZariskiSite → ℕ := fun U => (hbound U).choose
  have hn₀ : ∀ U, ∀ n ≥ n₀ U, ChartGood ((coordinateAlgebra i).grading U) (coordGen i U) n :=
    fun U => (hbound U).choose_spec
  have hcov : ∃ s : Finset X.affineOpens, ∀ x : X, ∃ V ∈ s, x ∈ (V : X.Opens) := by
    obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => (U : Set X))
      (fun U => U.1.isOpen) (fun x _ => by
        obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (x := x)
          (U := (⊤ : X.Opens)) trivial
        exact Set.mem_iUnion.mpr ⟨⟨W, hW⟩, hxW⟩)
    refine ⟨s, fun x => ?_⟩
    obtain ⟨V, hV, hxV⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact ⟨V, hV, hxV⟩
  obtain ⟨s, hs⟩ := hcov
  refine ⟨s.sup fun V => n₀ ⟨V.1, V.2⟩, fun U n hn => bijective_of_chartGood i ?_⟩
  have hspan : Ideal.span {f : Γ(X, U.1) | ChartGood ((coordinateAlgebra i).grading
      (U.basicOpen f)) (coordGen i (U.basicOpen f)) n} = ⊤ := by
    rw [← U.2.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨V, hV, hxV⟩ := hs x
    obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter U.2 V.2 x ⟨hx, hxV⟩
    have hgood := chartGood_basicOpen i (U := ⟨V.1, V.2⟩) g (hn₀ ⟨V.1, V.2⟩ n
      ((Finset.le_sup (f := fun V : X.affineOpens => n₀ ⟨V.1, V.2⟩) hV).trans hn))
    have heq : U.basicOpen f = Scheme.AffineZariskiSite.basicOpen ⟨V.1, V.2⟩ g := Subtype.ext hfg
    have hf : ChartGood ((coordinateAlgebra i).grading (U.basicOpen f))
        (coordGen i (U.basicOpen f)) n := by
      rw [heq]
      exact hgood
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨f, hf⟩, hxf⟩
  obtain ⟨t, hts, ht⟩ := (Ideal.span_eq_top_iff_finite _).1 hspan
  exact chartGood_of_cover i t ht fun f hf => hts hf

end Application

end SectionAlgebraModel

end Hartshorne

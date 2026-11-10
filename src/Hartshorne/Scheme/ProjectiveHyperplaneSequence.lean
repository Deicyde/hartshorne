/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ProjTwistPullback
import Hartshorne.Scheme.ProjSurjectionClosedImmersion

/-!
# The hyperplane sequence on projective space (partial)

Hartshorne, *Algebraic Geometry*, III.5, proof of Theorem 5.1(b) (p. 227).

Let `x ∈ S_1` and let `φ : S → T` be a graded ring map with `φ(x) = 0`. Multiplication by `x`
is a map of graded modules `S(n-1) → S(n)`, which gives `𝒪(n-1) ⟶ 𝒪(n)` (`mulSection`). Its
composite with the restriction `𝒪_{Proj S}(n) ⟶ f_*(𝒪_{Proj T}(n)|_U)` of the partial Proj
morphism `f` is zero (`mulSection_psi`).

For `X = ℙ^{m+1}_A = Proj A[x_0, …, x_{m+1}]` and `H = V₊(x_{m+1})`, `hyperplaneHom` is the
surjective graded map `A[x_0, …, x_{m+1}] → A[x_0, …, x_m]` with `x_{m+1} ↦ 0`. Its partial Proj
morphism is defined on all of `ℙ^m_A` and is a closed immersion with image `H`.
-/

universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Hartshorne.HyperplaneSequence

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace HomogeneousLocalization
  ProjGradedModuleSheaf ProjTwistMap

section General

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

omit [AddSubgroupClass τ B] [GradedRing ℬ] in
theorem mem_of_map_mem (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f) (p : ProjectiveSpectrum 𝒜)
    (hp : ∀ a, f a = 0 → a ∈ p.asHomogeneousIdeal) {a : A}
    (h : f a ∈ p.asHomogeneousIdeal.toIdeal.map f) : a ∈ p.asHomogeneousIdeal := by
  have : a ∈ (p.asHomogeneousIdeal.toIdeal.map f).comap f := h
  rw [Ideal.comap_map_of_surjective _ hf, sup_eq_left.2 fun b hb => hp b (by simpa using hb)]
    at this
  exact this

/-- The point of `Proj T` over a point `p ⊇ ker f` of `Proj S`, for `f` surjective. -/
def liftPoint (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f) (p : ProjectiveSpectrum 𝒜)
    (hp : ∀ a, f a = 0 → a ∈ p.asHomogeneousIdeal) : ProjectiveSpectrum ℬ where
  asHomogeneousIdeal := p.asHomogeneousIdeal.map f
  isPrime := by
    rw [HomogeneousIdeal.toIdeal_map]
    exact Ideal.map_isPrime_of_surjective hf fun a ha => hp a ha
  not_irrelevant_le h := by
    refine p.not_irrelevant_le fun a ha => ?_
    have hfa : f a ∈ HomogeneousIdeal.irrelevant ℬ := by
      rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
        ← GradedRingHom.map_directSumDecompose]
      rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply] at ha
      rw [ha, map_zero]
    exact mem_of_map_mem f hf p hp (h hfa)

theorem mem_liftPoint_iff (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f) (p : ProjectiveSpectrum 𝒜)
    (hp : ∀ a, f a = 0 → a ∈ p.asHomogeneousIdeal) (a : A) :
    f a ∈ (liftPoint f hf p hp).asHomogeneousIdeal ↔ a ∈ p.asHomogeneousIdeal :=
  ⟨mem_of_map_mem f hf p hp, fun h => Ideal.mem_map_of_mem _ h⟩

omit [AddSubgroupClass τ B] [GradedRing ℬ] in
/-- Homogeneous elements of the kernel are multiples of `x` by homogeneous elements. -/
theorem exists_mem_eq_mul {x : A} (hx : x ∈ 𝒜 1) (f : 𝒜 →+*ᵍ ℬ)
    (hker : ∀ a, f a = 0 → ∃ b, a = x * b) {e : ℕ} {a : A} (ha : a ∈ 𝒜 (1 + e)) (hfa : f a = 0) :
    ∃ b ∈ 𝒜 e, a = x * b := by
  obtain ⟨b, rfl⟩ := hker a hfa
  refine ⟨DirectSum.decompose 𝒜 b e, SetLike.coe_mem _, ?_⟩
  rw [← DirectSum.coe_decompose_mul_add_of_left_mem 𝒜 hx, DirectSum.decompose_of_mem_same _ ha]

omit [AddSubgroupClass τ B] [GradedRing ℬ] in
theorem eq_zero_of_mem_zero {x : A} (hx : x ∈ 𝒜 1) (f : 𝒜 →+*ᵍ ℬ)
    (hker : ∀ a, f a = 0 → ∃ b, a = x * b) {a : A} (ha : a ∈ 𝒜 0) (hfa : f a = 0) : a = 0 := by
  obtain ⟨b, rfl⟩ := hker a hfa
  rw [← DirectSum.decompose_of_mem_same _ ha,
    DirectSum.coe_decompose_mul_of_left_mem_of_not_le 𝒜 hx (by omega)]

/-- If `u c = 0` with `c` homogeneous and `u ∉ z`, some homogeneous component of `u` is not in
`z` and kills `c`. -/
theorem exists_homogeneous_mul_eq_zero (z : ProjectiveSpectrum ℬ) {u c : B} {j : ℕ}
    (hc : c ∈ ℬ j) (huc : u * c = 0) (hu : u ∉ z.asHomogeneousIdeal) :
    ∃ i, (DirectSum.decompose ℬ u i : B) ∉ z.asHomogeneousIdeal ∧
      (DirectSum.decompose ℬ u i : B) * c = 0 := by
  have hall : ∀ i, (DirectSum.decompose ℬ u i : B) * c = 0 := fun i => by
    rw [← DirectSum.coe_decompose_mul_add_of_right_mem ℬ hc, huc]
    simp
  obtain ⟨i, hi⟩ : ∃ i, (DirectSum.decompose ℬ u i : B) ∉ z.asHomogeneousIdeal := by
    by_contra! h
    exact hu ((z.asHomogeneousIdeal.isHomogeneous.mem_iff ℬ).2 h)
  exact ⟨i, hi, hall i⟩

/-- Multiplication by a degree-one element maps `S(n-1)_i` into `S(n)_i`. -/
theorem mul_mem_gradedTwist {x : A} (hx : x ∈ 𝒜 1) (n : ℤ) {i : ℤ} {m : A}
    (hm : m ∈ gradedTwist 𝒜 (n - 1) i) : x * m ∈ gradedTwist 𝒜 n i := by
  obtain ⟨hm1, hm2⟩ := hm
  by_cases h : n - 1 + i < 0
  · rw [hm2 h, mul_zero]
    exact zero_mem _
  · exact (mem_gradedTwist_of_eq (k := 1 + (n - 1 + i).toNat) (by omega)).2
      (SetLike.GradedMul.mul_mem hx hm1)

variable {x : A} (hx : x ∈ 𝒜 1) (n : ℤ)

/-- Multiplication by `x ∈ S_1`, `𝒪_{Proj S}(n-1) ⟶ 𝒪_{Proj S}(n)`. -/
def mulSection : projTwistingSheaf 𝒜 (n - 1) ⟶ projTwistingSheaf 𝒜 n :=
  projGradedModuleSheafMap (ℳ := gradedTwist 𝒜 (n - 1)) (𝒩 := gradedTwist 𝒜 n)
    (LinearMap.mulLeft A x) fun _ _ hm => mul_mem_gradedTwist hx n hm

/-- On fibers, multiplication by `x` followed by `φ` is zero when `φ(x) = 0`. -/
theorem twistFiber_gradedLocMap_mul (f : 𝒜 →+*ᵍ ℬ) (hfx : f x = 0) {P : Submonoid A}
    {Q : Submonoid B} (h : P ≤ Q.comap f)
    (y : HomogeneousLocalizedModule 𝒜 (gradedTwist 𝒜 (n - 1)) P) :
    twistFiber f n h (gradedLocMap (ℳ := gradedTwist 𝒜 (n - 1)) (𝒩 := gradedTwist 𝒜 n)
      (LinearMap.mulLeft A x) (fun _ _ hm => mul_mem_gradedTwist hx n hm) P y) = 0 := by
  obtain ⟨k, m, hm, t, ht, htP, rfl⟩ := HomogeneousLocalizedModule.mk_surjective y
  apply HomogeneousLocalizedModule.ext
  rw [val_twistFiber]
  change locMap f h (IsLocalizedModule.map P (LocalizedModule.mkLinearMap P A)
    (LocalizedModule.mkLinearMap P A) (LinearMap.mulLeft A x)
    (HomogeneousLocalizedModule.mk k m hm t ht htP).val) = 0
  rw [HomogeneousLocalizedModule.val_mk, IsLocalizedModule.map_LocalizedModules, locMap_mk]
  simp [map_mul, hfx]

/-- Multiplication by `x` followed by the restriction to `Proj T` is zero when `φ(x) = 0`. -/
theorem mulSection_psi (f : 𝒜 →+*ᵍ ℬ) (hfx : f x = 0) :
    mulSection hx n ≫ ProjTwistPullback.psi f n = 0 := by
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  ext s
  refine Subtype.ext (funext fun z => ?_)
  exact twistFiber_gradedLocMap_mul hx n f hfx _ _

/-- If `x` is a non-zero-divisor, multiplication by `x` is injective on fibers. -/
theorem gradedLocMap_mul_injective (hinj : Function.Injective (x * ·)) (P : Submonoid A) :
    Function.Injective (gradedLocMap (𝒜 := 𝒜) (ℳ := gradedTwist 𝒜 (n - 1)) (𝒩 := gradedTwist 𝒜 n)
      (LinearMap.mulLeft A x) (fun _ _ hm => mul_mem_gradedTwist hx n hm) P) := by
  intro y z h
  apply HomogeneousLocalizedModule.ext
  exact IsLocalizedModule.map_injective P (LocalizedModule.mkLinearMap P A)
    (LocalizedModule.mkLinearMap P A) (LinearMap.mulLeft A x) hinj (congrArg (·.val) h)

theorem mulSection_app_injective (hinj : Function.Injective (x * ·))
    (U : (Proj 𝒜).Opensᵒᵖ) : Function.Injective ((mulSection hx n).val.app U) := by
  intro s t h
  refine Subtype.ext (funext fun p => ?_)
  exact gradedLocMap_mul_injective hx n hinj _ (congrFun (congrArg Subtype.val h) p)

/-- If `x` is a non-zero-divisor, multiplication by `x` is a monomorphism. -/
theorem mono_mulSection (hinj : Function.Injective (x * ·)) : Mono (mulSection hx n) := by
  apply (SheafOfModules.forget _).mono_of_mono_map
  exact PresheafOfModules.mono_of_injective fun U => mulSection_app_injective hx n hinj U

end General

section ProjectiveSpace

variable (A : Type u) [CommRing A] (m : ℕ)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The coordinate substitution `x_i ↦ x_i` (`i ≤ m`), `x_{m+1} ↦ 0`. -/
abbrev hyperplaneSubst : Fin (m + 2) → MvPolynomial (Fin (m + 1)) A :=
  Fin.lastCases 0 MvPolynomial.X

/-- **The hyperplane restriction** `A[x_0, …, x_{m+1}] → A[x_0, …, x_m]`, `x_{m+1} ↦ 0`, as a
graded ring map. -/
def hyperplaneHom :
    MvPolynomial.homogeneousSubmodule (Fin (m + 2)) A →+*ᵍ
      MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A where
  toRingHom := (MvPolynomial.aeval (hyperplaneSubst A m)).toRingHom
  map_mem {k} φ hφ := by
    have h := (MvPolynomial.mem_homogeneousSubmodule k φ).1 hφ
    refine (MvPolynomial.mem_homogeneousSubmodule k _).2 ?_
    have := h.eval₂ (algebraMap A (MvPolynomial (Fin (m + 1)) A)) (hyperplaneSubst A m)
      (fun r => MvPolynomial.isHomogeneous_C _ r) (n := 1) (fun i => by
        induction i using Fin.lastCases with
        | last => simpa using MvPolynomial.isHomogeneous_zero _ _ 1
        | cast i => simpa using MvPolynomial.isHomogeneous_X A i)
    rw [one_mul] at this
    exact this

theorem hyperplaneHom_apply (φ : MvPolynomial (Fin (m + 2)) A) :
    hyperplaneHom A m φ = MvPolynomial.aeval (hyperplaneSubst A m) φ :=
  rfl

theorem hyperplaneHom_X_last : hyperplaneHom A m (MvPolynomial.X (Fin.last (m + 1))) = 0 := by
  simp [hyperplaneHom_apply]

theorem hyperplaneHom_surjective : Function.Surjective (hyperplaneHom A m) := by
  intro ψ
  induction ψ using MvPolynomial.induction_on with
  | C a => exact ⟨MvPolynomial.C a, by simp [hyperplaneHom_apply]⟩
  | add p q hp hq =>
    obtain ⟨p', rfl⟩ := hp
    obtain ⟨q', rfl⟩ := hq
    exact ⟨p' + q', map_add _ _ _⟩
  | mul_X p i hp =>
    obtain ⟨p', rfl⟩ := hp
    exact ⟨p' * MvPolynomial.X i.castSucc, by simp [hyperplaneHom_apply]⟩

theorem x_last_mem : (MvPolynomial.X (Fin.last (m + 1)) : MvPolynomial (Fin (m + 2)) A) ∈
    MvPolynomial.homogeneousSubmodule (Fin (m + 2)) A 1 :=
  (MvPolynomial.mem_homogeneousSubmodule 1 _).2 (MvPolynomial.isHomogeneous_X A _)

/-- The hyperplane `H = V₊(x_{m+1}) ≅ ℙ^m_A` maps to `ℙ^{m+1}_A` by a closed immersion. -/
theorem isClosedImmersion_hyperplane :
    IsClosedImmersion (projPartialMap (hyperplaneHom A m)) :=
  isClosedImmersion_projPartialMap_of_surjective (hyperplaneHom_surjective A m)

/-- **Multiplication by `x_{m+1}` followed by restriction to the hyperplane is zero**:
`𝒪_X(n-1) ⟶ 𝒪_X(n) ⟶ i_* 𝒪_H(n)`. -/
theorem mulSection_psi_hyperplane (n : ℤ) :
    mulSection (x_last_mem A m) n ≫ ProjTwistPullback.psi (hyperplaneHom A m) n = 0 :=
  mulSection_psi _ n _ (hyperplaneHom_X_last A m)

/-- **Multiplication by `x_{m+1}` is injective**: `𝒪_X(n-1) ⟶ 𝒪_X(n)` is a monomorphism. -/
instance mono_mulSection_hyperplane (n : ℤ) : Mono (mulSection (x_last_mem A m) n) :=
  mono_mulSection _ n MvPolynomial.isRegular_X.left

/-- `x_{m+1}` divides `a - a(x_0, …, x_m, 0)`. -/
theorem X_last_dvd_sub (a : MvPolynomial (Fin (m + 2)) A) :
    MvPolynomial.X (Fin.last (m + 1)) ∣
      a - MvPolynomial.rename Fin.castSucc (hyperplaneHom A m a) := by
  induction a using MvPolynomial.induction_on with
  | C c => simp [hyperplaneHom_apply]
  | add p q hp hq =>
    rw [map_add, map_add, add_sub_add_comm]
    exact dvd_add hp hq
  | mul_X p i hp =>
    induction i using Fin.lastCases with
    | last => simp [hyperplaneHom_apply]
    | cast j =>
      have e : p * MvPolynomial.X j.castSucc -
          MvPolynomial.rename Fin.castSucc (hyperplaneHom A m (p * MvPolynomial.X j.castSucc)) =
          (p - MvPolynomial.rename Fin.castSucc (hyperplaneHom A m p)) *
            MvPolynomial.X j.castSucc := by
        simp [hyperplaneHom_apply, sub_mul]
      rw [e]
      exact dvd_mul_of_dvd_left hp _

/-- The kernel of `hyperplaneHom` is generated by `x_{m+1}`. -/
theorem exists_eq_X_last_mul {a : MvPolynomial (Fin (m + 2)) A} (ha : hyperplaneHom A m a = 0) :
    ∃ b, a = MvPolynomial.X (Fin.last (m + 1)) * b := by
  obtain ⟨b, hb⟩ := X_last_dvd_sub A m a
  rw [ha, map_zero, sub_zero] at hb
  exact ⟨b, hb⟩

end ProjectiveSpace

end Hartshorne.HyperplaneSequence

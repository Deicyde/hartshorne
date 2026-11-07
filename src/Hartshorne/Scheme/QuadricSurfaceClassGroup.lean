/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.QuadricSurface
import Hartshorne.Scheme.AffineLineClassGroup
import Hartshorne.Scheme.AffineUFDClassGroup
import Hartshorne.Scheme.ClassGroupOpenRestriction
import Hartshorne.Scheme.HeightOneLocalizationIntersection
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# The class group of the split quadric surface

Hartshorne, *Algebraic Geometry*, II.6, Example 6.6.1 (p. 135).

Let `Q = Proj` of the Segre ring of `ℙ¹ × ℙ¹` (the quadric `xy = zw` of `ℙ³_k`, see
`Hartshorne.quadricSurface`), with bihomogeneous coordinates `s₀, s₁` and `u₀, u₁`. Let `L₁` be
the line `s₀ = 0` (a fibre of the first projection) and `L₂` the line `u₀ = 0` (a fibre of the
second projection). They are the two components of the hyperplane section `w = s₀u₀ = 0`.

## Proof

The complement `Q - L₁ - L₂` is the chart `D₊(s₀u₀)`, an affine plane, whose coordinate ring is a
UFD. A prime divisor `Y` meeting the chart corresponds to a height-one prime `(π)` of the plane;
a rational function `F` on `Q` restricting to `π` has divisor `Y` on the chart, and the only prime
divisors outside the chart are `L₁` and `L₂`, so `Y ~ -a L₁ - b L₂` for suitable integers. Hence
`ℤ² → Cl Q`, `(a, b) ↦ a L₁ + b L₂`, is surjective. If `a L₁ + b L₂` is the divisor of `F`, then
`F` restricted to the chart has no zeros or poles, so it is a unit of the polynomial ring, i.e. a
nonzero constant; constants have trivial divisor on `Q`, so `a = b = 0`.

The lines are codimension one: on the chart `D₊(s₁u₁) ≅ 𝔸²` the line `L₁` is minimal over the
principal ideal `(s₀u₁ / s₁u₁)`, so its height is one by Krull's principal ideal theorem.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory AddMonoidAlgebra HomogeneousLocalization Order

namespace Hartshorne

universe u

variable (k : Type u) [Field k]

local notation "𝒬" => quadricGrading k

section Lines

variable (ℓ : quadricExponents →+ ℕ)

/-- The ideal of the Segre ring spanned by the monomials `m` with `ℓ m ≠ 0`. -/
def quadricLineIdeal : Ideal (QuadricRing k) :=
  Ideal.span {a | ∃ p, ℓ p ≠ 0 ∧ a = single p 1}

theorem single_mem_quadricLineIdeal {p : quadricExponents} (hp : ℓ p ≠ 0) (c : k) :
    single p c ∈ quadricLineIdeal k ℓ := by
  have : single p c = single 0 c * single p 1 := by rw [single_mul_single, zero_add, mul_one]
  rw [this]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨p, hp, rfl⟩)

/-- The ideal of the elements all of whose monomials `m` satisfy `ℓ m ≠ 0`. -/
def quadricSupportIdeal : Ideal (QuadricRing k) where
  carrier := {a | ∀ p ∈ a.coeff.support, ℓ p ≠ 0}
  add_mem' {a b} ha hb p hp := by
    classical
    rw [coeff_add] at hp
    rcases Finset.mem_union.mp (Finsupp.support_add hp) with h | h
    exacts [ha p h, hb p h]
  zero_mem' p hp := by simp at hp
  smul_mem' c a ha p hp := by
    classical
    obtain ⟨q, -, r, hr, rfl⟩ := Finset.mem_add.mp (support_coeff_mul_subset c a hp)
    rw [map_add]
    have := ha r hr
    omega

theorem mem_quadricLineIdeal_iff (a : QuadricRing k) :
    a ∈ quadricLineIdeal k ℓ ↔ ∀ p ∈ a.coeff.support, ℓ p ≠ 0 := by
  constructor
  · intro ha
    have hle : quadricLineIdeal k ℓ ≤ quadricSupportIdeal k ℓ := by
      rw [quadricLineIdeal, Ideal.span_le]
      rintro _ ⟨p, hp, rfl⟩ q hq
      rw [coeff_single] at hq
      rwa [Finset.mem_singleton.mp (Finsupp.support_single_subset hq)]
    exact hle ha
  · intro ha
    rw [← sum_coeff_single a, Finsupp.sum]
    exact Ideal.sum_mem _ fun p hp => single_mem_quadricLineIdeal k ℓ (ha p hp) _

theorem quadricLineIdeal_isHomogeneous : (quadricLineIdeal k ℓ).IsHomogeneous 𝒬 := by
  apply Ideal.homogeneous_span
  rintro _ ⟨p, -, rfl⟩
  exact ⟨quadricDegree p, single_mem_quadricGrading k p 1⟩

/-- Setting to zero the monomials `m` with `ℓ m ≠ 0`, on monomials. -/
def quadricLineKillMonoidHom : Multiplicative quadricExponents →* QuadricRing k where
  toFun p := if ℓ p.toAdd = 0 then single p.toAdd 1 else 0
  map_one' := by simp [one_def]
  map_mul' p q := by
    simp only [toAdd_mul, map_add, Nat.add_eq_zero_iff]
    by_cases hp : ℓ p.toAdd = 0 <;> by_cases hq : ℓ q.toAdd = 0 <;>
      simp [hp, hq, single_mul_single]

/-- The ring endomorphism setting to zero the monomials `m` with `ℓ m ≠ 0`. -/
def quadricLineKill : QuadricRing k →ₐ[k] QuadricRing k :=
  lift k (QuadricRing k) quadricExponents (quadricLineKillMonoidHom k ℓ)

theorem coeff_quadricLineKill (a : QuadricRing k) (q : quadricExponents) :
    (quadricLineKill k ℓ a).coeff q = if ℓ q = 0 then a.coeff q else 0 := by
  classical
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, coeff_add, Finsupp.add_apply, hx, hy, coeff_add, Finsupp.add_apply]
    split_ifs <;> simp
  | single p c =>
    rw [quadricLineKill, lift_single]
    change (c • (if ℓ p = 0 then single p (1 : k) else 0)).coeff q = _
    by_cases hpq : p = q
    · subst hpq
      by_cases hp : ℓ p = 0
      · simp [hp, coeff_single]
      · simp [hp]
    · by_cases hp : ℓ p = 0
      · simp [hp, coeff_single, hpq]
      · simp [hp, coeff_single, hpq]

theorem quadricLineKill_eq_zero_iff (a : QuadricRing k) :
    quadricLineKill k ℓ a = 0 ↔ a ∈ quadricLineIdeal k ℓ := by
  rw [mem_quadricLineIdeal_iff]
  constructor
  · intro h p hp hℓ
    have := congrArg (fun b : QuadricRing k => b.coeff p) h
    simp only [coeff_quadricLineKill, if_pos hℓ] at this
    exact (Finsupp.mem_support_iff.mp hp) (by simpa using this)
  · intro h
    rw [← coeff_inj]
    ext q
    rw [coeff_quadricLineKill]
    split_ifs with hq
    · by_contra hne
      exact h q (Finsupp.mem_support_iff.mpr (by simpa using hne)) hq
    · simp

instance quadricLineIdeal_isPrime : (quadricLineIdeal k ℓ).IsPrime := by
  have : quadricLineIdeal k ℓ =
      RingHom.ker (quadricLineKill k ℓ : QuadricRing k →+* QuadricRing k) := by
    ext a
    rw [RingHom.mem_ker]
    exact (quadricLineKill_eq_zero_iff k ℓ a).symm
  rw [this]
  exact RingHom.ker_isPrime _

variable {ℓ}

/-- The point of `Q` whose homogeneous prime is spanned by the monomials with `ℓ ≠ 0`, when the
coordinate `s₁u₁` is not one of them. -/
def quadricLinePoint (hℓ : ℓ (quadricChartExp 1 1) = 0) : quadricSurface k :=
  ⟨⟨quadricLineIdeal k ℓ, quadricLineIdeal_isHomogeneous k ℓ⟩, quadricLineIdeal_isPrime k ℓ,
    fun h => (mem_quadricLineIdeal_iff k ℓ _).mp (h (quadricChart_mem_irrelevant k 1 1))
      (quadricChartExp 1 1) (by simp [quadricChart, coeff_single]) hℓ⟩

theorem quadricLinePoint_ideal (hℓ : ℓ (quadricChartExp 1 1) = 0) :
    (quadricLinePoint k hℓ).asHomogeneousIdeal.toIdeal = quadricLineIdeal k ℓ :=
  rfl

theorem quadricSurface_specializes_iff (x y : quadricSurface k) :
    x ⤳ y ↔ x.asHomogeneousIdeal.toIdeal ≤ y.asHomogeneousIdeal.toIdeal :=
  quadricSurface_specializes_iff_le k x y

theorem quadricSurface_ext {x y : quadricSurface k}
    (h : x.asHomogeneousIdeal.toIdeal = y.asHomogeneousIdeal.toIdeal) : x = y :=
  ProjectiveSpectrum.ext (HomogeneousIdeal.toIdeal_injective h)

/-- If a prime contains `t` but not `y`, and every monomial `p` with `ℓ p ≠ 0` satisfies
`p y = t p'`, then the prime contains the line ideal of `ℓ`. -/
theorem quadricLineIdeal_le_of_shift {q : Ideal (QuadricRing k)} [q.IsPrime]
    {y t : quadricExponents} (hy : single y (1 : k) ∉ q) (ht : single t (1 : k) ∈ q)
    (hshift : ∀ p, ℓ p ≠ 0 → ∃ p', p + y = t + p') : quadricLineIdeal k ℓ ≤ q := by
  rw [quadricLineIdeal, Ideal.span_le]
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨p', hp'⟩ := hshift p hp
  have h : single p (1 : k) * single y 1 = single t 1 * single p' 1 := by
    rw [single_mul_single, single_mul_single, hp']
  have hmem : single p (1 : k) * single y 1 ∈ q := h ▸ Ideal.mul_mem_right _ _ ht
  exact (Ideal.IsPrime.mem_or_mem ‹_› hmem).resolve_right hy

/-- If a prime contains `a` and `b`, and every monomial `p` with `ℓ p ≠ 0` is divisible by `a` or
by `b`, then the prime contains the line ideal of `ℓ`. -/
theorem quadricLineIdeal_le_of_dvd {q : Ideal (QuadricRing k)} {a b : quadricExponents}
    (ha : single a (1 : k) ∈ q) (hb : single b (1 : k) ∈ q)
    (hdvd : ∀ p, ℓ p ≠ 0 → ∃ p', p = a + p' ∨ p = b + p') : quadricLineIdeal k ℓ ≤ q := by
  rw [quadricLineIdeal, Ideal.span_le]
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨p', hp' | hp'⟩ := hdvd p hp
  · rw [hp', ← one_mul (1 : k), ← single_mul_single]
    exact Ideal.mul_mem_right _ _ ha
  · rw [hp', ← one_mul (1 : k), ← single_mul_single]
    exact Ideal.mul_mem_right _ _ hb

/-- Two codimension-one points, one specializing to the other, are equal. -/
theorem eq_of_coheight_eq_one_of_specializes {X : Scheme.{u}} {x y : X}
    (hx : coheight x = 1) (hy : coheight y = 1) (h : y ⤳ x) : x = y := by
  have hle : x ≤ y := Scheme.le_iff_specializes.mpr h
  by_cases hyx : y ≤ x
  · exact ((Scheme.le_iff_specializes.mp hyx).antisymm h).eq
  · have := coheight_add_one_le (lt_of_le_not_ge hle hyx)
    rw [hx, hy] at this
    exact absurd this (by decide)

variable (ℓ) in
/-- **The lines have codimension one.** If `t` has degree one, `ℓ t ≠ 0`, and every monomial `p`
with `ℓ p ≠ 0` satisfies `p · s₁u₁ = t · p'`, then the line point of `ℓ` has codimension one: on
the chart `D₊(s₁u₁)` its prime is minimal over the principal ideal `(t / s₁u₁)`. -/
theorem coheight_quadricLinePoint (hℓ : ℓ (quadricChartExp 1 1) = 0) {t : quadricExponents}
    (ht1 : quadricDegree t = 1) (htℓ : ℓ t ≠ 0)
    (hshift : ∀ p, ℓ p ≠ 0 → ∃ p', p + quadricChartExp 1 1 = t + p') :
    coheight (quadricLinePoint k hℓ) = 1 := by
  set η := quadricLinePoint k hℓ with hη_def
  have hy11 : quadricChartExp 1 1 ∈ (quadricChart k 1 1).coeff.support := by
    simp [quadricChart, coeff_single]
  have hmemt : single t (1 : k) ∈ 𝒬 1 := by
    simpa [ht1] using single_mem_quadricGrading k t 1
  let φ := Proj.awayι 𝒬 (quadricChart k 1 1) (quadricChart_mem k 1 1) Nat.one_pos
  have hη : η ∈ Proj.basicOpen 𝒬 (quadricChart k 1 1) := by
    rw [Proj.mem_basicOpen]
    intro h
    exact (mem_quadricLineIdeal_iff k ℓ _).mp h (quadricChartExp 1 1) hy11 hℓ
  obtain ⟨v, hv⟩ : η ∈ Set.range φ.base := by
    rw [← Scheme.Hom.coe_opensRange, Proj.opensRange_awayι]
    exact hη
  have hpre : ∀ v' : Spec (CommRingCat.of (Away 𝒬 (quadricChart k 1 1))),
      Away.isLocalizationElem (quadricChart_mem k 1 1) hmemt ∈ v'.asIdeal ↔
        single t (1 : k) ∈ (φ.base v').asHomogeneousIdeal := by
    intro v'
    have := congrArg (fun U : (Spec (CommRingCat.of (Away 𝒬 (quadricChart k 1 1)))).Opens =>
      v' ∈ U) (Proj.awayι_preimage_basicOpen 𝒬 (quadricChart_mem k 1 1) Nat.one_pos hmemt
        Nat.one_pos)
    simp only [eq_iff_iff] at this
    have h2 : v' ∈ PrimeSpectrum.basicOpen (Away.isLocalizationElem (quadricChart_mem k 1 1) hmemt)
        ↔ Away.isLocalizationElem (quadricChart_mem k 1 1) hmemt ∉ v'.asIdeal := Iff.rfl
    exact (not_iff_not.mp (this.trans h2)).symm
  have hnot11 : ∀ v' : Spec (CommRingCat.of (Away 𝒬 (quadricChart k 1 1))),
      single (quadricChartExp 1 1) (1 : k) ∉ (φ.base v').asHomogeneousIdeal.toIdeal := by
    intro v'
    have : φ.base v' ∈ Proj.basicOpen 𝒬 (quadricChart k 1 1) := by
      rw [← Proj.opensRange_awayι 𝒬 _ (quadricChart_mem k 1 1) Nat.one_pos]
      exact ⟨v', rfl⟩
    exact (Proj.mem_basicOpen _ _ _).mp this
  have hmin : v.asIdeal ∈ (Ideal.span
      {Away.isLocalizationElem (quadricChart_mem k 1 1) hmemt}).minimalPrimes := by
    refine ⟨⟨v.isPrime, ?_⟩, ?_⟩
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact (hpre v).mpr (by rw [hv]; exact single_mem_quadricLineIdeal k ℓ htℓ 1)
    · rintro q ⟨hq, hτq⟩ hqv
      let v' : Spec (CommRingCat.of (Away 𝒬 (quadricChart k 1 1))) := ⟨q, hq⟩
      have hτ' := (hpre v').mp (hτq (Ideal.mem_span_singleton_self _))
      have hsp : v' ⤳ v := (PrimeSpectrum.le_iff_specializes v' v).mp hqv
      have hsp' : φ.base v' ⤳ η := hv ▸ hsp.map φ.base.hom.continuous
      rw [quadricSurface_specializes_iff] at hsp'
      have hle : quadricLineIdeal k ℓ ≤ (φ.base v').asHomogeneousIdeal.toIdeal :=
        quadricLineIdeal_le_of_shift k (hnot11 v') hτ' hshift
      have heq : φ.base v' = η := quadricSurface_ext k (le_antisymm hsp' hle)
      have : v' = v := φ.isOpenEmbedding.injective (heq.trans hv.symm)
      rw [← this]
  apply le_antisymm
  · rw [← hv, coheight_eq_of_isOpenImmersion, ← idealHeight_eq_coheight]
    have : (Ideal.span {Away.isLocalizationElem (quadricChart_mem k 1 1) hmemt}).IsPrincipal :=
      ⟨⟨_, rfl⟩⟩
    have : IsNoetherianRing (Away 𝒬 (quadricChart k 1 1)) :=
      isNoetherianRing_of_ringEquiv (MvPolynomial (Fin 2) k) (quadricChartAwayEquiv k 1 1).symm
    exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmin
  · have hgen : genericPoint (quadricSurface k) = quadricSurfaceGenericPoint k :=
      (genericPoint_spec _).eq (isGenericPoint_quadricSurfaceGenericPoint k)
    have hlt : η < ⊤ := by
      refine lt_of_le_not_ge le_top fun h => ?_
      have h' : η.asHomogeneousIdeal.toIdeal ≤
          (quadricSurfaceGenericPoint k).asHomogeneousIdeal.toIdeal := by
        rw [← hgen, ← quadricSurface_specializes_iff]
        exact Scheme.le_iff_specializes.mp h
      have hmem := h' (single_mem_quadricLineIdeal k ℓ htℓ (1 : k))
      exact single_ne_zero.mpr one_ne_zero ((Submodule.mem_bot _).mp hmem)
    exact Order.one_le_iff_ne_zero.mpr (coheight_pos_of_lt_top hlt).ne'

end Lines

section TwoLines

/-- The exponent of `s₀` in a monomial. -/
def quadricExpS : quadricExponents →+ ℕ where
  toFun p := p.1.1 0
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The exponent of `u₀` in a monomial. -/
def quadricExpU : quadricExponents →+ ℕ where
  toFun p := p.1.2 0
  map_zero' := rfl
  map_add' _ _ := rfl

theorem quadricExpS_apply (p : quadricExponents) : quadricExpS p = p.1.1 0 := rfl

theorem quadricExpU_apply (p : quadricExponents) : quadricExpU p = p.1.2 0 := rfl

theorem quadricExpS_chartExp_one_one : quadricExpS (quadricChartExp 1 1) = 0 := rfl

theorem quadricExpU_chartExp_one_one : quadricExpU (quadricChartExp 1 1) = 0 := rfl

/-- A monomial with `eᵢ ≠ 0` and `gⱼ ≠ 0` is divisible by `sᵢuⱼ`. -/
theorem exists_eq_quadricChartExp_add (p : quadricExponents) (i j : Fin 2) (hi : p.1.1 i ≠ 0)
    (hj : p.1.2 j ≠ 0) : ∃ p', p = quadricChartExp i j + p' := by
  have h := (mem_quadricExponents _).mp p.2
  refine ⟨⟨(p.1.1 - Pi.single i 1, p.1.2 - Pi.single j 1), ?_⟩, ?_⟩
  · rw [mem_quadricExponents]
    fin_cases i <;> fin_cases j <;> simp at hi hj ⊢ <;> omega
  · apply Subtype.ext
    apply Prod.ext <;> funext l <;>
      fin_cases i <;> fin_cases j <;> fin_cases l <;> simp [quadricChartExp] at hi hj ⊢ <;> omega

theorem quadricExpS_shift (p : quadricExponents) (hp : quadricExpS p ≠ 0) :
    ∃ p', p + quadricChartExp 1 1 = quadricChartExp 0 1 + p' := by
  have h := (mem_quadricExponents _).mp p.2
  rw [quadricExpS_apply] at hp
  refine ⟨⟨(p.1.1 - Pi.single 0 1 + Pi.single 1 1, p.1.2), ?_⟩, ?_⟩
  · rw [mem_quadricExponents]
    simp
    omega
  · apply Subtype.ext
    apply Prod.ext <;> funext l <;> fin_cases l <;> simp [quadricChartExp] <;> omega

theorem quadricExpU_shift (p : quadricExponents) (hp : quadricExpU p ≠ 0) :
    ∃ p', p + quadricChartExp 1 1 = quadricChartExp 1 0 + p' := by
  have h := (mem_quadricExponents _).mp p.2
  rw [quadricExpU_apply] at hp
  refine ⟨⟨(p.1.1, p.1.2 - Pi.single 0 1 + Pi.single 1 1), ?_⟩, ?_⟩
  · rw [mem_quadricExponents]
    simp
    omega
  · apply Subtype.ext
    apply Prod.ext <;> funext l <;> fin_cases l <;> simp [quadricChartExp] <;> omega

/-- **The line `L₁ = {s₀ = 0}`** of `Q`, a fibre of the first projection `Q ≅ ℙ¹ × ℙ¹ → ℙ¹`. -/
def quadricLineOne : quadricSurface k :=
  quadricLinePoint k quadricExpS_chartExp_one_one

/-- **The line `L₂ = {u₀ = 0}`** of `Q`, a fibre of the second projection `Q ≅ ℙ¹ × ℙ¹ → ℙ¹`. -/
def quadricLineTwo : quadricSurface k :=
  quadricLinePoint k quadricExpU_chartExp_one_one

theorem coheight_quadricLineOne : coheight (quadricLineOne k) = 1 :=
  coheight_quadricLinePoint k quadricExpS quadricExpS_chartExp_one_one
    (quadricDegree_chartExp 0 1) (by simp [quadricExpS_apply, quadricChartExp]) quadricExpS_shift

theorem coheight_quadricLineTwo : coheight (quadricLineTwo k) = 1 :=
  coheight_quadricLinePoint k quadricExpU quadricExpU_chartExp_one_one
    (quadricDegree_chartExp 1 0) (by simp [quadricExpU_apply, quadricChartExp]) quadricExpU_shift

theorem quadricLineOne_ne_quadricLineTwo : quadricLineOne k ≠ quadricLineTwo k := by
  intro h
  have hmem := single_mem_quadricLineIdeal k quadricExpS (p := quadricChartExp 0 1)
    (by simp [quadricExpS_apply, quadricChartExp]) (1 : k)
  rw [← quadricLinePoint_ideal k quadricExpS_chartExp_one_one] at hmem
  change single _ 1 ∈ (quadricLineOne k).asHomogeneousIdeal.toIdeal at hmem
  rw [h] at hmem
  exact (mem_quadricLineIdeal_iff k quadricExpU _).mp hmem (quadricChartExp 0 1)
    (by simp [coeff_single]) (by simp [quadricExpU_apply, quadricChartExp])

/-- `L₁` lies outside the chart `D₊(s₀u₀)`. -/
theorem quadricLineOne_notMem_basicOpen :
    quadricLineOne k ∉ Proj.basicOpen 𝒬 (quadricChart k 0 0) := by
  rw [Proj.mem_basicOpen, not_not]
  exact single_mem_quadricLineIdeal k quadricExpS (by simp [quadricExpS_apply, quadricChartExp]) 1

/-- `L₂` lies outside the chart `D₊(s₀u₀)`. -/
theorem quadricLineTwo_notMem_basicOpen :
    quadricLineTwo k ∉ Proj.basicOpen 𝒬 (quadricChart k 0 0) := by
  rw [Proj.mem_basicOpen, not_not]
  exact single_mem_quadricLineIdeal k quadricExpU (by simp [quadricExpU_apply, quadricChartExp]) 1

/-- The hyperplane section `s₀u₀ = 0` is `L₁ ∪ L₂`: a point outside the chart `D₊(s₀u₀)` is a
specialization of `L₁` or of `L₂`. -/
theorem quadricLine_specializes_of_notMem_basicOpen {x : quadricSurface k}
    (hx : x ∉ Proj.basicOpen 𝒬 (quadricChart k 0 0)) :
    quadricLineOne k ⤳ x ∨ quadricLineTwo k ⤳ x := by
  rw [Proj.mem_basicOpen, not_not] at hx
  have hw : single (quadricChartExp 0 0) (1 : k) ∈ x.asHomogeneousIdeal.toIdeal := hx
  rw [quadricSurface_specializes_iff, quadricSurface_specializes_iff]
  by_cases hz : single (quadricChartExp 0 1) (1 : k) ∈ x.asHomogeneousIdeal.toIdeal
  · left
    refine quadricLineIdeal_le_of_dvd k hw hz fun p hp => ?_
    have h := (mem_quadricExponents _).mp p.2
    rw [quadricExpS_apply] at hp
    by_cases hg : p.1.2 0 = 0
    · obtain ⟨p', hp'⟩ := exists_eq_quadricChartExp_add p 0 1 hp (by omega)
      exact ⟨p', Or.inr hp'⟩
    · obtain ⟨p', hp'⟩ := exists_eq_quadricChartExp_add p 0 0 hp hg
      exact ⟨p', Or.inl hp'⟩
  · right
    have hrel : single (quadricChartExp 0 0) (1 : k) * single (quadricChartExp 1 1) 1 =
        single (quadricChartExp 0 1) 1 * single (quadricChartExp 1 0) 1 := by
      rw [single_mul_single, single_mul_single]
      congr 1
      apply Subtype.ext
      apply Prod.ext <;> funext l <;> fin_cases l <;> simp [quadricChartExp]
    have hw'' : single (quadricChartExp 1 0) (1 : k) ∈ x.asHomogeneousIdeal.toIdeal := by
      have hmem : single (quadricChartExp 0 1) (1 : k) * single (quadricChartExp 1 0) 1 ∈
          x.asHomogeneousIdeal.toIdeal := hrel ▸ Ideal.mul_mem_right _ _ hw
      exact (x.isPrime.mem_or_mem hmem).resolve_left hz
    refine quadricLineIdeal_le_of_dvd k hw hw'' fun p hp => ?_
    have h := (mem_quadricExponents _).mp p.2
    rw [quadricExpU_apply] at hp
    by_cases he : p.1.1 0 = 0
    · obtain ⟨p', hp'⟩ := exists_eq_quadricChartExp_add p 1 0 (by omega) hp
      exact ⟨p', Or.inr hp'⟩
    · obtain ⟨p', hp'⟩ := exists_eq_quadricChartExp_add p 0 0 he hp
      exact ⟨p', Or.inl hp'⟩

/-- The only prime divisors of `Q` outside the chart `D₊(s₀u₀)` are `L₁` and `L₂`. -/
theorem eq_quadricLine_of_notMem_basicOpen {x : quadricSurface k} (hx1 : coheight x = 1)
    (hx : x ∉ Proj.basicOpen 𝒬 (quadricChart k 0 0)) :
    x = quadricLineOne k ∨ x = quadricLineTwo k := by
  rcases quadricLine_specializes_of_notMem_basicOpen k hx with h | h
  · exact Or.inl (eq_of_coheight_eq_one_of_specializes hx1 (coheight_quadricLineOne k) h)
  · exact Or.inr (eq_of_coheight_eq_one_of_specializes hx1 (coheight_quadricLineTwo k) h)

end TwoLines

section Chart

instance quadricChart_isDomain (i j : Fin 2) : IsDomain (Away 𝒬 (quadricChart k i j)) :=
  MulEquiv.isDomain (MvPolynomial (Fin 2) k) (quadricChartAwayEquiv k i j).toMulEquiv

instance quadricChart_isNoetherianRing (i j : Fin 2) :
    IsNoetherianRing (Away 𝒬 (quadricChart k i j)) :=
  isNoetherianRing_of_ringEquiv (MvPolynomial (Fin 2) k) (quadricChartAwayEquiv k i j).symm

instance quadricChart_uniqueFactorizationMonoid (i j : Fin 2) :
    UniqueFactorizationMonoid (Away 𝒬 (quadricChart k i j)) :=
  (quadricChartAwayEquiv k i j).symm.toMulEquiv.uniqueFactorizationMonoid inferInstance

theorem quadricChart_spec_satisfiesConditionStar (i j : Fin 2) :
    (Spec (CommRingCat.of (Away 𝒬 (quadricChart k i j)))).SatisfiesConditionStar := by
  have : IsNormal (Spec (CommRingCat.of (Away 𝒬 (quadricChart k i j)))) :=
    isNormal_spec_of_isIntegrallyClosed _
  exact satisfiesConditionStar_of_isNormal

/-- The units of a chart are the nonzero constants. -/
theorem quadricChart_eq_const_of_isUnit (i j : Fin 2) {a : Away 𝒬 (quadricChart k i j)}
    (ha : IsUnit a) : ∃ c : k, c ≠ 0 ∧ a = quadricChartConst k i j c := by
  obtain ⟨c, hc, hca⟩ :=
    MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp (ha.map (quadricChartAwayEquiv k i j))
  refine ⟨c, hc.ne_zero, (quadricChartAwayEquiv k i j).injective ?_⟩
  rw [hca]
  have hconst : quadricChartConst k i j c = quadricChartOfPoly k i j (MvPolynomial.C c) := by
    simp [quadricChartOfPoly]
  rw [hconst]
  exact (RingHom.congr_fun (quadricChartToPoly_comp_chartOfPoly k i j) (MvPolynomial.C c)).symm

end Chart

section ClassGroup

local notation "hQ" => quadricSurface_satisfiesConditionStar k

/-- The coordinate ring of the chart `D₊(s₀u₀)`. -/
def quadricChartRing : CommRingCat.{u} := CommRingCat.of (Away 𝒬 (quadricChart k 0 0))

instance quadricChartRing_isDomain : IsDomain (quadricChartRing k) := quadricChart_isDomain k 0 0

instance quadricChartRing_isNoetherianRing : IsNoetherianRing (quadricChartRing k) :=
  quadricChart_isNoetherianRing k 0 0

instance quadricChartRing_uniqueFactorizationMonoid :
    UniqueFactorizationMonoid (quadricChartRing k) :=
  quadricChart_uniqueFactorizationMonoid k 0 0

theorem quadricChartRing_spec_satisfiesConditionStar :
    (Spec (quadricChartRing k)).SatisfiesConditionStar :=
  quadricChart_spec_satisfiesConditionStar k 0 0

local notation "hA" => quadricChartRing_spec_satisfiesConditionStar k

/-- The chart `D₊(s₀u₀) ≅ 𝔸²` of `Q`, as an open immersion. -/
abbrev quadricChartι : Spec (quadricChartRing k) ⟶ quadricSurface k :=
  Proj.awayι 𝒬 (quadricChart k 0 0) (quadricChart_mem k 0 0) Nat.one_pos

instance quadricChartι_isOpenImmersion : IsOpenImmersion (quadricChartι k) :=
  inferInstanceAs
    (IsOpenImmersion (Proj.awayι 𝒬 (quadricChart k 0 0) (quadricChart_mem k 0 0) Nat.one_pos))

theorem quadricChartι_genericPoint :
    (quadricChartι k).base (genericPoint _) = genericPoint (quadricSurface k) :=
  genericPoint_eq_of_isOpenImmersion _

theorem mem_range_quadricChartι {x : quadricSurface k} :
    x ∈ Set.range (quadricChartι k).base ↔ x ∈ Proj.basicOpen 𝒬 (quadricChart k 0 0) := by
  have h := Proj.opensRange_awayι 𝒬 (quadricChart k 0 0) (quadricChart_mem k 0 0) Nat.one_pos
  rw [← Scheme.Hom.coe_opensRange]
  change x ∈ (Proj.awayι 𝒬 (quadricChart k 0 0) (quadricChart_mem k 0 0) Nat.one_pos).opensRange
    ↔ _
  rw [h]

/-- Pullback of rational functions from `Q` to the chart `D₊(s₀u₀)`. -/
abbrev quadricChartPull :
    (quadricSurface k).functionField ⟶ (Spec (quadricChartRing k)).functionField :=
  (quadricChartι k).genericFunctionFieldMap (quadricChartι_genericPoint k)

theorem ord_quadricChartPull {v : Spec (quadricChartRing k)} (hv : coheight v = 1)
    (F : (quadricSurface k).functionField) :
    (Spec (quadricChartRing k)).ord (quadricChartPull k F) v =
      (quadricSurface k).ord F ((quadricChartι k).base v) :=
  Scheme.ord_genericFunctionFieldMap hA hQ _ _ hv
    (by rw [coheight_eq_of_isOpenImmersion]; exact hv)
    (Scheme.Hom.map_maximalIdeal_stalkMap_of_isOpenImmersion _ v) F

/-- The prime divisor `L₁ = {s₀ = 0}`. -/
def quadricLineOneDivisor : (quadricSurface k).PrimeDivisor :=
  ⟨quadricLineOne k, coheight_quadricLineOne k⟩

/-- The prime divisor `L₂ = {u₀ = 0}`. -/
def quadricLineTwoDivisor : (quadricSurface k).PrimeDivisor :=
  ⟨quadricLineTwo k, coheight_quadricLineTwo k⟩

/-- The homomorphism `ℤ × ℤ → Cl Q`, `(a, b) ↦ a [L₁] + b [L₂]`. -/
def quadricClassGroupHom : ℤ × ℤ →+ (quadricSurface k).WeilClassGroup hQ :=
  AddMonoidHom.coprod
    (zmultiplesHom _ ((quadricSurface k).weilDivisorClassHom hQ
      (quadricLineOneDivisor k).toWeilDivisor))
    (zmultiplesHom _ ((quadricSurface k).weilDivisorClassHom hQ
      (quadricLineTwoDivisor k).toWeilDivisor))

theorem quadricClassGroupHom_apply (a b : ℤ) :
    quadricClassGroupHom k (a, b) = (quadricSurface k).weilDivisorClassHom hQ
      (a • (quadricLineOneDivisor k).toWeilDivisor +
        b • (quadricLineTwoDivisor k).toWeilDivisor) := by
  simp [quadricClassGroupHom, map_add, map_zsmul]

theorem quadricLineOne_ne_of_mem {x : quadricSurface k}
    (hx : x ∈ Proj.basicOpen 𝒬 (quadricChart k 0 0)) : x ≠ (quadricLineOneDivisor k).1 :=
  fun h => quadricLineOne_notMem_basicOpen k (by rw [h] at hx; exact hx)

theorem quadricLineTwo_ne_of_mem {x : quadricSurface k}
    (hx : x ∈ Proj.basicOpen 𝒬 (quadricChart k 0 0)) : x ≠ (quadricLineTwoDivisor k).1 :=
  fun h => quadricLineTwo_notMem_basicOpen k (by rw [h] at hx; exact hx)

/-- **Surjectivity, one prime divisor.** The class of a prime divisor of `Q` is an integral
combination of `[L₁]` and `[L₂]`. -/
theorem quadric_primeDivisor_mem_range (P : (quadricSurface k).PrimeDivisor) :
    (quadricSurface k).weilDivisorClassHom hQ P.toWeilDivisor ∈
      (quadricClassGroupHom k).range := by
  by_cases hxU : P.1 ∈ Proj.basicOpen 𝒬 (quadricChart k 0 0)
  swap
  · rcases eq_quadricLine_of_notMem_basicOpen k P.2 hxU with h | h
    · refine ⟨(1, 0), ?_⟩
      rw [quadricClassGroupHom_apply]
      have : P = quadricLineOneDivisor k := Subtype.ext h
      simp [this]
    · refine ⟨(0, 1), ?_⟩
      rw [quadricClassGroupHom_apply]
      have : P = quadricLineTwoDivisor k := Subtype.ext h
      simp [this]
  obtain ⟨v, hv⟩ := (mem_range_quadricChartι k).mpr hxU
  have hv1 : coheight v = 1 := by rw [← coheight_eq_of_isOpenImmersion (quadricChartι k), hv]; exact P.2
  have hheight : v.asIdeal.height = 1 := by rw [idealHeight_eq_coheight]; exact hv1
  have := v.isPrime
  obtain ⟨π, hπ⟩ := (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hheight).principal
  have hπ0 : π ≠ 0 := by
    rintro rfl
    have : v.asIdeal = ⊥ := by rw [hπ]; simp
    rw [this, Ideal.height_bot] at hheight
    exact zero_ne_one hheight
  have hπK : algebraMap (quadricChartRing k) (Spec (quadricChartRing k)).functionField π ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hπ0)
  obtain ⟨F, hF⟩ := Scheme.Hom.genericFunctionFieldMap_surjective_of_isOpenImmersion
    (quadricChartι k) (quadricChartι_genericPoint k)
    (algebraMap (quadricChartRing k) (Spec (quadricChartRing k)).functionField π)
  have hF0 : F ≠ 0 := by
    rintro rfl
    rw [map_zero] at hF
    exact hπK hF.symm
  set a := (quadricSurface k).ord F (quadricLineOne k) with ha
  set b := (quadricSurface k).ord F (quadricLineTwo k) with hb
  refine ⟨(-a, -b), ?_⟩
  rw [quadricClassGroupHom_apply]
  refine (((quadricSurface k).weilDivisorClass_eq_iff hQ _ _).mpr ⟨Units.mk0 F hF0, ?_⟩).symm
  apply Scheme.WeilDivisor.ext_apply
  intro x
  rw [Scheme.principalDivisor_apply hQ, Units.val_mk0]
  simp only [neg_smul, AddSubgroup.coe_sub, AddSubgroup.coe_add, AddSubgroup.coe_neg,
    AddSubgroupClass.coe_zsmul, Function.locallyFinsuppWithin.coe_sub,
    Function.locallyFinsuppWithin.coe_add, Function.locallyFinsuppWithin.coe_neg,
    Function.locallyFinsuppWithin.coe_zsmul, Pi.sub_apply, Pi.add_apply, Pi.neg_apply,
    Pi.smul_apply, smul_eq_mul]
  by_cases hx1 : coheight x = 1
  swap
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one hx1, P.toWeilDivisor.2 x hx1,
      (quadricLineOneDivisor k).toWeilDivisor.2 x hx1,
      (quadricLineTwoDivisor k).toWeilDivisor.2 x hx1]
    ring
  by_cases hxU' : x ∈ Proj.basicOpen 𝒬 (quadricChart k 0 0)
  · obtain ⟨v', rfl⟩ := (mem_range_quadricChartι k).mpr hxU'
    have hv1' : coheight v' = 1 := by rwa [coheight_eq_of_isOpenImmersion] at hx1
    rw [Scheme.PrimeDivisor.toWeilDivisor_apply_of_ne _ (quadricLineOne_ne_of_mem k hxU'),
      Scheme.PrimeDivisor.toWeilDivisor_apply_of_ne _ (quadricLineTwo_ne_of_mem k hxU'),
      ← ord_quadricChartPull k hv1', hF]
    by_cases hvv : v' = v
    · subst hvv
      rw [hv, Scheme.PrimeDivisor.toWeilDivisor_apply_self,
        spec_ord_algebraMap_eq_one_of_span_eq hA hv1 hπ.symm]
      ring
    · have hne : (quadricChartι k).base v' ≠ P.1 := by
        rw [← hv]
        exact fun h => hvv ((quadricChartι k).isOpenEmbedding.injective h)
      rw [Scheme.PrimeDivisor.toWeilDivisor_apply_of_ne _ hne]
      have hπv' : π ∉ v'.asIdeal := by
        intro hmem
        have hle : v.asIdeal ≤ v'.asIdeal := by
          rw [hπ, Submodule.span_le, Set.singleton_subset_iff]
          exact hmem
        exact hvv (eq_of_coheight_eq_one_of_specializes hv1' hv1
          ((PrimeSpectrum.le_iff_specializes v v').mp hle))
      rw [(spec_ord_algebraMap_eq_zero_iff hA hv1' hπ0).mpr hπv']
      ring
  · rcases eq_quadricLine_of_notMem_basicOpen k hx1 hxU' with rfl | rfl
    · rw [Scheme.PrimeDivisor.toWeilDivisor_apply_of_ne _
          (fun h => quadricLineOne_notMem_basicOpen k (by rw [h]; exact hxU)),
        show quadricLineOne k = (quadricLineOneDivisor k).1 from rfl,
        Scheme.PrimeDivisor.toWeilDivisor_apply_self,
        Scheme.PrimeDivisor.toWeilDivisor_apply_of_ne _ (quadricLineOne_ne_quadricLineTwo k)]
      change _ = (quadricSurface k).ord F (quadricLineOne k)
      ring
    · rw [Scheme.PrimeDivisor.toWeilDivisor_apply_of_ne _
          (fun h => quadricLineTwo_notMem_basicOpen k (by rw [h]; exact hxU)),
        show quadricLineTwo k = (quadricLineTwoDivisor k).1 from rfl,
        Scheme.PrimeDivisor.toWeilDivisor_apply_self,
        Scheme.PrimeDivisor.toWeilDivisor_apply_of_ne _
          (quadricLineOne_ne_quadricLineTwo k).symm]
      change _ = (quadricSurface k).ord F (quadricLineTwo k)
      ring

/-- **Surjectivity.** Every divisor class of `Q` is an integral combination of `[L₁]` and
`[L₂]`. -/
theorem quadricClassGroupHom_surjective : Function.Surjective (quadricClassGroupHom k) := by
  classical
  intro c
  obtain ⟨D, rfl⟩ := QuotientAddGroup.mk_surjective c
  let e := (quadricSurface k).weilDivisorAddEquivFinsupp
  have key : ∀ f : (quadricSurface k).PrimeDivisor →₀ ℤ,
      (quadricSurface k).weilDivisorClassHom hQ (e.symm f) ∈ (quadricClassGroupHom k).range := by
    intro f
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg =>
      rw [map_add, map_add]
      exact add_mem hf hg
    | single P n =>
      have hsingle : e.symm (Finsupp.single P n) = n • P.toWeilDivisor := by
        apply Scheme.WeilDivisor.ext_apply
        intro x
        simp only [AddSubgroupClass.coe_zsmul, Function.locallyFinsuppWithin.coe_zsmul,
          Pi.smul_apply, smul_eq_mul]
        by_cases hx : coheight x = 1
        · have := Scheme.weilDivisorAddEquivFinsupp_symm_apply_coeff (Finsupp.single P n)
            ⟨x, hx⟩
          simp only at this
          rw [this, Finsupp.single_apply]
          by_cases hPx : P = ⟨x, hx⟩
          · subst hPx
            rw [if_pos rfl, Scheme.PrimeDivisor.toWeilDivisor_apply_self, mul_one]
          · rw [if_neg hPx, Scheme.PrimeDivisor.toWeilDivisor_apply_of_ne _
              (fun h => hPx (Subtype.ext h.symm)), mul_zero]
        · rw [(e.symm (Finsupp.single P n)).2 x hx, P.toWeilDivisor.2 x hx, mul_zero]
      rw [hsingle, map_zsmul]
      exact zsmul_mem (quadric_primeDivisor_mem_range k P) n
  have := key (e D)
  rw [AddEquiv.symm_apply_apply] at this
  exact this

/-- The constant function `c` on `Q`: the pullback of `c ∈ k ⊆ 𝒬₀` along `Q → Spec 𝒬₀`. -/
def quadricConstSection (c : k) : Γ(quadricSurface k, ⊤) :=
  (Proj.toSpecZero 𝒬).appTop
    ((Scheme.ΓSpecIso (CommRingCat.of ↥(𝒬 0))).inv (algebraMap k ↥(𝒬 0) c))

instance quadricSurface_nonempty_top : Nonempty (⊤ : (quadricSurface k).Opens) :=
  ⟨⟨quadricSurfaceGenericPoint k, trivial⟩⟩

theorem isUnit_quadricConstSection {c : k} (hc : c ≠ 0) : IsUnit (quadricConstSection k c) :=
  ((hc.isUnit.map (algebraMap k ↥(𝒬 0))).map
    (Scheme.ΓSpecIso (CommRingCat.of ↥(𝒬 0))).inv.hom).map
    (Proj.toSpecZero 𝒬).appTop.hom

/-- Nonzero constants have trivial divisor on `Q`. -/
theorem ord_quadricConst {c : k} (hc : c ≠ 0) (x : quadricSurface k) :
    (quadricSurface k).ord
      ((quadricSurface k).germToFunctionField ⊤ (quadricConstSection k c)) x = 0 :=
  Scheme.ord_of_isUnit (isUnit_quadricConstSection k hc) trivial

/-- The constant `c` on `Q` restricts to the constant `c` of the chart `D₊(s₀u₀)`. -/
theorem quadricChartPull_const (c : k) :
    quadricChartPull k ((quadricSurface k).germToFunctionField ⊤ (quadricConstSection k c)) =
      algebraMap (quadricChartRing k) (Spec (quadricChartRing k)).functionField
        (quadricChartConst k 0 0 c) := by
  have h1 := Scheme.Hom.genericFunctionFieldMap_algebraMap (quadricChartι k)
    (quadricChartι_genericPoint k) (genericPoint (Spec (quadricChartRing k)))
    ((quadricSurface k).presheaf.germ ⊤ _ trivial (quadricConstSection k c))
  have e1 := Scheme.algebraMap_germ_eq_germToFunctionField (X := quadricSurface k) (U := ⊤)
    (x := (quadricChartι k).base (genericPoint _)) trivial (quadricConstSection k c)
  rw [← e1, h1]
  have e2 := Scheme.Hom.germ_stalkMap_apply (quadricChartι k) ⊤
    (genericPoint (Spec (quadricChartRing k))) trivial (quadricConstSection k c)
  erw [e2]
  have h2 : (quadricChartι k).appTop (quadricConstSection k c) =
      (Scheme.ΓSpecIso (quadricChartRing k)).inv (quadricChartConst k 0 0 c) := by
    have h3 : quadricChartι k ≫ Proj.toSpecZero 𝒬 =
        Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒬 (Submonoid.powers (quadricChart k 0 0)))) :=
      Proj.awayι_toSpecZero _ _ _ _
    have h4 := Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (fromZeroRingHom 𝒬 (Submonoid.powers (quadricChart k 0 0))))
    rw [quadricConstSection, ← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, h3,
      ← ConcreteCategory.comp_apply]
    erw [← h4]
    rfl
  erw [h2, Scheme.ΓSpecIso_inv, StructureSheaf.algebraMap_germ_apply]
  exact spec_algebraMap_stalk_toStalk _ _

theorem quadricChart_exists_algebraMap_eq {g : (Spec (quadricChartRing k)).functionField}
    (hg : g ≠ 0) (h : ∀ v : Spec (quadricChartRing k), coheight v = 1 →
      0 ≤ (Spec (quadricChartRing k)).ord g v) :
    ∃ α : quadricChartRing k, algebraMap _ (Spec (quadricChartRing k)).functionField α = g := by
  apply exists_algebraMap_eq_of_forall_height_one (Spec (quadricChartRing k)).functionField g
  intro q hq hqh
  let y : Spec (quadricChartRing k) := ⟨q, hq⟩
  have hy : coheight y = 1 := by
    rw [← idealHeight_eq_coheight]
    exact hqh
  exact spec_mem_ofField_of_ord_nonneg hA hy hg (h y hy)

/-- **Injectivity.** If `a L₁ + b L₂` is principal then `a = b = 0`: its rational function has
no zeros or poles on the chart `D₊(s₀u₀)`, hence is a nonzero constant. -/
theorem quadricClassGroupHom_injective : Function.Injective (quadricClassGroupHom k) := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨a, b⟩ hab
  rw [quadricClassGroupHom_apply] at hab
  obtain ⟨F, hF⟩ :=
    ((quadricSurface k).weilDivisorClass_eq_iff hQ _ 0).mp (hab.trans (map_zero _).symm)
  rw [sub_zero] at hF
  have hordF : ∀ x, (quadricSurface k).ord (F : (quadricSurface k).functionField) x =
      (a • (quadricLineOneDivisor k).toWeilDivisor +
        b • (quadricLineTwoDivisor k).toWeilDivisor).1 x := by
    intro x
    rw [hF, Scheme.principalDivisor_apply hQ]
  have hinj : Function.Injective (quadricChartPull k) := (quadricChartPull k).hom.injective
  have hG0 : quadricChartPull k (F : (quadricSurface k).functionField) ≠ 0 := by
    rw [Ne, ← map_zero (quadricChartPull k).hom]
    exact fun h => F.ne_zero (hinj h)
  have hzero : ∀ v : Spec (quadricChartRing k), coheight v = 1 →
      (Spec (quadricChartRing k)).ord (quadricChartPull k F) v = 0 := by
    intro v hv
    rw [ord_quadricChartPull k hv, hordF]
    have hU := (mem_range_quadricChartι k).mp ⟨v, rfl⟩
    simp [Scheme.PrimeDivisor.toWeilDivisor_apply_of_ne _ (quadricLineOne_ne_of_mem k hU),
      Scheme.PrimeDivisor.toWeilDivisor_apply_of_ne _ (quadricLineTwo_ne_of_mem k hU)]
  have hinv : ∀ v : Spec (quadricChartRing k), coheight v = 1 →
      (Spec (quadricChartRing k)).ord (quadricChartPull k F)⁻¹ v = 0 := by
    intro v hv
    have h := Scheme.ord_mul (x := v) hG0 (inv_ne_zero hG0)
    have h1 := Scheme.ord_mul (x := v) (one_ne_zero (α := (Spec (quadricChartRing k)).functionField))
      one_ne_zero
    rw [mul_one] at h1
    rw [mul_inv_cancel₀ hG0, hzero v hv] at h
    omega
  obtain ⟨α, hα⟩ := quadricChart_exists_algebraMap_eq k hG0 fun v hv => (hzero v hv).symm.le
  obtain ⟨β, hβ⟩ := quadricChart_exists_algebraMap_eq k (inv_ne_zero hG0)
    fun v hv => (hinv v hv).symm.le
  have hαβ : α * β = 1 := by
    apply IsFractionRing.injective (quadricChartRing k) (Spec (quadricChartRing k)).functionField
    rw [map_mul, hα, hβ, mul_inv_cancel₀ hG0, map_one]
  obtain ⟨c, hc0, hαc⟩ := quadricChart_eq_const_of_isUnit k 0 0 (IsUnit.of_mul_eq_one β hαβ)
  have hFc : (F : (quadricSurface k).functionField) =
      (quadricSurface k).germToFunctionField ⊤ (quadricConstSection k c) := by
    apply hinj
    rw [quadricChartPull_const, ← hα]
    exact congrArg _ hαc
  have h1 := hordF (quadricLineOneDivisor k).1
  have h2 := hordF (quadricLineTwoDivisor k).1
  rw [hFc, ord_quadricConst k hc0] at h1 h2
  simp only [AddSubgroup.coe_add, AddSubgroupClass.coe_zsmul,
    Function.locallyFinsuppWithin.coe_add, Function.locallyFinsuppWithin.coe_zsmul, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, Scheme.PrimeDivisor.toWeilDivisor_apply_self] at h1 h2
  rw [Scheme.PrimeDivisor.toWeilDivisor_apply_of_ne _ (quadricLineOne_ne_quadricLineTwo k)] at h1
  rw [Scheme.PrimeDivisor.toWeilDivisor_apply_of_ne _
    (quadricLineOne_ne_quadricLineTwo k).symm] at h2
  simp only [mul_one, mul_zero, add_zero, zero_add] at h1 h2
  simp [← h1, ← h2]

/-- **Hartshorne II, Example 6.6.1.** The class group of the split quadric surface is `ℤ × ℤ`:
the class of the line `L₁ = {s₀ = 0}` (a fibre of the first projection) is `(1, 0)` and the class
of the line `L₂ = {u₀ = 0}` (a fibre of the second projection) is `(0, 1)`. -/
def quadricSurfaceClassGroupEquiv : (quadricSurface k).WeilClassGroup hQ ≃+ ℤ × ℤ :=
  (AddEquiv.ofBijective (quadricClassGroupHom k)
    ⟨quadricClassGroupHom_injective k, quadricClassGroupHom_surjective k⟩).symm

theorem quadricSurfaceClassGroupEquiv_symm_apply (a b : ℤ) :
    (quadricSurfaceClassGroupEquiv k).symm (a, b) = (quadricSurface k).weilDivisorClassHom hQ
      (a • (quadricLineOneDivisor k).toWeilDivisor +
        b • (quadricLineTwoDivisor k).toWeilDivisor) := by
  rw [quadricSurfaceClassGroupEquiv, AddEquiv.symm_symm]
  exact quadricClassGroupHom_apply k a b

theorem quadricSurfaceClassGroupEquiv_lineOne :
    quadricSurfaceClassGroupEquiv k
      ((quadricSurface k).weilDivisorClassHom hQ (quadricLineOneDivisor k).toWeilDivisor) =
      (1, 0) := by
  apply (AddEquiv.eq_symm_apply _).mp
  rw [quadricSurfaceClassGroupEquiv_symm_apply]
  simp

theorem quadricSurfaceClassGroupEquiv_lineTwo :
    quadricSurfaceClassGroupEquiv k
      ((quadricSurface k).weilDivisorClassHom hQ (quadricLineTwoDivisor k).toWeilDivisor) =
      (0, 1) := by
  apply (AddEquiv.eq_symm_apply _).mp
  rw [quadricSurfaceClassGroupEquiv_symm_apply]
  simp

/-- The hyperplane section `s₀u₀ = 0` of `Q` is `L₁ + L₂`, of class `(1, 1)`. -/
theorem quadricSurfaceClassGroupEquiv_lineOne_add_lineTwo :
    quadricSurfaceClassGroupEquiv k ((quadricSurface k).weilDivisorClassHom hQ
      ((quadricLineOneDivisor k).toWeilDivisor + (quadricLineTwoDivisor k).toWeilDivisor)) =
      (1, 1) := by
  rw [map_add, map_add, quadricSurfaceClassGroupEquiv_lineOne,
    quadricSurfaceClassGroupEquiv_lineTwo]
  rfl

end ClassGroup

end Hartshorne

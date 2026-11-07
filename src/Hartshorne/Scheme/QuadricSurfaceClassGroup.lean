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

end Hartshorne

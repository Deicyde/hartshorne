/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ProjectiveSpaceRegular
import Hartshorne.Scheme.RegularInCodimensionOne
import Mathlib.Algebra.MonoidAlgebra.Grading
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# The split nonsingular quadric surface

Hartshorne, *Algebraic Geometry*, II.6, Example 6.6.1 (p. 135), and I, Exercise 2.15.

The quadric surface `Q = {xy = zw} ⊆ ℙ³_k` is the image of the Segre embedding
`ℙ¹ × ℙ¹ → ℙ³`, `([s₀ : s₁], [u₀ : u₁]) ↦ [s₀u₀ : s₁u₁ : s₀u₁ : s₁u₀]`. Its homogeneous coordinate
ring is the Segre ring: the span in `k[s₀, s₁, u₀, u₁]` of the monomials
`s₀^{e₀} s₁^{e₁} u₀^{g₀} u₁^{g₁}` of bidegree `(d, d)` (that is, `e₀ + e₁ = g₀ + g₁ = d`), graded by
`d`. We realise it as the monoid algebra of the monoid of such exponent pairs, graded by `d`,
and set `Q = Proj` of it. The coordinates `x, y, z, w` of `ℙ³` are the four monomials
`s_i u_j` of degree one.

## Main results

* `Hartshorne.quadricChartAwayEquiv`: the chart `D₊(sᵢuⱼ)` of `Q` is the affine plane: the
  degree-zero localization at `sᵢuⱼ` is the polynomial ring in the two ratios
  `s_{i'}/sᵢ` and `u_{j'}/uⱼ` (where `i' ≠ i`, `j' ≠ j`).
* `Hartshorne.quadricSurface_iSup_basicOpen`: the four charts cover `Q`.
* `Hartshorne.quadricSurface_isRegular`: `Q` is a regular scheme.
* `Hartshorne.quadricSurface_satisfiesConditionStar`: `Q` satisfies condition `(*)`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory AddMonoidAlgebra HomogeneousLocalization

namespace Hartshorne

universe u

/-- The exponent pairs `(e, g)` of the monomials `s₀^{e₀} s₁^{e₁} u₀^{g₀} u₁^{g₁}` of bidegree
`(d, d)` for some `d`, i.e. with `e₀ + e₁ = g₀ + g₁`. -/
def quadricExponents : AddSubmonoid ((Fin 2 → ℕ) × (Fin 2 → ℕ)) where
  carrier := {p | p.1 0 + p.1 1 = p.2 0 + p.2 1}
  zero_mem' := rfl
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Pi.add_apply] at ha hb ⊢
    omega

theorem mem_quadricExponents (p : (Fin 2 → ℕ) × (Fin 2 → ℕ)) :
    p ∈ quadricExponents ↔ p.1 0 + p.1 1 = p.2 0 + p.2 1 :=
  Iff.rfl

/-- The degree `d` of a monomial of bidegree `(d, d)`. -/
def quadricDegree : quadricExponents →+ ℕ where
  toFun p := p.1.1 0 + p.1.1 1
  map_zero' := rfl
  map_add' a b := by
    change (a.1 + b.1).1 0 + (a.1 + b.1).1 1 = _
    simp only [Prod.fst_add, Pi.add_apply]
    ring

theorem quadricDegree_apply (p : quadricExponents) : quadricDegree p = p.1.1 0 + p.1.1 1 :=
  rfl

theorem quadricDegree_eq_snd (p : quadricExponents) : quadricDegree p = p.1.2 0 + p.1.2 1 :=
  p.2

instance : UniqueSums quadricExponents :=
  UniqueSums.of_injective_addHom (quadricExponents.subtype : _ →+ _).toAddHom
    Subtype.val_injective inferInstance

variable (k : Type u) [Field k]

/-- The Segre ring of `ℙ¹ × ℙ¹`, the homogeneous coordinate ring of the quadric surface
`xy = zw`: the monoid algebra of the exponent pairs of bidegree `(d, d)`. -/
abbrev QuadricRing := AddMonoidAlgebra k quadricExponents

/-- The grading of the Segre ring by `d` (a monomial of bidegree `(d, d)` has degree `d`). -/
abbrev quadricGrading : ℕ → Submodule k (QuadricRing k) :=
  gradeBy k quadricDegree

/-- **The split nonsingular quadric surface** `Q = {xy = zw} ⊆ ℙ³_k`, as `Proj` of its
homogeneous coordinate ring, the Segre ring of `ℙ¹ × ℙ¹`. -/
abbrev quadricSurface : Scheme.{u} :=
  Proj (quadricGrading k)

local notation "𝒬" => quadricGrading k

section Charts

theorem pi_single_add_pi_single (i : Fin 2) :
    (Pi.single i 1 : Fin 2 → ℕ) 0 + (Pi.single i 1 : Fin 2 → ℕ) 1 = 1 := by
  fin_cases i <;> rfl

theorem pi_single_rev (i : Fin 2) : (Pi.single i 1 : Fin 2 → ℕ) i.rev = 0 := by
  fin_cases i <;> rfl

/-- The exponent pair of the degree-one monomial `sᵢuⱼ`. -/
def quadricChartExp (i j : Fin 2) : quadricExponents :=
  ⟨(Pi.single i 1, Pi.single j 1), by
    rw [mem_quadricExponents, pi_single_add_pi_single, pi_single_add_pi_single]⟩

theorem quadricDegree_chartExp (i j : Fin 2) : quadricDegree (quadricChartExp i j) = 1 :=
  pi_single_add_pi_single i

/-- The coordinate `sᵢuⱼ` of `ℙ³` restricted to `Q`. With `x = s₀u₀`, `y = s₁u₁`, `z = s₀u₁`
and `w = s₁u₀` these satisfy `xy = zw`. -/
def quadricChart (i j : Fin 2) : QuadricRing k :=
  single (quadricChartExp i j) 1

theorem single_mem_quadricGrading (p : quadricExponents) (c : k) :
    single p c ∈ 𝒬 (quadricDegree p) :=
  single_mem_gradeBy _ _ _

theorem quadricChart_mem (i j : Fin 2) : quadricChart k i j ∈ 𝒬 1 := by
  have := single_mem_quadricGrading k (quadricChartExp i j) 1
  rwa [quadricDegree_chartExp] at this

theorem quadricChart_ne_zero (i j : Fin 2) : quadricChart k i j ≠ 0 :=
  single_ne_zero.mpr one_ne_zero

theorem mem_quadricGrading_iff (n : ℕ) (a : QuadricRing k) :
    a ∈ 𝒬 n ↔ ∀ p ∈ a.coeff.support, quadricDegree p = n :=
  Iff.rfl

/-- The dehomogenization at `sᵢuⱼ` on monomials: `(e, g) ↦ X₀^{e_{i'}} X₁^{g_{j'}}`, where
`i' ≠ i` and `j' ≠ j`. -/
def quadricDehomMonoidHom (i j : Fin 2) :
    Multiplicative quadricExponents →* MvPolynomial (Fin 2) k where
  toFun p := MvPolynomial.X 0 ^ (p.toAdd.1.1 i.rev) * MvPolynomial.X 1 ^ (p.toAdd.1.2 j.rev)
  map_one' := by simp
  map_mul' p q := by
    simp only [toAdd_mul, AddSubmonoid.coe_add, Prod.fst_add, Prod.snd_add, Pi.add_apply,
      pow_add]
    ring

/-- Dehomogenization at `sᵢuⱼ`: `s_{i'}/sᵢ ↦ X₀`, `u_{j'}/uⱼ ↦ X₁`. -/
def quadricDehom (i j : Fin 2) : QuadricRing k →ₐ[k] MvPolynomial (Fin 2) k :=
  lift k (MvPolynomial (Fin 2) k) quadricExponents (quadricDehomMonoidHom k i j)

theorem quadricDehom_single (i j : Fin 2) (p : quadricExponents) (c : k) :
    quadricDehom k i j (single p c) =
      c • (MvPolynomial.X 0 ^ (p.1.1 i.rev) * MvPolynomial.X 1 ^ (p.1.2 j.rev)) := by
  rw [quadricDehom, lift_single]
  rfl

theorem quadricDehom_chart (i j : Fin 2) : quadricDehom k i j (quadricChart k i j) = 1 := by
  rw [quadricChart, quadricDehom_single]
  simp [quadricChartExp, pi_single_rev]

/-- Dehomogenization inverts `sᵢuⱼ`, so it factors through the localization. -/
def quadricAwayDehom (i j : Fin 2) :
    Localization.Away (quadricChart k i j) →+* MvPolynomial (Fin 2) k :=
  IsLocalization.lift (M := Submonoid.powers (quadricChart k i j))
    (g := (quadricDehom k i j).toRingHom) (by
      rintro ⟨y, n, rfl⟩
      simp [quadricDehom_chart])

theorem quadricAwayDehom_mk (i j : Fin 2) (a : QuadricRing k) (n : ℕ)
    (h : quadricChart k i j ^ n ∈ Submonoid.powers (quadricChart k i j)) :
    quadricAwayDehom k i j (Localization.mk a ⟨_, h⟩) = quadricDehom k i j a := by
  rw [Localization.mk_eq_mk', quadricAwayDehom, IsLocalization.lift_mk'_spec]
  simp [quadricDehom_chart]

/-- The dehomogenization map `(Segre ring)_(sᵢuⱼ) → k[X₀, X₁]`. -/
def quadricChartToPoly (i j : Fin 2) :
    Away 𝒬 (quadricChart k i j) →+* MvPolynomial (Fin 2) k where
  toFun z := quadricAwayDehom k i j z.val
  map_one' := by simp [HomogeneousLocalization.val_one]
  map_mul' a b := by simp [HomogeneousLocalization.val_mul]
  map_zero' := by simp [HomogeneousLocalization.val_zero]
  map_add' a b := by simp [HomogeneousLocalization.val_add]

theorem quadricChartToPoly_mk (i j : Fin 2) (n : ℕ) (a : QuadricRing k) (ha : a ∈ 𝒬 (n • 1)) :
    quadricChartToPoly k i j (Away.mk 𝒬 (quadricChart_mem k i j) n a ha) =
      quadricDehom k i j a := by
  change quadricAwayDehom k i j _ = _
  rw [Away.val_mk, quadricAwayDehom_mk]

/-- The ratio `m / (sᵢuⱼ)` in the chart, for a degree-one monomial `m`. -/
def quadricChartRatio (i j : Fin 2) (p : quadricExponents) (hp : quadricDegree p = 1) :
    Away 𝒬 (quadricChart k i j) :=
  Away.mk 𝒬 (quadricChart_mem k i j) 1 (single p 1) (by
    simpa [hp] using single_mem_quadricGrading k p 1)

/-- The constants `c / 1` in the chart. -/
def quadricChartConst (i j : Fin 2) : k →+* Away 𝒬 (quadricChart k i j) :=
  (HomogeneousLocalization.fromZeroRingHom 𝒬 _).comp (algebraMap k (𝒬 0))

/-- The substitution `X₀ ↦ s_{i'}uⱼ / sᵢuⱼ`, `X₁ ↦ sᵢu_{j'} / sᵢuⱼ`, the inverse of
dehomogenization. -/
def quadricChartOfPoly (i j : Fin 2) :
    MvPolynomial (Fin 2) k →+* Away 𝒬 (quadricChart k i j) :=
  MvPolynomial.eval₂Hom (quadricChartConst k i j)
    ![quadricChartRatio k i j (quadricChartExp i.rev j) (quadricDegree_chartExp _ _),
      quadricChartRatio k i j (quadricChartExp i j.rev) (quadricDegree_chartExp _ _)]

theorem quadricChartConst_val (i j : Fin 2) (c : k) :
    (quadricChartConst k i j c).val =
      algebraMap (QuadricRing k) (Localization.Away (quadricChart k i j))
        (algebraMap k (QuadricRing k) c) := by
  rw [← Localization.mk_one_eq_algebraMap]
  rfl

theorem quadricChartRatio_val (i j : Fin 2) (p : quadricExponents) (hp : quadricDegree p = 1) :
    algebraMap (QuadricRing k) (Localization.Away (quadricChart k i j)) (quadricChart k i j) *
        (quadricChartRatio k i j p hp).val =
      algebraMap (QuadricRing k) (Localization.Away (quadricChart k i j)) (single p 1) := by
  rw [quadricChartRatio, Away.val_mk, Localization.mk_eq_mk']
  have := IsLocalization.mk'_spec' (Localization.Away (quadricChart k i j)) (single p 1)
    (⟨quadricChart k i j ^ 1, ⟨1, rfl⟩⟩ : Submonoid.powers (quadricChart k i j))
  simp only [pow_one] at this ⊢
  exact this

theorem quadricChartToPoly_comp_chartOfPoly (i j : Fin 2) :
    (quadricChartToPoly k i j).comp (quadricChartOfPoly k i j) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro r
    change quadricAwayDehom k i j (quadricChartOfPoly k i j (MvPolynomial.C r)).val =
      MvPolynomial.C r
    rw [quadricChartOfPoly, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C,
      quadricChartConst_val, quadricAwayDehom, IsLocalization.lift_eq]
    change quadricDehom k i j (single 0 r) = _
    rw [quadricDehom_single]
    simp [MvPolynomial.smul_eq_C_mul]
  · intro l
    change quadricChartToPoly k i j (MvPolynomial.eval₂ _ _ (MvPolynomial.X l)) =
      MvPolynomial.X l
    rw [MvPolynomial.eval₂_X]
    fin_cases l
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, quadricChartRatio,
        quadricChartToPoly_mk, quadricDehom_single]
      simp [quadricChartExp, pi_single_rev]
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        quadricChartRatio, quadricChartToPoly_mk, quadricDehom_single]
      simp [quadricChartExp, pi_single_rev]

/-- The exponent identity behind the chart isomorphism: for a monomial `p` of degree `n`, with
`a = e_{i'}` and `b = g_{j'}`, `(sᵢuⱼ)^n (s_{i'}uⱼ)^a (sᵢu_{j'})^b = p · (sᵢuⱼ)^{a+b}`. -/
theorem quadric_exponent_identity (i j : Fin 2) (p : quadricExponents) :
    quadricDegree p • quadricChartExp i j + p.1.1 i.rev • quadricChartExp i.rev j +
        p.1.2 j.rev • quadricChartExp i j.rev =
      p + (p.1.1 i.rev + p.1.2 j.rev) • quadricChartExp i j := by
  have h1 := quadricDegree_apply p
  have h2 := quadricDegree_eq_snd p
  apply Subtype.ext
  apply Prod.ext <;> funext l <;>
    fin_cases i <;> fin_cases j <;> fin_cases l <;>
    simp [quadricChartExp] <;> omega

theorem quadricChartOfPoly_comp_chartToPoly (i j : Fin 2) :
    (quadricChartOfPoly k i j).comp (quadricChartToPoly k i j) = RingHom.id _ := by
  ext z
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒬 (quadricChart_mem k i j) z
  rw [RingHom.comp_apply, quadricChartToPoly_mk, RingHom.id_apply]
  let L := Localization.Away (quadricChart k i j)
  let ι : QuadricRing k →+* L := algebraMap _ _
  let Θ : QuadricRing k →+* L :=
    (algebraMap (Away 𝒬 (quadricChart k i j)) L).comp
      ((quadricChartOfPoly k i j).comp (quadricDehom k i j).toRingHom)
  have hΘ : ∀ x, Θ x = (quadricChartOfPoly k i j (quadricDehom k i j x)).val := fun _ => rfl
  have hunit : IsUnit (ι (quadricChart k i j)) :=
    IsLocalization.map_units L (⟨quadricChart k i j, 1, pow_one _⟩ :
      Submonoid.powers (quadricChart k i j))
  have hconst : ∀ c : k, Θ (algebraMap k _ c) = ι (algebraMap k _ c) := by
    intro c
    rw [hΘ, AlgHom.commutes, MvPolynomial.algebraMap_eq, quadricChartOfPoly,
      MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, quadricChartConst_val]
  have hmono : ∀ p : quadricExponents,
      ι (quadricChart k i j) ^ quadricDegree p * Θ (single p 1) = ι (single p 1) := by
    intro p
    set a := p.1.1 i.rev
    set b := p.1.2 j.rev
    apply (hunit.pow (a + b)).mul_left_cancel
    have hval : Θ (single p 1) =
        (quadricChartRatio k i j (quadricChartExp i.rev j) (quadricDegree_chartExp _ _)).val ^ a *
          (quadricChartRatio k i j (quadricChartExp i j.rev)
            (quadricDegree_chartExp _ _)).val ^ b := by
      rw [hΘ, quadricDehom_single, one_smul, map_mul, map_pow, map_pow, quadricChartOfPoly,
        MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X, MvPolynomial.eval₂_X,
        HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow,
        HomogeneousLocalization.val_pow]
      rfl
    have e1 := quadricChartRatio_val k i j (quadricChartExp i.rev j) (quadricDegree_chartExp _ _)
    have e2 := quadricChartRatio_val k i j (quadricChartExp i j.rev) (quadricDegree_chartExp _ _)
    calc ι (quadricChart k i j) ^ (a + b) *
          (ι (quadricChart k i j) ^ quadricDegree p * Θ (single p 1))
        = ι (quadricChart k i j) ^ quadricDegree p *
            (ι (quadricChart k i j) * (quadricChartRatio k i j (quadricChartExp i.rev j)
              (quadricDegree_chartExp _ _)).val) ^ a *
            (ι (quadricChart k i j) * (quadricChartRatio k i j (quadricChartExp i j.rev)
              (quadricDegree_chartExp _ _)).val) ^ b := by
          rw [hval]; ring
      _ = ι (quadricChart k i j) ^ quadricDegree p * ι (single (quadricChartExp i.rev j) 1) ^ a *
            ι (single (quadricChartExp i j.rev) 1) ^ b := by
          rw [e1, e2]
      _ = ι (single (quadricDegree p • quadricChartExp i j + a • quadricChartExp i.rev j +
            b • quadricChartExp i j.rev) 1) := by
          simp only [quadricChart, ← map_pow, ← map_mul, single_pow, single_mul_single, one_pow,
            mul_one]
      _ = ι (single (p + (a + b) • quadricChartExp i j) 1) := by
          rw [quadric_exponent_identity]
      _ = ι (quadricChart k i j) ^ (a + b) * ι (single p 1) := by
          simp only [quadricChart, ← map_pow, ← map_mul, single_pow, single_mul_single, one_pow,
            mul_one, add_comm p]
  have key : ι (quadricChart k i j ^ n) * Θ a = ι a := by
    conv_rhs => rw [← sum_coeff_single a]
    conv_lhs => rw [← sum_coeff_single a]
    rw [Finsupp.sum, map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hdeg : quadricDegree p = n := by
      simpa using ha p hp
    have hsingle : single p (a.coeff p) = algebraMap k _ (a.coeff p) * single p 1 := by
      rw [coe_algebraMap]
      simp [single_mul_single]
    rw [hsingle, map_mul, map_mul, hconst, map_pow, ← hdeg, mul_left_comm, hmono]
  rw [Away.val_mk, Localization.mk_eq_mk', IsLocalization.eq_mk'_iff_mul_eq, ← hΘ, mul_comm]
  exact key

/-- **The charts of the quadric surface are affine planes.** Dehomogenization is a ring
isomorphism from the degree-zero localization of the Segre ring at `sᵢuⱼ` to `k[X₀, X₁]`, with
`X₀ = s_{i'}/sᵢ` and `X₁ = u_{j'}/uⱼ`. -/
def quadricChartAwayEquiv (i j : Fin 2) :
    Away 𝒬 (quadricChart k i j) ≃+* MvPolynomial (Fin 2) k :=
  RingEquiv.ofRingHom (quadricChartToPoly k i j) (quadricChartOfPoly k i j)
    (quadricChartToPoly_comp_chartOfPoly k i j) (quadricChartOfPoly_comp_chartToPoly k i j)

/-- Every monomial of positive degree is divisible by one of the four coordinates `sᵢuⱼ`. -/
theorem single_mem_span_quadricChart (p : quadricExponents) (hp : 0 < quadricDegree p) (c : k) :
    single p c ∈ Ideal.span (Set.range fun ij : Fin 2 × Fin 2 => quadricChart k ij.1 ij.2) := by
  have h1 := quadricDegree_apply p
  have h2 := quadricDegree_eq_snd p
  obtain ⟨i, hi⟩ : ∃ i : Fin 2, 0 < p.1.1 i := by
    by_contra! h
    have := h 0; have := h 1; omega
  obtain ⟨j, hj⟩ : ∃ j : Fin 2, 0 < p.1.2 j := by
    by_contra! h
    have := h 0; have := h 1; omega
  let q : quadricExponents := ⟨(p.1.1 - Pi.single i 1, p.1.2 - Pi.single j 1), by
    rw [mem_quadricExponents]
    fin_cases i <;> fin_cases j <;> simp at hi hj ⊢ <;> omega⟩
  have hq : q + quadricChartExp i j = p := by
    apply Subtype.ext
    apply Prod.ext <;> funext l <;>
      fin_cases i <;> fin_cases j <;> fin_cases l <;> simp [q, quadricChartExp] at hi hj ⊢ <;>
      omega
  have : single p c = single q c * quadricChart k i j := by
    rw [quadricChart, single_mul_single, hq, mul_one]
  rw [this]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨(i, j), rfl⟩)

theorem quadric_irrelevant_le_span :
    (HomogeneousIdeal.irrelevant 𝒬).toIdeal ≤
      Ideal.span (Set.range fun ij : Fin 2 × Fin 2 => quadricChart k ij.1 ij.2) := by
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro d hd a ha
  change a ∈ Ideal.span _
  rw [← sum_coeff_single a, Finsupp.sum]
  refine Ideal.sum_mem _ fun p hp => ?_
  have : quadricDegree p = d := ha p hp
  exact single_mem_span_quadricChart k p (this ▸ hd) _

/-- The four charts `D₊(sᵢuⱼ)` cover the quadric surface. -/
theorem quadricSurface_iSup_basicOpen :
    ⨆ ij : Fin 2 × Fin 2, Proj.basicOpen 𝒬 (quadricChart k ij.1 ij.2) = ⊤ :=
  Proj.iSup_basicOpen_eq_top _ _ (quadric_irrelevant_le_span k)

theorem quadricSurface_isAffineOpen_basicOpen (i j : Fin 2) :
    IsAffineOpen (Proj.basicOpen 𝒬 (quadricChart k i j)) :=
  Proj.isAffineOpen_basicOpen 𝒬 _ (quadricChart_mem k i j) Nat.one_pos

end Charts

section ConditionStar

instance quadricSurface_isPrime (x : quadricSurface k) :
    x.asHomogeneousIdeal.toIdeal.IsPrime :=
  x.isPrime

theorem quadricChart_mem_irrelevant (i j : Fin 2) :
    quadricChart k i j ∈ HomogeneousIdeal.irrelevant 𝒬 := by
  rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
    DirectSum.decompose_of_mem_ne 𝒬 (quadricChart_mem k i j) one_ne_zero]

/-- The generic point of `Q`: the zero ideal of the Segre ring. -/
def quadricSurfaceGenericPoint : quadricSurface k :=
  ⟨⊥, Ideal.isPrime_bot, fun h ↦
    quadricChart_ne_zero k 0 0 ((Submodule.mem_bot _).mp (h (quadricChart_mem_irrelevant k 0 0)))⟩

theorem quadricSurface_specializes_iff_le (x y : quadricSurface k) :
    x ⤳ y ↔ x.asHomogeneousIdeal ≤ y.asHomogeneousIdeal := by
  rw [specializes_iff_mem_closure]
  exact (ProjectiveSpectrum.le_iff_mem_closure 𝒬 x y).symm

theorem isGenericPoint_quadricSurfaceGenericPoint :
    IsGenericPoint (quadricSurfaceGenericPoint k) Set.univ :=
  isGenericPoint_iff_specializes.mpr fun x ↦
    ⟨fun _ ↦ trivial, fun _ ↦ (quadricSurface_specializes_iff_le k _ x).mpr bot_le⟩

instance quadricSurface_irreducibleSpace : IrreducibleSpace (quadricSurface k) :=
  (irreducibleSpace_def _).mpr (isGenericPoint_quadricSurfaceGenericPoint k).isIrreducible

instance quadricSurface_isDomain_stalk (x : quadricSurface k) :
    IsDomain ((quadricSurface k).presheaf.stalk x) := by
  have : IsDomain (AtPrime 𝒬 x.asHomogeneousIdeal.toIdeal) :=
    Function.Injective.isDomain
      (algebraMap (AtPrime 𝒬 x.asHomogeneousIdeal.toIdeal)
        (Localization x.asHomogeneousIdeal.toIdeal.primeCompl))
      (HomogeneousLocalization.val_injective _)
  have : IsDomain (CommRingCat.of (AtPrime 𝒬 x.asHomogeneousIdeal.toIdeal)) := this
  exact Function.Injective.isDomain (Proj.stalkIso 𝒬 x).hom.hom
    (ConcreteCategory.injective_of_mono_of_preservesPullback (Proj.stalkIso 𝒬 x).hom)

instance quadricSurface_isReduced : IsReduced (quadricSurface k) :=
  isReduced_of_isReduced_stalk _

instance quadricSurface_isIntegral : IsIntegral (quadricSurface k) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

/-- **The quadric surface is regular**: it is covered by four affine planes. -/
theorem quadricSurface_isRegular : (quadricSurface k).IsRegular := by
  have hreg (ij : Fin 2 × Fin 2) :
      IsRegularRing Γ(quadricSurface k, Proj.basicOpen 𝒬 (quadricChart k ij.1 ij.2)) :=
    IsRegularRing.of_ringEquiv ((quadricChartAwayEquiv k ij.1 ij.2).symm.trans
      (Proj.basicOpenIsoAway _ _ (quadricChart_mem k ij.1 ij.2)
        Nat.one_pos).commRingCatIsoToRingEquiv)
  have hcov := quadricSurface_iSup_basicOpen k
  have haff (ij : Fin 2 × Fin 2) := quadricSurface_isAffineOpen_basicOpen k ij.1 ij.2
  refine ⟨isLocallyNoetherian_of_affine_cover (S := fun ij => ⟨_, haff ij⟩) hcov
    fun ij => by have := hreg ij; infer_instance, fun x => ?_⟩
  obtain ⟨ij, hij⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcov.symm ▸ trivial :
    x ∈ ⨆ ij : Fin 2 × Fin 2, Proj.basicOpen 𝒬 (quadricChart k ij.1 ij.2))
  have := hreg ij
  exact isRegularAt_of_isAffineOpen (haff ij) x hij

instance quadricSurface_compactSpace : CompactSpace (quadricSurface k) := by
  constructor
  have h : (Set.univ : Set (quadricSurface k)) =
      ⋃ ij : Fin 2 × Fin 2, (Proj.basicOpen 𝒬 (quadricChart k ij.1 ij.2) : Set _) := by
    rw [← TopologicalSpace.Opens.coe_iSup, quadricSurface_iSup_basicOpen]
    rfl
  rw [h]
  exact isCompact_iUnion fun ij => (quadricSurface_isAffineOpen_basicOpen k ij.1 ij.2).isCompact

instance quadricSurface_isNoetherian : IsNoetherian (quadricSurface k) :=
  have := (quadricSurface_isRegular k).1
  {}

/-- **The quadric surface satisfies condition `(*)`**: it is Noetherian, integral, separated
and regular, in particular regular in codimension one. -/
theorem quadricSurface_satisfiesConditionStar : (quadricSurface k).SatisfiesConditionStar :=
  ⟨inferInstance, inferInstance, inferInstance, fun x _ ↦ (quadricSurface_isRegular k).2 x⟩

end ConditionStar

end Hartshorne

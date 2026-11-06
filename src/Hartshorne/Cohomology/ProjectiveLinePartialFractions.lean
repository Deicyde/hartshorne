/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Projective.LocalFraction
import Hartshorne.Projective.IrreducibleSpace
import Hartshorne.Projective.ProjSpaceDimension
import Hartshorne.Morphism.GlobalLocalIntersection
import Hartshorne.Curve.Cofinite
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Partial fractions on the projective line

Supporting algebra for Hartshorne, *Algebraic Geometry*, II.1, Exercise 1.21(e) (p. 68),
adopted for III, Exercise 2.2 (p. 212).

Let `X = ℙ¹` over an algebraically closed field `k`, with function field `K`. For every point
`P` and every `f ∈ K` there is a rational function `g`, regular at every point other than `P`,
with `f - g ∈ 𝒪_P`: the *principal part* of `f` at `P`.

Write `P = [v₀ : v₁]` and `ℓ = v₁x₀ - v₀x₁`, the linear form vanishing exactly at `P`. A binary
form vanishing at `P` is divisible by `ℓ` (the Nullstellensatz, since `(ℓ)` is prime). Writing
`f = G/H` with `G, H` forms of the same degree, split off the largest power of `ℓ` from
`H = ℓᵉ H'`, with `H'(P) ≠ 0`. Induction on `e` gives forms `A` of degree `e` and `G'` with
`G = A H' + ℓᵉ G'`: subtract the multiple `λ mᵉ H'` of `H'` (with `m` a coordinate not vanishing
at `P`) that kills `G` at `P`, and divide the difference by `ℓ`. Then
`f = A/ℓᵉ + G'/H'`, where `A/ℓᵉ` is regular away from `P` and `G'/H'` is regular at `P`.

The file also records that proper closed subsets of `ℙ¹` are finite, since `ℙ¹` is a curve.

## Main results

* `Hartshorne.projectiveLine_exists_principalPart`
* `Hartshorne.projectiveLine_finite_of_isClosed`
-/

noncomputable section

namespace Hartshorne

open MvPolynomial TopologicalSpace

universe u

section BinaryForms

variable {k : Type u} [Field k]

/-- The linear form `v₁x₀ - v₀x₁`, which vanishes exactly on the line spanned by `v`. -/
def binaryLinForm (v : Fin 2 → k) : MvPolynomial (Fin 2) k :=
  C (v 1) * X 0 - C (v 0) * X 1

theorem eval_binaryLinForm (v w : Fin 2 → k) :
    eval w (binaryLinForm v) = v 1 * w 0 - v 0 * w 1 := by
  simp [binaryLinForm]

theorem isHomogeneous_binaryLinForm (v : Fin 2 → k) : (binaryLinForm v).IsHomogeneous 1 :=
  (isHomogeneous_C_mul_X _ _).sub (isHomogeneous_C_mul_X _ _)

/-- The linear form of `v` vanishes at `w` only when `w` is a multiple of `v`. -/
theorem exists_eq_smul_of_eval_binaryLinForm_eq_zero {v w : Fin 2 → k} (hv : v ≠ 0)
    (h : eval w (binaryLinForm v) = 0) : ∃ t : k, w = t • v := by
  rw [eval_binaryLinForm, sub_eq_zero] at h
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1
      apply hv
      funext i
      fin_cases i
      · exact h0
      · exact h1
    rw [h0, zero_mul] at h
    have hw0 : w 0 = 0 := (mul_eq_zero.mp h).resolve_left h1
    refine ⟨w 1 / v 1, funext fun i => ?_⟩
    fin_cases i
    · simp [hw0, h0]
    · simp [h1]
  · refine ⟨w 0 / v 0, funext fun i => ?_⟩
    fin_cases i
    · simp [h0]
    · simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, smul_eq_mul]
      rw [div_mul_eq_mul_div, eq_div_iff h0]
      linear_combination -h

/-- Some point is not on the zero line of the linear form of a nonzero `v`. -/
theorem exists_eval_binaryLinForm_ne_zero {v : Fin 2 → k} (hv : v ≠ 0) :
    ∃ w : Fin 2 → k, w ≠ 0 ∧ eval w (binaryLinForm v) ≠ 0 := by
  by_cases h1 : v 1 = 0
  · have h0 : v 0 ≠ 0 := by
      intro h0
      apply hv
      funext i
      fin_cases i
      · exact h0
      · exact h1
    refine ⟨Pi.single 1 1, fun h => by simpa using congrFun h 1, ?_⟩
    simp [eval_binaryLinForm, h0]
  · refine ⟨Pi.single 0 1, fun h => by simpa using congrFun h 0, ?_⟩
    simp [eval_binaryLinForm, h1]

theorem binaryLinForm_ne_zero {v : Fin 2 → k} (hv : v ≠ 0) : binaryLinForm v ≠ 0 := by
  obtain ⟨w, -, hw⟩ := exists_eval_binaryLinForm_ne_zero hv
  intro h
  rw [h, map_zero] at hw
  exact hw rfl

/-- The linear form of a nonzero vector is prime. -/
theorem prime_binaryLinForm {v : Fin 2 → k} (hv : v ≠ 0) : Prime (binaryLinForm v) := by
  have hne := binaryLinForm_ne_zero hv
  refine UniqueFactorizationMonoid.irreducible_iff_prime.mp
    (irreducible_of_totalDegree_eq_one ((isHomogeneous_binaryLinForm v).totalDegree hne) ?_)
  intro x hx
  rw [isUnit_iff_ne_zero]
  rintro rfl
  apply hne
  ext i
  simpa using hx i

/-- Taking the homogeneous component commutes with multiplication by a linear form. -/
theorem homogeneousComponent_succ_mul {ℓ : MvPolynomial (Fin 2) k} (hℓ : ℓ.IsHomogeneous 1)
    (n : ℕ) (G : MvPolynomial (Fin 2) k) :
    homogeneousComponent (n + 1) (ℓ * G) = ℓ * homogeneousComponent n G := by
  conv_lhs => rw [← sum_homogeneousComponent G]
  rw [Finset.mul_sum, map_sum]
  have hterm : ∀ i ∈ Finset.range (G.totalDegree + 1),
      homogeneousComponent (n + 1) (ℓ * homogeneousComponent i G) =
        if n = i then ℓ * homogeneousComponent i G else 0 := by
    intro i _
    rw [homogeneousComponent_of_mem (hℓ.mul (homogeneousComponent_isHomogeneous i G))]
    congr 1
    apply propext
    omega
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq]
  split_ifs with hn
  · rfl
  · rw [Finset.mem_range, not_lt] at hn
    rw [homogeneousComponent_eq_zero n G (by omega), mul_zero]

variable [IsAlgClosed k]

/-- **Factor theorem for binary forms.** A form vanishing at a nonzero `v` is divisible by the
linear form of `v`. -/
theorem exists_eq_binaryLinForm_mul {v : Fin 2 → k} (hv : v ≠ 0) {n : ℕ}
    {F : MvPolynomial (Fin 2) k} (hF : F.IsHomogeneous (n + 1)) (hFv : eval v F = 0) :
    ∃ G : MvPolynomial (Fin 2) k, G.IsHomogeneous n ∧ F = binaryLinForm v * G := by
  let I : Ideal (MvPolynomial (Fin 2) k) := Ideal.span {binaryLinForm v}
  have : I.IsPrime :=
    (Ideal.span_singleton_prime (binaryLinForm_ne_zero hv)).mpr (prime_binaryLinForm hv)
  have hmem : F ∈ vanishingIdeal k (zeroLocus k I) := by
    intro w hw
    have hw' := hw (binaryLinForm v) (Ideal.subset_span rfl)
    change eval w (binaryLinForm v) = 0 at hw'
    change eval w F = 0
    obtain ⟨t, rfl⟩ := exists_eq_smul_of_eval_binaryLinForm_eq_zero hv hw'
    rw [hF.eval_smul, hFv, mul_zero]
  rw [IsPrime.vanishingIdeal_zeroLocus] at hmem
  obtain ⟨G', hG'⟩ := Ideal.mem_span_singleton'.mp hmem
  refine ⟨homogeneousComponent n G', homogeneousComponent_isHomogeneous n G', ?_⟩
  calc F = homogeneousComponent (n + 1) F := (homogeneousComponent_eq_self hF).symm
    _ = homogeneousComponent (n + 1) (binaryLinForm v * G') := by rw [← hG', mul_comm]
    _ = binaryLinForm v * homogeneousComponent n G' :=
      homogeneousComponent_succ_mul (isHomogeneous_binaryLinForm v) n G'

/-- **Splitting off the order of vanishing.** A nonzero form is `ℓᵉ H'` with `H'` not vanishing
at `v`. -/
theorem exists_binaryLinForm_pow_mul {v : Fin 2 → k} (hv : v ≠ 0) :
    ∀ (n : ℕ) (H : MvPolynomial (Fin 2) k), H.IsHomogeneous n → H ≠ 0 →
      ∃ (e c : ℕ) (H' : MvPolynomial (Fin 2) k), H'.IsHomogeneous c ∧ e + c = n ∧
        eval v H' ≠ 0 ∧ H = binaryLinForm v ^ e * H' := by
  intro n
  induction n with
  | zero =>
    intro H hH hH0
    refine ⟨0, 0, H, hH, rfl, ?_, by simp⟩
    have hC := totalDegree_eq_zero_iff_eq_C.mp (hH.totalDegree hH0)
    intro hev
    apply hH0
    rw [hC, eval_C] at hev
    rw [hC, hev, map_zero]
  | succ n ih =>
    intro H hH hH0
    by_cases hev : eval v H = 0
    · obtain ⟨H₁, hH₁, rfl⟩ := exists_eq_binaryLinForm_mul hv hH hev
      obtain ⟨e, c, H', hH', hec, hH'v, rfl⟩ :=
        ih H₁ hH₁ (right_ne_zero_of_mul hH0)
      exact ⟨e + 1, c, H', hH', by omega, hH'v, by ring⟩
    · exact ⟨0, n + 1, H, hH, by omega, hev, by simp⟩

/-- **The division step.** If `H'` is a form of degree `c` not vanishing at `v`, every form `G`
of degree `e + c` is `A H' + ℓᵉ G'` with `A` of degree `e` and `G'` of degree `c`. -/
theorem exists_eq_mul_add_binaryLinForm_pow_mul {v : Fin 2 → k} (hv : v ≠ 0) {c : ℕ}
    {H' : MvPolynomial (Fin 2) k} (hH' : H'.IsHomogeneous c) (hH'v : eval v H' ≠ 0) :
    ∀ (e : ℕ) (G : MvPolynomial (Fin 2) k), G.IsHomogeneous (e + c) →
      ∃ A G' : MvPolynomial (Fin 2) k, A.IsHomogeneous e ∧ G'.IsHomogeneous c ∧
        G = A * H' + binaryLinForm v ^ e * G' := by
  intro e
  induction e with
  | zero =>
    intro G hG
    exact ⟨0, G, isHomogeneous_zero _ _ _, by simpa using hG, by simp⟩
  | succ e ih =>
    intro G hG
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    let m : MvPolynomial (Fin 2) k := X i ^ (e + 1)
    have hm : m.IsHomogeneous (e + 1) := by
      simpa using (isHomogeneous_X k i).pow (e + 1)
    have hmv : eval v m ≠ 0 := by
      simp only [m, map_pow, eval_X]
      exact pow_ne_zero _ hi
    let lam : k := eval v G / (eval v m * eval v H')
    let F : MvPolynomial (Fin 2) k := G - C lam * m * H'
    have hF : F.IsHomogeneous ((e + c) + 1) := by
      have h1 : (C lam * m * H').IsHomogeneous (e + 1 + c) :=
        ((hm.C_mul lam).mul hH')
      have h2 : e + 1 + c = (e + c) + 1 := by omega
      rw [h2] at h1
      have h3 : e + 1 + c = (e + c) + 1 := by omega
      rw [h3] at hG
      exact hG.sub h1
    have hFv : eval v F = 0 := by
      simp only [F, lam, map_sub, map_mul, eval_C]
      field_simp
      ring
    obtain ⟨G₁, hG₁, hFG⟩ := exists_eq_binaryLinForm_mul hv hF hFv
    obtain ⟨A₁, G', hA₁, hG', hG₁eq⟩ := ih G₁ hG₁
    refine ⟨C lam * m + binaryLinForm v * A₁, G', ?_, hG', ?_⟩
    · have h1 := (isHomogeneous_binaryLinForm v).mul hA₁
      rw [show 1 + e = e + 1 by omega] at h1
      exact (hm.C_mul lam).add h1
    · have hG_eq : G = F + C lam * m * H' := by simp [F]
      rw [hG_eq, hFG, hG₁eq]
      ring

end BinaryForms

section FunctionField

variable {k : Type u} [Field k] {σ : Type*} {Y : Set (ProjectiveSpace k σ)}

/-- Every rational function on a quasi-projective variety is a ratio of forms of the same
degree. -/
theorem exists_eq_projRatClass (hY : IsQuasiProjVariety Y)
    (f : (Variety.ofQuasiProjective hY).FunctionField) :
    ∃ (n : ℕ) (G H : MvPolynomial σ k) (hG : G.IsHomogeneous n) (hH : H.IsHomogeneous n)
      (hne : ∃ P ∈ Y, eval P.rep H ≠ 0), f = projRatClass hY hG hH hne := by
  refine Quotient.inductionOn f fun r => ?_
  obtain ⟨x, hx⟩ := r.nonempty_U
  obtain ⟨W, hW, hxW, n, G, H, hG, hH, hHne, hrat⟩ :=
    (mem_projRegularSubalgebra.1 r.regular) ⟨x, hx⟩
  have hne : ∃ P ∈ Y, eval P.rep H ≠ 0 := ⟨x.1, x.2, hHne ⟨x, hx⟩ hxW⟩
  refine ⟨n, G, H, hG, hH, hne, ?_⟩
  let W' : Opens (Variety.ofQuasiProjective hY).carrier :=
    ⟨Subtype.val '' W, r.U.isOpen.isOpenMap_subtype_val W hW⟩
  have hW'U : W' ≤ r.U := by
    rintro y ⟨w, -, rfl⟩
    exact w.2
  let r' : Variety.RationalRep (Variety.ofQuasiProjective hY) :=
    { U := W'
      nonempty_U := ⟨x, ⟨⟨x, hx⟩, hxW, rfl⟩⟩
      toFun := fun y => r.toFun ⟨y.1, hW'U y.2⟩
      regular := (Variety.ofQuasiProjective hY).regular_restrict hW'U r.regular }
  have h1 : (Quotient.mk _ r : (Variety.ofQuasiProjective hY).FunctionField) =
      Quotient.mk _ r' := Quotient.sound fun _ _ _ => rfl
  have h2 : (Quotient.mk _ r' : (Variety.ofQuasiProjective hY).FunctionField) =
      projRatClass hY hG hH hne := by
    apply Quotient.sound
    rintro y ⟨w, hwW, rfl⟩ -
    exact hrat w hwW
  exact h1.trans h2

/-- Ratios of forms add as fractions. -/
theorem projRatClass_eq_add (hY : IsQuasiProjVariety Y) {n a b : ℕ}
    {G H A B C D : MvPolynomial σ k} (hG : G.IsHomogeneous n) (hH : H.IsHomogeneous n)
    (hA : A.IsHomogeneous a) (hB : B.IsHomogeneous a) (hC : C.IsHomogeneous b)
    (hD : D.IsHomogeneous b) (hne : ∃ P ∈ Y, eval P.rep H ≠ 0)
    (hneB : ∃ P ∈ Y, eval P.rep B ≠ 0) (hneD : ∃ P ∈ Y, eval P.rep D ≠ 0)
    (heq : G * (B * D) = (A * D + C * B) * H) :
    projRatClass hY hG hH hne = projRatClass hY hA hB hneB + projRatClass hY hC hD hneD := by
  apply Quotient.sound
  intro x hx hx'
  have hHx : eval x.1.rep H ≠ 0 := hx
  have hBx : eval x.1.rep B ≠ 0 := hx'.1
  have hDx : eval x.1.rep D ≠ 0 := hx'.2
  change eval x.1.rep G / eval x.1.rep H =
    eval x.1.rep A / eval x.1.rep B + eval x.1.rep C / eval x.1.rep D
  rw [div_add_div _ _ hBx hDx, div_eq_div_iff hHx (mul_ne_zero hBx hDx)]
  have := congrArg (eval x.1.rep) heq
  simp only [map_mul, map_add] at this
  linear_combination this

/-- A ratio of forms whose denominator does not vanish at `P` lies in the local ring at `P`. -/
theorem projRatClass_mem_localRingRange (hY : IsQuasiProjVariety Y)
    (P : (Variety.ofQuasiProjective hY).carrier) {n : ℕ} {G H : MvPolynomial σ k}
    (hG : G.IsHomogeneous n) (hH : H.IsHomogeneous n) (hne : ∃ R ∈ Y, eval R.rep H ≠ 0)
    (hP : eval P.1.rep H ≠ 0) :
    projRatClass hY hG hH hne ∈ (Variety.ofQuasiProjective hY).localRingRange P := by
  let q := projRatOfFraction hY hG hH hne
  let r : Variety.GermRep (Variety.ofQuasiProjective hY) P :=
    { U := q.U
      mem_U := hP
      toFun := q.toFun
      regular := q.regular }
  exact ⟨Quotient.mk _ r, Quotient.sound fun _ _ _ => rfl⟩

end FunctionField

section ProjectiveLine

variable (k : Type u) [Field k] [IsAlgClosed k]

theorem isQuasiProjVariety_projectiveLine :
    IsQuasiProjVariety (Set.univ : Set (ProjectiveSpace k (Fin 2))) :=
  (isProjVariety_univ (k := k) (σ := Fin 2)).isQuasiProjVariety

/-- The projective line `ℙ¹` over `k`, as a variety. -/
abbrev projectiveLine : Variety k :=
  Variety.ofQuasiProjective (isQuasiProjVariety_projectiveLine k)

variable {k}

/-- **Principal parts on `ℙ¹`.** For every point `P` and every rational function `f` there is a
rational function `g`, regular at every point other than `P`, with `f - g` regular at `P`. -/
theorem projectiveLine_exists_principalPart (P : (projectiveLine k).carrier)
    (f : (projectiveLine k).FunctionField) :
    ∃ g : (projectiveLine k).FunctionField,
      (∀ Q, Q ≠ P → g ∈ (projectiveLine k).localRingRange Q) ∧
        f - g ∈ (projectiveLine k).localRingRange P := by
  have hY := isQuasiProjVariety_projectiveLine k
  obtain ⟨n, G, H, hG, hH, hne, rfl⟩ := exists_eq_projRatClass hY f
  let v : Fin 2 → k := P.1.rep
  have hv : v ≠ 0 := P.1.rep_nonzero
  have hH0 : H ≠ 0 := by
    rintro rfl
    obtain ⟨R, -, hR⟩ := hne
    exact hR (map_zero _)
  obtain ⟨e, c, H', hH', hec, hH'v, hHeq⟩ := exists_binaryLinForm_pow_mul hv n H hH hH0
  subst hec
  obtain ⟨A, G', hA, hG', hGeq⟩ :=
    exists_eq_mul_add_binaryLinForm_pow_mul hv hH' hH'v e G hG
  have hℓe : (binaryLinForm v ^ e).IsHomogeneous e := by
    simpa using (isHomogeneous_binaryLinForm v).pow e
  obtain ⟨w, hw0, hw⟩ := exists_eval_binaryLinForm_ne_zero hv
  have hneℓ : ∃ R ∈ (Set.univ : Set (ProjectiveSpace k (Fin 2))),
      eval R.rep (binaryLinForm v ^ e) ≠ 0 := by
    refine ⟨Projectivization.mk k w hw0, trivial, ?_⟩
    refine (homogeneousVanish_iff_of_isHomogeneous hℓe hw0).not.mpr ?_
    rw [map_pow]
    exact pow_ne_zero _ hw
  have hneH' : ∃ R ∈ (Set.univ : Set (ProjectiveSpace k (Fin 2))), eval R.rep H' ≠ 0 :=
    ⟨P.1, trivial, hH'v⟩
  refine ⟨projRatClass hY hA hℓe hneℓ, ?_, ?_⟩
  · intro Q hQ
    apply projRatClass_mem_localRingRange
    rw [map_pow]
    refine pow_ne_zero _ fun hQv => hQ ?_
    obtain ⟨t, ht⟩ := exists_eq_smul_of_eval_binaryLinForm_eq_zero hv hQv
    apply Subtype.ext
    rw [← Projectivization.mk_rep Q.1, ← Projectivization.mk_rep P.1]
    rw [Projectivization.mk_eq_mk_iff']
    exact ⟨t, ht.symm⟩
  · have hsum := projRatClass_eq_add hY hG hH hA hℓe hG' hH' hne hneℓ hneH'
      (by rw [hHeq, hGeq]; ring)
    rw [hsum, add_sub_cancel_left]
    exact projRatClass_mem_localRingRange hY P hG' hH' hneH' hH'v

/-- **Proper closed subsets of `ℙ¹` are finite.** -/
theorem projectiveLine_finite_of_isClosed :
    ∀ Z : Set (projectiveLine k).carrier, IsClosed Z → Z ≠ Set.univ → Z.Finite := by
  intro Z hZ hZne
  have hcurve : (projectiveLine k).IsCurve := projDim_univ_fin (k := k) 1
  exact (((isQuasiProjVariety_projectiveLine k).isCurve_infinite_and_isClosed_iff hcurve).2
    Z).1 hZ |>.resolve_left hZne

end ProjectiveLine

end Hartshorne

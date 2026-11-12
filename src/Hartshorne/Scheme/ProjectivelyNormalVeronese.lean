/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ProjEventualSectionRecovery
import Hartshorne.Scheme.ProjectiveNormalityCriterion
import Hartshorne.Scheme.VeroneseDuple

/-!
# Projectively normal Veronese embeddings

Hartshorne, *Algebraic Geometry*, II, Exercise 5.14(b,c) (p. 126).

Let `k` be algebraically closed, `S = k[x₀, …, xᵣ]`, and let `X ⊆ ℙʳ_k` be a connected normal
closed subscheme with homogeneous coordinate ring `S(X) = S/I`, `I` saturated, so `X = Proj (S/I)`
(Corollary 5.16). For `d > 0` let `y_I` be the homogeneous coordinates of `ℙᴺ_k` indexed by the
monomials `x^I` of degree `d`.

## Main definitions

* `projDupleMap`: the `d`-uple embedding `ρ_d : ℙʳ_k ⟶ ℙᴺ_k`, `Proj S ≅ Proj S^{(d)}` followed by
  the morphism induced by `y_I ↦ x^I`.
* `projDupleEmbedding`: the `d`-uple embedding of `X`, the same construction for `S/I`; it is the
  restriction of `ρ_d` (`projQuotientι_comp_projDupleMap`) and a closed immersion.
* `dupleIdeal`: the kernel `J_d` of `y_I ↦ x^I`, `k[y_I] → S/I`, a homogeneous ideal.

## Main results

* `isIntegrallyClosed_veroneseSubring`: a criterion for a Veronese subring `A^{(d)}` of a graded
  domain to be integrally closed; components of degree not divisible by `d` of an element of the
  fraction field integral over `A^{(d)}` vanish (`sum_filter_not_dvd_eq_zero`).
* `exists_mem_algebraMap_eq_sectionToFraction` (Exercise 5.14(b)): by Exercise 5.9, every global
  section of `𝒪_X(n)`, `n ≫ 0`, comes from `(S/I)_n`: `S_n = S'_n` in the fraction field.
* `exists_isIntegrallyClosed_veroneseSubring`: `(S/I)^{(d)}` is integrally closed for `d ≫ 0`.
* `projDupleEmbedding_eq`, `dupleQuotientEquiv`: the image of `X` under the `d`-uple embedding is
  the closed subscheme `Proj (k[y_I] / J_d)`, and `k[y_I] / J_d ≅ (S/I)^{(d)}`.
* `exists_isProjectivelyNormal_image_projDupleMap` (Exercise 5.14(b,c)): for `d ≫ 0` the image of
  `X` under `ρ_d` is projectively normal.

## Proof

Following the book. By Exercise 5.14(a)
(`ProjectiveSectionRing.projectiveSectionRing_isIntegralClosure`) `S/I` is a domain and `S' = ⨁_{n ≥ 0} Γ(X, 𝒪_X(n))` is its integral closure in its fraction field
`K`, embedded by values at the generic point. By Exercise 5.9
(`EventualSectionRecovery.exists_bijective_alphaComponent`, for the graded module `S/I`) every
section of `𝒪_X(n)` is `s / 1` with `s ∈ (S/I)_n` once `n ≥ n₀`; in degree `0` an element of `K`
integral over `S/I` is integral over `(S/I)₀ = k` (`exists_monic_coeff_mem_zero`), hence in `k`.
So `S_n = S'_n` for `n = 0` and `n ≥ n₀`, and for `d ≥ n₀` an element of the fraction field of
`(S/I)^{(d)}` integral over it lies in `S'`, has no components of degree prime to `d`, and its
remaining components lie in `(S/I)_{nd}`. Finally `J_d` is saturated, so it is the homogeneous
ideal `Γ_*(ℐ) ∩ k[y_I]` of the image (Exercise 5.10, `gammaStarIdeal_ker_projQuotientι`), whose
homogeneous coordinate ring `k[y_I] / J_d ≅ (S/I)^{(d)}` is therefore an integrally closed domain.
-/

universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open _root_.Polynomial

namespace Hartshorne

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace HomogeneousLocalization
open GradedGlobalSections MonoidalCategory ProjGradedModuleSheaf

namespace ProjectivelyNormalVeronese

open ProjectiveSectionRing

/-! ### Homogeneous fractions of degree zero -/

section DegreeZero

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] [IsDomain A]

/-- An element of degree `0` of the fraction field which is integral over `A` is a root of a
monic polynomial with coefficients in `A₀`: take the degree-`0` parts of the coefficients of an
integral equation. -/
private theorem exists_monic_coeff_mem_zero {w : FractionRing A} (hw : IsHomFrac (𝒜 := 𝒜) 0 w)
    (hint : IsIntegral A w) :
    ∃ p : A[X], p.Monic ∧ (∀ i, p.coeff i ∈ 𝒜 0) ∧ aeval w p = 0 := by
  obtain ⟨e, a, s, ha, hs, hs0, rfl⟩ := hw
  obtain ⟨p, hpm, hp⟩ := hint
  set f := algebraMap A (FractionRing A)
  have hfs : f s ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).2 hs0
  have key : ∀ q : A[X], f (eval a (q.scaleRoots s)) = f s ^ q.natDegree * aeval (f a / f s) q := by
    intro q
    have := scaleRoots_eval₂_mul (p := q) f (f a / f s) s
    rwa [mul_div_cancel₀ _ hfs, eval₂_at_apply] at this
  set p₀ := p.map (GradedRing.projZeroRingHom 𝒜)
  have hdeg : p₀.natDegree = p.natDegree := hpm.natDegree_map _
  have hmem : ∀ i ∈ Finset.range (p.natDegree + 1),
      s ^ (p.natDegree - i) * a ^ i ∈ 𝒜 (e * p.natDegree) := by
    intro i hi
    have hi' : i ≤ p.natDegree := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have h1 := SetLike.mul_mem_graded (SetLike.pow_mem_graded (p.natDegree - i) hs)
      (SetLike.pow_mem_graded i ha)
    have : (p.natDegree - i) • e + i • (e + 0) = e * p.natDegree := by
      rw [smul_eq_mul, smul_eq_mul, add_zero, ← add_mul, Nat.sub_add_cancel hi', mul_comm]
    rwa [this] at h1
  have h1 : eval a (p.scaleRoots s) = 0 := by
    apply IsFractionRing.injective A (FractionRing A)
    rw [key, map_zero]
    have hp' : aeval (f a / f s) p = 0 := hp
    rw [hp', mul_zero]
  have h2 : eval a (p₀.scaleRoots s) = 0 := by
    rw [eval_eq_sum_range, natDegree_scaleRoots] at h1 ⊢
    rw [hdeg]
    have h3 := congrArg (GradedRing.proj 𝒜 (0 + e * p.natDegree)) h1
    rw [map_sum, map_zero] at h3
    rw [← h3]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [GradedRing.proj_apply, coeff_scaleRoots, coeff_scaleRoots, hdeg, mul_assoc, mul_assoc,
      DirectSum.coe_decompose_mul_add_of_right_mem 𝒜 (hmem i hi)]
    simp [p₀, coeff_map]
  refine ⟨p₀, hpm.map _, fun i => ?_, ?_⟩
  · rw [coeff_map, GradedRing.projZeroRingHom_apply]
    exact SetLike.coe_mem _
  · have h4 := key p₀
    rw [h2, map_zero, hdeg] at h4
    exact (mul_eq_zero.1 h4.symm).resolve_left (pow_ne_zero _ hfs)

/-- **Degree-zero integral elements are constants.** If `A₀` is the image of an algebraically
closed field `k`, an element of degree `0` of the fraction field integral over `A` lies in
`A₀`. -/
theorem exists_mem_zero_eq_of_isIntegral (k : Type u) [Field k] [IsAlgClosed k] [Algebra k A]
    (h0 : ∀ a ∈ 𝒜 0, ∃ c : k, algebraMap k A c = a) (h0' : ∀ c : k, algebraMap k A c ∈ 𝒜 0)
    {w : FractionRing A} (hw : IsHomFrac (𝒜 := 𝒜) 0 w) (hint : IsIntegral A w) :
    ∃ a ∈ 𝒜 0, algebraMap A (FractionRing A) a = w := by
  obtain ⟨p, hpm, hpc, hp⟩ := exists_monic_coeff_mem_zero hw hint
  have hlift : p ∈ lifts (algebraMap k A) :=
    (lifts_iff_coeff_lifts p).2 fun i => h0 _ (hpc i)
  obtain ⟨q, hqp, -, hqm⟩ := lifts_and_natDegree_eq_and_monic hlift hpm
  have hwk : IsIntegral k w := ⟨q, hqm, by
    rw [← aeval_def, ← aeval_map_algebraMap A, hqp, hp]⟩
  obtain ⟨c, hc⟩ := minpoly.mem_range_of_degree_eq_one k w
    (IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hwk))
  exact ⟨algebraMap k A c, h0' c, by rw [← hc, ← IsScalarTower.algebraMap_apply k A]⟩

end DegreeZero

/-! ### Veronese subrings -/

section VeroneseNormal

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜]

variable (𝒜) in
open Classical in
/-- The sum of the homogeneous components of degree not divisible by `d`. -/
private def offProj (d : ℕ) : A →+ A :=
  (DirectSum.toAddMonoid fun n => if d ∣ n then 0 else AddSubmonoidClass.subtype (𝒜 n)).comp
    (DirectSum.decomposeAddEquiv 𝒜).toAddMonoidHom

private theorem offProj_of_mem {d n : ℕ} {a : A} (ha : a ∈ 𝒜 n) :
    offProj 𝒜 d a = if d ∣ n then 0 else a := by
  classical
  simp only [offProj, AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
    DirectSum.decomposeAddEquiv_apply, DirectSum.decompose_of_mem 𝒜 ha, DirectSum.toAddMonoid_of]
  split_ifs <;> rfl

private theorem offProj_mul {d : ℕ} {x : A} (hx : x ∈ veroneseSubring 𝒜 d) (c : A) :
    offProj 𝒜 d (x * c) = x * offProj 𝒜 d c := by
  classical
  rw [← DirectSum.sum_support_decompose 𝒜 x, ← DirectSum.sum_support_decompose 𝒜 c,
    Finset.sum_mul_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hi : d ∣ i
  · rw [offProj_of_mem (SetLike.mul_mem_graded (DirectSum.decompose 𝒜 x i).2
      (DirectSum.decompose 𝒜 c j).2), offProj_of_mem (DirectSum.decompose 𝒜 c j).2]
    by_cases hj : d ∣ j
    · rw [if_pos (dvd_add hi hj), if_pos hj, mul_zero]
    · rw [if_neg (fun h => hj ((Nat.dvd_add_right hi).1 h)), if_neg hj]
  · rw [Veronese.mem_veroneseSubring_iff.1 hx i hi, zero_mul, zero_mul, map_zero]

private theorem offProj_eq_zero {d : ℕ} {x : A} (hx : x ∈ veroneseSubring 𝒜 d) :
    offProj 𝒜 d x = 0 := by
  have := offProj_mul hx 1
  rwa [mul_one, offProj_of_mem (SetLike.GradedOne.one_mem (A := 𝒜)), if_pos (dvd_zero d),
    mul_zero] at this

variable [IsDomain A]

/-- Finitely many homogeneous fractions have a common denominator. -/
private theorem exists_common_denom (F : Finset ℕ) (w : ℕ → FractionRing A)
    (hw : ∀ n ∈ F, IsHomFrac (𝒜 := 𝒜) n (w n)) :
    ∃ (E : ℕ) (D : A) (c : ℕ → A), D ∈ 𝒜 E ∧ D ≠ 0 ∧ ∀ n ∈ F, c n ∈ 𝒜 (E + n) ∧
      algebraMap A (FractionRing A) D * w n = algebraMap A (FractionRing A) (c n) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    exact ⟨0, 1, 0, SetLike.GradedOne.one_mem, one_ne_zero, fun n hn => absurd hn (by simp)⟩
  | insert m F hm ih =>
    obtain ⟨E, D, c, hD, hD0, hc⟩ := ih fun n hn => hw n (Finset.mem_insert_of_mem hn)
    obtain ⟨e, a, s, ha, hs, hs0, has⟩ := hw m (Finset.mem_insert_self m F)
    have hfs : algebraMap A (FractionRing A) s ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).2 hs0
    refine ⟨E + e, D * s, fun n => if n = m then a * D else c n * s,
      SetLike.mul_mem_graded hD hs, mul_ne_zero hD0 hs0, fun n hn => ?_⟩
    dsimp only
    rcases Finset.mem_insert.1 hn with rfl | hn
    · rw [if_pos rfl]
      refine ⟨?_, ?_⟩
      · have := SetLike.mul_mem_graded ha hD
        rwa [show e + n + E = E + e + n by omega] at this
      · rw [has, map_mul, map_mul]
        field_simp
    · rw [if_neg (fun h : n = m => hm (h ▸ hn))]
      obtain ⟨hcn, hcw⟩ := hc n hn
      refine ⟨?_, ?_⟩
      · have := SetLike.mul_mem_graded hcn hs
        rwa [show E + n + e = E + e + n by omega] at this
      · rw [map_mul, map_mul, ← hcw]
        ring

/-- The same, with the degree of the common denominator divisible by `d > 0`. -/
private theorem exists_common_denom_dvd {d : ℕ} (hd : 0 < d) (F : Finset ℕ) (w : ℕ → FractionRing A)
    (hw : ∀ n ∈ F, IsHomFrac (𝒜 := 𝒜) n (w n)) :
    ∃ (E : ℕ) (D : A) (c : ℕ → A), d ∣ E ∧ D ∈ 𝒜 E ∧ D ≠ 0 ∧ ∀ n ∈ F, c n ∈ 𝒜 (E + n) ∧
      algebraMap A (FractionRing A) D * w n = algebraMap A (FractionRing A) (c n) := by
  obtain ⟨E, D, c, hD, hD0, hc⟩ := exists_common_denom F w hw
  refine ⟨d * E, D ^ d, fun n => c n * D ^ (d - 1), dvd_mul_right d E, ?_, pow_ne_zero _ hD0,
    fun n hn => ?_⟩
  · have := SetLike.pow_mem_graded d hD
    rwa [smul_eq_mul] at this
  · obtain ⟨hcn, hcw⟩ := hc n hn
    refine ⟨?_, ?_⟩
    · have := SetLike.mul_mem_graded hcn (SetLike.pow_mem_graded (d - 1) hD)
      have e : E + n + (d - 1) • E = d * E + n := by
        rw [smul_eq_mul]
        obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
        rw [Nat.add_sub_cancel]
        ring
      rwa [e] at this
    · rw [map_mul, map_pow, ← hcw]
      obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
      rw [Nat.add_sub_cancel, pow_succ, map_pow]
      ring

/-- **Components of degree not divisible by `d` drop out.** If `b z = a` with `a, b ∈ S^{(d)}`,
`b ≠ 0`, and `z` is a finite sum of homogeneous fractions `w_n` of degree `n`, then the sum of
the `w_n` with `d ∤ n` vanishes: in `b z = a`, components of degree not divisible by `d` can
only come from them. -/
theorem sum_filter_not_dvd_eq_zero {d : ℕ} (hd : 0 < d) {F : Finset ℕ} {w : ℕ → FractionRing A}
    (hw : ∀ n ∈ F, IsHomFrac (𝒜 := 𝒜) n (w n)) {a b : A} (ha : a ∈ veroneseSubring 𝒜 d)
    (hb : b ∈ veroneseSubring 𝒜 d) (hb0 : b ≠ 0)
    (h : algebraMap A (FractionRing A) b * ∑ n ∈ F, w n = algebraMap A (FractionRing A) a) :
    ∑ n ∈ F with ¬d ∣ n, w n = 0 := by
  classical
  obtain ⟨E, D, c, hE, hD, hD0, hc⟩ := exists_common_denom_dvd hd F w hw
  set f := algebraMap A (FractionRing A)
  have hDv : D ∈ veroneseSubring 𝒜 d := Veronese.mem_veroneseAddSubgroup_of_mem_of_dvd hE hD
  have h1 : b * ∑ n ∈ F, c n = D * a := by
    apply IsFractionRing.injective A (FractionRing A)
    rw [map_mul, map_sum, map_mul, ← h, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [← (hc n hn).2]
    ring
  have h2 := congrArg (offProj 𝒜 d) h1
  rw [offProj_mul hb, offProj_mul hDv, offProj_eq_zero ha, mul_zero, map_sum] at h2
  have h3 : ∑ n ∈ F, offProj 𝒜 d (c n) = ∑ n ∈ F with ¬d ∣ n, c n := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [offProj_of_mem (hc n hn).1]
    by_cases hn' : d ∣ n
    · rw [if_pos ((Nat.dvd_add_right hE).2 hn'), if_neg (not_not.2 hn')]
    · rw [if_neg (fun h' => hn' ((Nat.dvd_add_right hE).1 h')), if_pos hn']
  rw [h3] at h2
  have h4 : ∑ n ∈ F with ¬d ∣ n, c n = 0 := (mul_eq_zero.1 h2).resolve_left hb0
  have hfD : f D ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).2 hD0
  have h5 : f D * ∑ n ∈ F with ¬d ∣ n, w n = 0 := by
    rw [Finset.mul_sum, ← map_zero f, ← h4, map_sum]
    exact Finset.sum_congr rfl fun n hn => (hc n (Finset.mem_filter.1 hn).1).2
  exact (mul_eq_zero.1 h5).resolve_left hfD

/-- **A Veronese subring of a graded domain is integrally closed** as soon as every element of the
fraction field integral over `A` is a finite sum of homogeneous fractions `w_n` of degree `n`
with property `P n w_n` (`hdec`), and every homogeneous fraction of degree `n` divisible by `d`
with property `P n` lies in `A_n` (`hrec`). (With `P` = "integral over `A`" and `A` integrally
closed this says that every Veronese subring of a graded normal domain is normal.) -/
theorem isIntegrallyClosed_veroneseSubring {d : ℕ} (hd : 0 < d) (P : ℕ → FractionRing A → Prop)
    (hdec : ∀ z : FractionRing A, IsIntegral A z → ∃ (F : Finset ℕ) (w : ℕ → FractionRing A),
      (∀ n ∈ F, IsHomFrac (𝒜 := 𝒜) n (w n) ∧ P n (w n)) ∧ ∑ n ∈ F, w n = z)
    (hrec : ∀ n, d ∣ n → ∀ w : FractionRing A, IsHomFrac (𝒜 := 𝒜) n w → P n w →
      ∃ s ∈ 𝒜 n, algebraMap A (FractionRing A) s = w) :
    IsIntegrallyClosed (veroneseSubring 𝒜 d) := by
  classical
  let R := veroneseSubring 𝒜 d
  obtain ⟨ι, hι⟩ : ∃ ι : R →+* FractionRing A, (algebraMap A (FractionRing A)).comp R.subtype = ι :=
    ⟨_, rfl⟩
  have hιinj : Function.Injective ι := by
    rw [← hι]
    exact (IsFractionRing.injective A (FractionRing A)).comp Subtype.val_injective
  let g : FractionRing R →+* FractionRing A := IsFractionRing.lift hιinj
  have hg : ∀ y : R, g (algebraMap R (FractionRing R) y) = ι y :=
    IsFractionRing.lift_algebraMap hιinj
  have hg' : ∀ (a : R) (b : nonZeroDivisors R),
      g (IsLocalization.mk' (FractionRing R) a b) = ι a / ι b :=
    IsFractionRing.lift_mk' hιinj
  rw [isIntegrallyClosed_iff (FractionRing R)]
  intro x hx
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) x
  have hb0 : (b : R) ≠ 0 := nonZeroDivisors.ne_zero b.2
  have hb0' : ((b : R) : A) ≠ 0 := fun h => hb0 (Subtype.ext h)
  -- the image `z = a / b` of `x` in the fraction field of `A` is integral over `A`
  have hz : IsIntegral A (g (IsLocalization.mk' (FractionRing R) a b)) := by
    obtain ⟨p, hpm, hp⟩ := hx
    refine ⟨p.map R.subtype, hpm.map _, ?_⟩
    have hgc : g.comp (algebraMap R (FractionRing R)) = ι := RingHom.ext hg
    rw [eval₂_map, hι, ← hgc, ← hom_eval₂]
    exact (congrArg g hp).trans (map_zero g)
  have hbz : algebraMap A (FractionRing A) (b : R) * g (IsLocalization.mk' (FractionRing R) a b) =
      algebraMap A (FractionRing A) (a : R) := by
    have e : ∀ y : R, algebraMap A (FractionRing A) (y : A) = ι y := fun y => by rw [← hι]; rfl
    rw [e, e, hg' a b]
    exact mul_div_cancel₀ _ ((map_ne_zero_iff _ hιinj).2 hb0)
  obtain ⟨F, w, hw, hsum⟩ := hdec _ hz
  have hoff := sum_filter_not_dvd_eq_zero hd (fun n hn => (hw n hn).1) a.2 b.1.2 hb0'
    (by rw [hsum]; exact hbz)
  have hon : ∀ n ∈ F.filter (fun n => d ∣ n), ∃ s ∈ 𝒜 n,
      algebraMap A (FractionRing A) s = w n := fun n hn =>
    hrec n (Finset.mem_filter.1 hn).2 (w n) (hw n (Finset.mem_filter.1 hn).1).1
      (hw n (Finset.mem_filter.1 hn).1).2
  choose! sn hsn hfsn using hon
  have hs : ∑ n ∈ F with d ∣ n, sn n ∈ R :=
    Subring.sum_mem _ fun n hn =>
      Veronese.mem_veroneseAddSubgroup_of_mem_of_dvd (Finset.mem_filter.1 hn).2 (hsn n hn)
  refine ⟨⟨_, hs⟩, g.injective ?_⟩
  rw [hg, ← hι, RingHom.comp_apply, Subring.coe_subtype, map_sum, ← hsum,
    ← Finset.sum_filter_add_sum_filter_not F (fun n => d ∣ n), hoff, add_zero]
  exact Finset.sum_congr rfl fun n hn => hfsn n hn

private theorem exists_finset_sectionRingToFraction_eq
    (y : DirectSum ℕ fun n => twistGlobal (𝟙_ (Proj 𝒜).Modules) (n : ℤ)) :
    ∃ F : Finset ℕ, sectionRingToFraction 𝒜 y = ∑ n ∈ F, sectionToFraction 𝒜 n (y n) := by
  classical
  refine ⟨y.support, ?_⟩
  conv_lhs => rw [← DirectSum.sum_support_of y]
  rw [map_sum]
  exact Finset.sum_congr rfl fun n _ => sectionRingToFraction_of 𝒜 n (y n)

end VeroneseNormal

/-! ### Closed subschemes of `ℙʳ_k` -/

section ClosedSubscheme

open MvPolynomial ProjTruncation ProjectiveNormality

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] {r : ℕ}
  (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) k))

local notation "𝒮" => MvPolynomial.homogeneousSubmodule (Fin (r + 1)) k
local notation "S" => MvPolynomial (Fin (r + 1)) k ⧸ I.toIdeal
local notation "𝒬" => gradedQuotient 𝒮 I

/-- The map `k → (S/I)₀`. -/
private def quotientZeroHom : k →+* 𝒬 0 :=
  (gradedQuotientMk 𝒮 I).gradedZeroRingHom.comp (algebraMap k (𝒮 0))

private theorem exists_algebraMap_eq_of_mem_zero {a : S} (ha : a ∈ 𝒬 0) :
    ∃ c : k, algebraMap k S c = a := by
  obtain ⟨b, hb, rfl⟩ := mem_gradedQuotient_iff.1 ha
  obtain ⟨c, hc⟩ := (bijective_algebraMap_mvPolynomial_homogeneousSubmodule_zero k r).2 ⟨b, hb⟩
  refine ⟨c, ?_⟩
  rw [← Ideal.Quotient.mk_algebraMap]
  congr 1
  simpa using congrArg Subtype.val hc

private theorem algebraMap_mem_zero (c : k) : algebraMap k S c ∈ 𝒬 0 := by
  rw [← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq]
  exact mk_mem_gradedQuotient (isHomogeneous_C _ c)

private theorem quotientZeroHom_surjective : Function.Surjective (quotientZeroHom I) := by
  intro y
  obtain ⟨c, hc⟩ := exists_algebraMap_eq_of_mem_zero I y.2
  refine ⟨c, Subtype.ext ?_⟩
  rw [← hc, ← Ideal.Quotient.mk_algebraMap]
  change Ideal.Quotient.mk I.toIdeal ((algebraMap k (𝒮 0) c : MvPolynomial (Fin (r + 1)) k)) = _
  simp

theorem adjoin_coord_eq_top : Algebra.adjoin (𝒬 0) (Set.range (coord I)) = ⊤ := by
  rw [eq_top_iff]
  rintro y -
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  induction p using MvPolynomial.induction_on with
  | C a =>
    exact Subalgebra.algebraMap_mem _ (quotientZeroHom I a)
  | add p q hp hq =>
    rw [map_add]
    exact add_mem hp hq
  | mul_X p j hp =>
    rw [map_mul]
    exact mul_mem hp (Algebra.subset_adjoin ⟨j, rfl⟩)

/-! ### The homogeneous ideal of the `d`-uple image -/

section Duple

variable (d : ℕ)

local notation "𝒮N" => MvPolynomial.homogeneousSubmodule (Fin (Veronese.dupleN r d + 1)) k

/-- `k[y_I] → k[x₀, …, xᵣ]`, `y_I ↦ x^I`, the `I` running over the monomials of degree `d`. -/
def dupleHom₀ :
    MvPolynomial (Fin (Veronese.dupleN r d + 1)) k →ₐ[k] MvPolynomial (Fin (r + 1)) k :=
  aeval fun j => monomial (Veronese.dupleEquiv r d j).1 (1 : k)

/-- `k[y_I] → S/I`, `y_I ↦ x^I`. Its kernel is the homogeneous ideal of the image of
`X = Proj (S/I)` under the `d`-uple embedding, and its image is `(S/I)^{(d)}`. -/
def dupleHom : MvPolynomial (Fin (Veronese.dupleN r d + 1)) k →ₐ[k] S :=
  (Ideal.Quotient.mkₐ k I.toIdeal).comp (dupleHom₀ d)

theorem dupleHom_mem {n : ℕ} {p : MvPolynomial (Fin (Veronese.dupleN r d + 1)) k}
    (hp : p ∈ 𝒮N n) : dupleHom I d p ∈ 𝒬 (n * d) := by
  have h : (dupleHom₀ (k := k) (r := r) d p).IsHomogeneous (d * n) :=
    IsHomogeneous.aeval hp _ fun j => isHomogeneous_monomial _ (Veronese.dupleEquiv r d j).2
  rw [mul_comm]
  exact mk_mem_gradedQuotient h

theorem dupleHom_X (j : Fin (Veronese.dupleN r d + 1)) :
    dupleHom I d (X j) = Veronese.monomialOf (coord I) (Veronese.dupleEquiv r d j).1 := by
  simp [dupleHom, dupleHom₀, Veronese.monomialOf, coord, monomial_eq]

theorem isHomogeneous_ker_dupleHom [NeZero d] : (RingHom.ker (dupleHom I d)).IsHomogeneous 𝒮N := by
  classical
  intro i p hp
  rw [RingHom.mem_ker] at hp ⊢
  have h := congrArg (GradedRing.proj 𝒬 (i * d)) hp
  rw [← DirectSum.sum_support_decompose 𝒮N p, map_sum, map_sum, map_zero] at h
  rw [Finset.sum_eq_single i] at h
  · rwa [GradedRing.proj_apply, DirectSum.decompose_of_mem_same 𝒬 (dupleHom_mem I d
      (DirectSum.decompose 𝒮N p i).2)] at h
  · intro j _ hji
    rw [GradedRing.proj_apply, DirectSum.decompose_of_mem_ne 𝒬 (dupleHom_mem I d
      (DirectSum.decompose 𝒮N p j).2)]
    intro h'
    exact hji (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (NeZero.ne d)) h')
  · intro hi
    rw [DFinsupp.notMem_support_iff.1 hi, ZeroMemClass.coe_zero, map_zero, map_zero]

/-- **The homogeneous ideal of the `d`-uple image of `X`**: the kernel of `y_I ↦ x^I`,
`k[y_I] → S/I`. -/
def dupleIdeal [NeZero d] : HomogeneousIdeal 𝒮N :=
  ⟨RingHom.ker (dupleHom I d), isHomogeneous_ker_dupleHom I d⟩

theorem dupleHom_mem_veroneseSubring (p : MvPolynomial (Fin (Veronese.dupleN r d + 1)) k) :
    dupleHom I d p ∈ veroneseSubring 𝒬 d := by
  classical
  rw [← DirectSum.sum_support_decompose 𝒮N p, map_sum]
  exact Subring.sum_mem _ fun n _ =>
    Veronese.mem_veroneseSubring_of_mem (dupleHom_mem I d (DirectSum.decompose 𝒮N p n).2)

/-- `k[y_I] → (S/I)^{(d)}`, `y_I ↦ x^I`. -/
def dupleHomV : MvPolynomial (Fin (Veronese.dupleN r d + 1)) k →+* veroneseSubring 𝒬 d :=
  (dupleHom I d).toRingHom.codRestrict _ (dupleHom_mem_veroneseSubring I d)

/-- The degree-`d` monomials generate `(S/I)^{(d)}` (`Veronese.adjoin_dupleCoords`). -/
theorem dupleHomV_surjective [NeZero d] : Function.Surjective (dupleHomV I d) := by
  intro v
  have hv : v ∈ Algebra.adjoin ((veronese 𝒬 d) 0)
      (Set.range (Veronese.dupleCoords d (coord I) (coord_mem I))) := by
    rw [Veronese.adjoin_dupleCoords (coord I) (coord_mem I) (adjoin_coord_eq_top I)]
    trivial
  induction hv using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact ⟨X j, Subtype.ext (dupleHom_X I d j)⟩
  | algebraMap c =>
    have hc : ((c : veroneseSubring 𝒬 d) : S) ∈ 𝒬 0 := by
      have := c.2
      rwa [Veronese.mem_veronese_iff, zero_mul] at this
    obtain ⟨a, ha⟩ := exists_algebraMap_eq_of_mem_zero I hc
    refine ⟨C a, Subtype.ext ?_⟩
    have e1 : dupleHom I d (C a) = algebraMap k S a := (dupleHom I d).commutes a
    change dupleHom I d (C a) =
      ((algebraMap ((veronese 𝒬 d) 0) (veroneseSubring 𝒬 d) c : veroneseSubring 𝒬 d) : S)
    rw [SetLike.GradeZero.algebraMap_apply, e1, ha]
  | add x y _ _ hx hy =>
    obtain ⟨p, rfl⟩ := hx
    obtain ⟨q, rfl⟩ := hy
    exact ⟨p + q, map_add _ _ _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨p, rfl⟩ := hx
    obtain ⟨q, rfl⟩ := hy
    exact ⟨p * q, map_mul _ _ _⟩

/-- **The homogeneous coordinate ring of the `d`-uple image is `(S/I)^{(d)}`**:
`k[y_I] / J_d ≅ (S/I)^{(d)}`. -/
def dupleQuotientEquiv [NeZero d] :
    (MvPolynomial (Fin (Veronese.dupleN r d + 1)) k ⧸ (dupleIdeal I d).toIdeal) ≃+*
      veroneseSubring 𝒬 d :=
  (Ideal.quotEquivOfEq (by
    ext p
    change dupleHom I d p = 0 ↔ dupleHomV I d p = 0
    rw [← Subtype.coe_inj]
    rfl)).trans (RingHom.quotientKerEquivOfSurjective (dupleHomV_surjective I d))

/-- `J_d` is saturated when `S/I` is a domain and `Proj (S/I)` is nonempty. -/
theorem mem_dupleIdeal_of_pow_mul_mem [NeZero d] [IsDomain S] (hne : ∃ i, coord I i ≠ 0)
    (s : MvPolynomial (Fin (Veronese.dupleN r d + 1)) k)
    (hs : ∀ j, ∃ n : ℕ, X j ^ n * s ∈ (dupleIdeal I d).toIdeal) :
    s ∈ (dupleIdeal I d).toIdeal := by
  obtain ⟨i, hi⟩ := hne
  let m : Veronese.DupleIndex r d := ⟨Finsupp.single i d, Finsupp.degree_single _ _⟩
  obtain ⟨n, hn⟩ := hs ((Veronese.dupleEquiv r d).symm m)
  change dupleHom I d _ = 0 at hn
  change dupleHom I d s = 0
  rw [map_mul, map_pow, dupleHom_X, Equiv.apply_symm_apply] at hn
  have hm : Veronese.monomialOf (coord I) m.1 = coord I i ^ d := by
    simp [m, Veronese.monomialOf]
  rw [hm] at hn
  exact (mul_eq_zero.1 hn).resolve_left (pow_ne_zero _ (pow_ne_zero _ hi))

end Duple

/-! ### The `d`-uple embedding of `X` -/

section DupleEmbedding

variable (d : ℕ) [NeZero d]

local notation "𝒮N" => MvPolynomial.homogeneousSubmodule (Fin (Veronese.dupleN r d + 1)) k

/-- The graded homomorphism `k[y_I] → (S/I)^{(d)}`, `y_I ↦ x^I` (`y_I` of degree one). -/
def dupleGradedHom : 𝒮N →+*ᵍ veronese 𝒬 d where
  __ := dupleHomV I d
  map_mem := by
    intro i p hp
    exact dupleHom_mem I d hp

theorem dupleGradedHom_surjective : Function.Surjective (dupleGradedHom I d) :=
  dupleHomV_surjective I d

/-- **The `d`-uple embedding of `X = Proj (S/I)`** into `ℙᴺ_k = Proj k[y_I]`: the isomorphism
`Proj (S/I) ≅ Proj (S/I)^{(d)}` followed by the morphism induced by `y_I ↦ x^I`, the monomials of
degree `d` in the coordinates. -/
def projDupleEmbedding : Proj 𝒬 ⟶ Proj 𝒮N :=
  (Veronese.projIso 𝒬 d).hom ≫
    Proj.map (dupleGradedHom I d) (irrelevant_le_map_of_surjective (dupleGradedHom_surjective I d))

/-- The graded isomorphism `k[y_I] / J_d → (S/I)^{(d)}`. -/
def dupleQuotientHom : gradedQuotient 𝒮N (dupleIdeal I d) →+*ᵍ veronese 𝒬 d where
  __ := (dupleQuotientEquiv I d).toRingHom
  map_mem := by
    intro i x hx
    obtain ⟨a, ha, rfl⟩ := mem_gradedQuotient_iff.mp hx
    exact dupleHom_mem I d ha

theorem dupleQuotientHom_mk (p : MvPolynomial (Fin (Veronese.dupleN r d + 1)) k) :
    dupleQuotientHom I d (Ideal.Quotient.mk _ p) = dupleGradedHom I d p :=
  rfl

theorem dupleQuotientHom_surjective : Function.Surjective (dupleQuotientHom I d) :=
  (dupleQuotientEquiv I d).surjective

theorem dupleQuotientHom_bijective (n : ℕ) :
    Function.Bijective ((dupleQuotientHom I d).gradedAddHom n) := by
  constructor
  · intro x y h
    exact Subtype.ext ((dupleQuotientEquiv I d).injective (congrArg Subtype.val h))
  · intro y
    obtain ⟨a, ha⟩ := dupleGradedHom_surjective I d y
    refine ⟨⟨Ideal.Quotient.mk _ (DirectSum.decompose 𝒮N a n : MvPolynomial _ k),
      mk_mem_gradedQuotient (DirectSum.decompose 𝒮N a n).2⟩, Subtype.ext ?_⟩
    rw [GradedRingHom.gradedAddHom_apply_coe]
    change dupleGradedHom I d (DirectSum.decompose 𝒮N a n : MvPolynomial _ k) = y
    rw [GradedRingHom.map_directSumDecompose, ha]
    exact DirectSum.decompose_of_mem_same (veronese 𝒬 d) y.2

theorem isIso_map_dupleQuotientHom :
    IsIso (Proj.map (dupleQuotientHom I d)
      (irrelevant_le_map_of_surjective (dupleQuotientHom_surjective I d))) := by
  have hiso : IsIso (projPartialMap (dupleQuotientHom I d)) :=
    isIso_projPartialMap_of_bijective (d₀ := 0) fun n _ => dupleQuotientHom_bijective I d n
  have hι : IsIso (projPartialDomain (dupleQuotientHom I d)).ι := by
    rw [isIso_iff_isOpenImmersion_and_surjective]
    refine ⟨inferInstance, ⟨fun y => ?_⟩⟩
    have hy : y ∈ projPartialDomain (dupleQuotientHom I d) := by
      rw [projPartialDomain_eq_top_of_surjective (dupleQuotientHom_surjective I d)]
      trivial
    exact ⟨⟨y, hy⟩, rfl⟩
  rw [projPartialMap_eq_map
    (irrelevant_le_map_of_surjective (dupleQuotientHom_surjective I d))] at hiso
  exact IsIso.of_isIso_comp_left (projPartialDomain (dupleQuotientHom I d)).ι _

/-- **The `d`-uple image of `X` is `Proj (k[y_I] / J_d)`**: the `d`-uple embedding is an
isomorphism `X ≅ Proj (k[y_I] / J_d)` followed by the closed immersion
`Proj (k[y_I] / J_d) ⟶ ℙᴺ_k`. -/
theorem projDupleEmbedding_eq :
    projDupleEmbedding I d = (Veronese.projIso 𝒬 d).hom ≫
      Proj.map (dupleQuotientHom I d)
        (irrelevant_le_map_of_surjective (dupleQuotientHom_surjective I d)) ≫
      projQuotientι 𝒮N (dupleIdeal I d) := by
  rw [projDupleEmbedding, projQuotientι_eq_map, ← Proj.map_comp]
  rfl

instance isClosedImmersion_projDupleEmbedding : IsClosedImmersion (projDupleEmbedding I d) := by
  have := isIso_map_dupleQuotientHom I d
  rw [projDupleEmbedding_eq]
  infer_instance

/-- The ideal sheaf of the `d`-uple image of `X` is the one cut out by `J_d`. -/
theorem ker_projDupleEmbedding :
    (projDupleEmbedding I d).ker = (projQuotientι 𝒮N (dupleIdeal I d)).ker := by
  have := isIso_map_dupleQuotientHom I d
  rw [projDupleEmbedding_eq, Scheme.Hom.ker_comp_of_isIso, Scheme.Hom.ker_comp_of_isIso]

end DupleEmbedding

/-! ### The `d`-uple map of `ℙʳ_k` restricts to the `d`-uple embedding of `X` -/

section DupleMap

variable (d : ℕ) [NeZero d]

local notation "𝒮N" => MvPolynomial.homogeneousSubmodule (Fin (Veronese.dupleN r d + 1)) k

omit [NeZero d] in
private theorem dupleHom₀_mem {n : ℕ} {p : MvPolynomial (Fin (Veronese.dupleN r d + 1)) k}
    (hp : p ∈ 𝒮N n) : dupleHom₀ (k := k) (r := r) d p ∈ 𝒮 (n * d) := by
  have h : (dupleHom₀ (k := k) (r := r) d p).IsHomogeneous (d * n) :=
    IsHomogeneous.aeval hp _ fun j => isHomogeneous_monomial _ (Veronese.dupleEquiv r d j).2
  rw [mul_comm]
  exact h

omit [NeZero d] in
private theorem dupleHom₀_mem_veroneseSubring (p : MvPolynomial (Fin (Veronese.dupleN r d + 1)) k) :
    dupleHom₀ (k := k) (r := r) d p ∈ veroneseSubring 𝒮 d := by
  classical
  rw [← DirectSum.sum_support_decompose 𝒮N p, map_sum]
  exact Subring.sum_mem _ fun n _ =>
    Veronese.mem_veroneseSubring_of_mem (dupleHom₀_mem d (DirectSum.decompose 𝒮N p n).2)

/-- The graded homomorphism `k[y_I] → k[x₀, …, xᵣ]^{(d)}`, `y_I ↦ x^I`. -/
def dupleMapHom : 𝒮N →+*ᵍ veronese 𝒮 d where
  toRingHom := (dupleHom₀ (k := k) (r := r) d).toRingHom.codRestrict _
    (dupleHom₀_mem_veroneseSubring d)
  map_mem := fun hp => dupleHom₀_mem d hp

omit [NeZero d] in
theorem veroneseMap_comp_dupleMapHom :
    (Veronese.veroneseMap d (gradedQuotientMk 𝒮 I)).comp (dupleMapHom d) = dupleGradedHom I d :=
  GradedRingHom.ext fun _ => rfl

theorem veroneseMap_gradedQuotientMk_surjective :
    Function.Surjective (Veronese.veroneseMap d (gradedQuotientMk 𝒮 I)) := fun v => by
  obtain ⟨p, hp⟩ := dupleGradedHom_surjective I d v
  exact ⟨dupleMapHom d p, by rw [← hp, ← veroneseMap_comp_dupleMapHom]; rfl⟩

omit [NeZero d] in
private theorem adjoin_X_eq_top :
    Algebra.adjoin (𝒮 0) (Set.range (X : Fin (r + 1) → MvPolynomial (Fin (r + 1)) k)) = ⊤ := by
  rw [eq_top_iff]
  rintro p -
  induction p using MvPolynomial.induction_on with
  | C a =>
    exact Subalgebra.algebraMap_mem _ (algebraMap k (𝒮 0) a)
  | add p q hp hq => exact add_mem hp hq
  | mul_X p j hp => exact mul_mem hp (Algebra.subset_adjoin ⟨j, rfl⟩)

theorem dupleMapHom_surjective : Function.Surjective (dupleMapHom (k := k) (r := r) d) := by
  intro v
  have hv : v ∈ Algebra.adjoin ((veronese 𝒮 d) 0)
      (Set.range (Veronese.dupleCoords d X (X_mem_homogeneousSubmodule_one k))) := by
    rw [Veronese.adjoin_dupleCoords X (X_mem_homogeneousSubmodule_one k) adjoin_X_eq_top]
    trivial
  induction hv using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    refine ⟨X j, Subtype.ext ?_⟩
    change dupleHom₀ d (X j) = Veronese.monomialOf X (Veronese.dupleEquiv r d j).1
    simp [dupleHom₀, Veronese.monomialOf, monomial_eq]
  | algebraMap c =>
    have hc : ((c : veroneseSubring 𝒮 d) : MvPolynomial (Fin (r + 1)) k) ∈ 𝒮 0 := by
      have := c.2
      rwa [Veronese.mem_veronese_iff, zero_mul] at this
    obtain ⟨a, ha⟩ := (bijective_algebraMap_mvPolynomial_homogeneousSubmodule_zero k r).2
      ⟨_, hc⟩
    refine ⟨C a, Subtype.ext ?_⟩
    have e1 : dupleHom₀ (k := k) (r := r) d (C a) = algebraMap k _ a :=
      (dupleHom₀ (k := k) (r := r) d).commutes a
    change dupleHom₀ d (C a) =
      ((algebraMap ((veronese 𝒮 d) 0) (veroneseSubring 𝒮 d) c : veroneseSubring 𝒮 d) :
        MvPolynomial (Fin (r + 1)) k)
    rw [SetLike.GradeZero.algebraMap_apply, e1]
    exact congrArg Subtype.val ha
  | add x y _ _ hx hy =>
    obtain ⟨p, rfl⟩ := hx
    obtain ⟨q, rfl⟩ := hy
    exact ⟨p + q, map_add _ _ _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨p, rfl⟩ := hx
    obtain ⟨q, rfl⟩ := hy
    exact ⟨p * q, map_mul _ _ _⟩

/-- **The `d`-uple map** `ρ_d : ℙʳ_k ⟶ ℙᴺ_k`: `Proj k[x] ≅ Proj k[x]^{(d)}` followed by the morphism
induced by `y_I ↦ x^I`. -/
def projDupleMap : Proj 𝒮 ⟶ Proj 𝒮N :=
  (Veronese.projIso 𝒮 d).hom ≫
    Proj.map (dupleMapHom d) (irrelevant_le_map_of_surjective (dupleMapHom_surjective d))

/-- **The `d`-uple embedding of `X` is the restriction of `ρ_d`** to `X ⊆ ℙʳ_k`. -/
theorem projQuotientι_comp_projDupleMap :
    projQuotientι 𝒮 I ≫ projDupleMap d = projDupleEmbedding I d := by
  rw [projQuotientι_eq_map, projDupleMap, projDupleEmbedding, Veronese.projIso_hom,
    Veronese.projIso_hom, ← Category.assoc,
    Veronese.map_comp_toProj d (gradedQuotientMk 𝒮 I) _
      (irrelevant_le_map_of_surjective (veroneseMap_gradedQuotientMk_surjective I d)),
    Category.assoc, ← Proj.map_comp]
  congr 2

end DupleMap

variable [IsDomain (MvPolynomial (Fin (r + 1)) k ⧸ I.toIdeal)]

/-- **Hartshorne II, Exercise 5.14(b).** For a closed subscheme `X = Proj (S/I)` of `ℙʳ_k` with
`S/I` a domain, every global section of `𝒪_X(n)`, `n ≫ 0`, comes from `(S/I)_n`: by
Exercise 5.9 the map `(S/I)_n → Γ(X, 𝒪_X(n))` is bijective for large `n`. In the fraction field
of `S/I`, `S_n = S'_n` for `n ≫ 0`. -/
theorem exists_mem_algebraMap_eq_sectionToFraction (h : ¬HomogeneousIdeal.irrelevant 𝒬 ≤ ⊥) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ t : twistGlobal (𝟙_ (Proj 𝒬).Modules) (n : ℤ),
      ∃ s ∈ 𝒬 n, algebraMap S (FractionRing S) s = sectionToFraction 𝒬 n t := by
  classical
  let _ : Algebra k (𝒬 0) := (quotientZeroHom I).toAlgebra
  have : Algebra.FiniteType k (𝒬 0) :=
    Algebra.FiniteType.of_surjective (Algebra.ofId k (𝒬 0)) (quotientZeroHom_surjective I)
  have hs : ∀ a ∈ (Finset.univ.image (coord I) : Finset S), a ∈ 𝒬 1 := by
    intro a ha
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ha
    exact coord_mem I i
  obtain ⟨d₀, hd₀⟩ := EventualSectionRecovery.exists_bijective_alphaComponent
    (ℳ := gradedTwist 𝒬 0) k hs (by
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
      exact adjoin_coord_eq_top I)
  refine ⟨d₀.toNat, fun n hn t => ?_⟩
  have hb := hd₀ n (by omega)
  have hmem : ∀ (i : ℤ) (m : S),
      m ∈ gradedModuleTwist (gradedTwist 𝒬 0) (n : ℤ) i ↔ m ∈ gradedTwist 𝒬 (n : ℤ) i := by
    intro i m
    change m ∈ gradedTwist 𝒬 0 (i + n) ↔ _
    change m ∈ 𝒬 (0 + (i + n)).toNat ∧ (0 + (i + n) < 0 → m = 0) ↔
      m ∈ 𝒬 ((n : ℤ) + i).toNat ∧ ((n : ℤ) + i < 0 → m = 0)
    rw [show (0 : ℤ) + (i + n) = n + i by ring]
  rw [EventualSectionRecovery.bijective_alphaComponent_iff,
    EventualSectionRecovery.bijective_constHom_iff,
    EventualSectionRecovery.bijective_constHom0_congr _ (gradedTwist 𝒬 (n : ℤ)) hmem] at hb
  obtain ⟨⟨m, hm⟩, hmt⟩ := hb.2 (unitorGlobal (n : ℤ) t)
  refine ⟨m, (mem_gradedTwist_of_eq (by simp)).1 hm, ?_⟩
  rw [sectionToFraction_apply h _ t (genericPoint h), ← hmt]
  unfold sectionValue
  change algebraMap S (FractionRing S) m = toFraction _ (LocalizedModule.mk m 1)
  rw [toFraction_mk]
  simp

omit [IsDomain (MvPolynomial (Fin (r + 1)) k ⧸ I.toIdeal)] in
/-- **Hartshorne II, Exercise 5.14(b,c), algebraic part.** Let `k` be algebraically closed and
`X = Proj (S/I) ⊆ ℙʳ_k` a connected normal closed subscheme, `I` saturated. Then `S/I` is a domain
and its Veronese subring `(S/I)^{(d)} = ⨁_n (S/I)_{nd}` is integrally closed for all large `d`.

Following the book: `S' = ⨁_{n ≥ 0} Γ(X, 𝒪_X(n))` is the integral closure of `S/I`
(Exercise 5.14(a)), `(S/I)_n = S'_n` for large `n` (Exercise 5.9,
`exists_mem_algebraMap_eq_sectionToFraction`)
and for `n = 0` (`S'_0` is integral over `k`), and the components of degree not divisible by `d`
of an element of the fraction field of `(S/I)^{(d)}` integral over it vanish
(`isIntegrallyClosed_veroneseSubring`). -/
theorem exists_isIntegrallyClosed_veroneseSubring [IsAlgClosed k]
    (hsat : ∀ s : MvPolynomial (Fin (r + 1)) k, (∀ i, ∃ n : ℕ, X i ^ n * s ∈ I.toIdeal) →
      s ∈ I.toIdeal)
    [ConnectedSpace (Proj 𝒬)] [Hartshorne.IsNormal (Proj 𝒬)] :
    IsDomain S ∧ ∃ d₀ : ℕ, 0 < d₀ ∧ ∀ d ≥ d₀, IsIntegrallyClosed (veroneseSubring 𝒬 d) := by
  obtain ⟨hdom, hic⟩ := projectiveSectionRing_isIntegralClosure I hsat
  refine ⟨hdom, ?_⟩
  have := ProjectiveSectionRing.isIntegral_proj I
  have : Nonempty (Proj 𝒬) := AlgebraicGeometry.IsIntegral.nonempty
  obtain ⟨-, -, hrange⟩ := @hic hdom
  have h := not_irrelevant_le_bot I
  obtain ⟨n₀, hn₀⟩ := exists_mem_algebraMap_eq_sectionToFraction I h
  refine ⟨max n₀ 1, by omega, fun d hd => ?_⟩
  have hint : ∀ (n : ℕ) (t : twistGlobal (𝟙_ (Proj 𝒬).Modules) (n : ℤ)),
      IsIntegral S (sectionToFraction 𝒬 n t) := by
    intro n t
    have hmem : sectionToFraction 𝒬 n t ∈ Set.range (sectionRingToFraction 𝒬) :=
      ⟨DirectSum.of _ n t, sectionRingToFraction_of 𝒬 n t⟩
    rw [hrange] at hmem
    exact hmem
  refine isIntegrallyClosed_veroneseSubring (by omega)
    (fun n w => ∃ t : twistGlobal (𝟙_ (Proj 𝒬).Modules) (n : ℤ), sectionToFraction 𝒬 n t = w)
    (fun z hz => ?_) ?_
  · have hz' : z ∈ Set.range (sectionRingToFraction 𝒬) := by
      rw [hrange]
      exact hz
    obtain ⟨y, hy⟩ := hz'
    obtain ⟨F, hF⟩ := exists_finset_sectionRingToFraction_eq (𝒜 := 𝒬) y
    exact ⟨F, fun n => sectionToFraction 𝒬 n (y n),
      fun n _ => ⟨isHomFrac_sectionToFraction h n (y n), y n, rfl⟩, hF.symm.trans hy⟩
  · rintro n hdn w hw ⟨t, rfl⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact exists_mem_zero_eq_of_isIntegral k (fun a ha => exists_algebraMap_eq_of_mem_zero I ha)
        (algebraMap_mem_zero I) hw (hint 0 t)
    · have := Nat.le_of_dvd hn hdn
      exact hn₀ n (by omega) t

section DupleNormal

open ProjectiveClosedSubscheme

variable (d : ℕ) [NeZero d]

local notation "𝒮N" => MvPolynomial.homogeneousSubmodule (Fin (Veronese.dupleN r d + 1)) k

/-- The ideal sheaf of the closed subscheme `Proj (k[y_I] / J_d) ⊆ ℙᴺ_k` cut out by the
homogeneous ideal `J_d` of the `d`-uple image of `X`. -/
def dupleImageIdealSheaf : QuasicoherentIdealSubsheaf (Proj 𝒮N) :=
  quasicoherentIdealSubsheafEquiv.symm (projQuotientι 𝒮N (dupleIdeal I d)).ker

omit [IsDomain (MvPolynomial (Fin (r + 1)) k ⧸ I.toIdeal)] in
/-- `J_d` is the homogeneous ideal `Γ_*(ℐ) ∩ k[y_I]` of the closed subscheme it defines: it is
saturated (Exercise 5.10). -/
theorem gammaStarIdeal_dupleImageIdealSheaf [IsDomain S] (hne : ∃ i, coord I i ≠ 0) :
    (gammaStarIdeal k (Veronese.dupleN r d) (dupleImageIdealSheaf I d)).toIdeal =
      (dupleIdeal I d).toIdeal := by
  rw [dupleImageIdealSheaf, gammaStarIdeal_ker_projQuotientι]
  exact le_antisymm (fun s hs => mem_dupleIdeal_of_pow_mul_mem I d hne s (mem_saturation.1 hs))
    (le_saturation _)

omit [IsDomain (MvPolynomial (Fin (r + 1)) k ⧸ I.toIdeal)] [NeZero d] in
/-- **Hartshorne II, Exercise 5.14(b,c).** Let `k` be algebraically closed and let
`X = Proj (S/I) ⊆ ℙʳ_k` be a connected normal closed subscheme, `S = k[x₀, …, xᵣ]`, `I` its
saturated homogeneous ideal. For all sufficiently large `d`, the image of `X` under the `d`-uple
embedding, the closed subscheme of `ℙᴺ_k` cut out by the kernel `J_d` of `y_I ↦ x^I`,
`k[y_I] → S/I`, is projectively normal: its homogeneous coordinate ring
`k[y_I] / J_d ≅ (S/I)^{(d)}` is an integrally closed domain. -/
theorem exists_isProjectivelyNormal_dupleImage [IsAlgClosed k]
    (hsat : ∀ s : MvPolynomial (Fin (r + 1)) k, (∀ i, ∃ n : ℕ, X i ^ n * s ∈ I.toIdeal) →
      s ∈ I.toIdeal)
    [ConnectedSpace (Proj 𝒬)] [Hartshorne.IsNormal (Proj 𝒬)] :
    ∃ d₀ : ℕ, 0 < d₀ ∧ ∀ (d : ℕ) [NeZero d], d₀ ≤ d →
      IsProjectivelyNormal (dupleImageIdealSheaf I d) := by
  obtain ⟨hdom, d₀, hd₀, hic⟩ := exists_isIntegrallyClosed_veroneseSubring I hsat
  refine ⟨d₀, hd₀, fun d _ hd => ?_⟩
  have := ProjectiveSectionRing.isIntegral_proj I
  obtain ⟨x⟩ : Nonempty (Proj 𝒬) := AlgebraicGeometry.IsIntegral.nonempty
  have := hic d hd
  let e := (Ideal.quotEquivOfEq (gammaStarIdeal_dupleImageIdealSheaf I d
    (exists_coord_ne_zero I x))).trans (dupleQuotientEquiv I d)
  exact ⟨e.injective.isDomain (e : _ →+* veroneseSubring 𝒬 d), IsIntegrallyClosed.of_equiv e.symm⟩

omit [IsDomain (MvPolynomial (Fin (r + 1)) k ⧸ I.toIdeal)] [NeZero d] in
/-- **Hartshorne II, Exercise 5.14(b,c), for a saturated homogeneous ideal.** Let `k` be
algebraically closed and let `X = Proj (S/I) ⊆ ℙʳ_k` be connected and normal, `S = k[x₀, …, xᵣ]`,
`I` saturated. For all sufficiently large `d`, the image of `X` under its `d`-uple embedding
(`projDupleEmbedding`, a closed immersion into `ℙᴺ_k`) is projectively normal. -/
theorem exists_isProjectivelyNormal_projDupleEmbedding_of_saturated [IsAlgClosed k]
    (hsat : ∀ s : MvPolynomial (Fin (r + 1)) k, (∀ i, ∃ n : ℕ, X i ^ n * s ∈ I.toIdeal) →
      s ∈ I.toIdeal)
    [ConnectedSpace (Proj 𝒬)] [Hartshorne.IsNormal (Proj 𝒬)] :
    ∃ d₀ : ℕ, 0 < d₀ ∧ ∀ (d : ℕ) [NeZero d], d₀ ≤ d →
      IsProjectivelyNormal (quasicoherentIdealSubsheafEquiv.symm (projDupleEmbedding I d).ker) := by
  obtain ⟨d₀, hd₀, h⟩ := exists_isProjectivelyNormal_dupleImage I hsat
  refine ⟨d₀, hd₀, fun d _ hd => ?_⟩
  rw [ker_projDupleEmbedding]
  exact h d hd

end DupleNormal

end ClosedSubscheme

/-! ### Closed subschemes of `ℙʳ_k` -/

section ClosedImmersion

open MvPolynomial ProjectiveClosedSubscheme ProjectiveNormality

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] {r : ℕ}

local notation "𝒮" => MvPolynomial.homogeneousSubmodule (Fin (r + 1)) k

/-- A scheme isomorphic to a normal scheme is normal. -/
private theorem isNormal_of_iso {X Y : Scheme.{u}} (e : Y ≅ X) [IsNormal X] : IsNormal Y where
  isDomain_stalk y :=
    (asIso (e.hom.stalkMap y)).symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  isIntegrallyClosed_stalk y :=
    IsIntegrallyClosed.of_equiv (asIso (e.hom.stalkMap y)).commRingCatIsoToRingEquiv

/-- **Hartshorne II, Exercise 5.14(b,c).** Let `k` be algebraically closed and let `X` be a
connected normal closed subscheme of `ℙʳ_k` (a closed immersion `f : X ⟶ ℙʳ_k`). Then for all
sufficiently large `d`, the image of `X` under the `d`-uple embedding `ρ_d : ℙʳ_k ⟶ ℙᴺ_k`
(`projDupleMap`), the closed subscheme of `ℙᴺ_k` with ideal sheaf `ker (f ≫ ρ_d)`, is
projectively normal.

Following the book: with `S(X) = S/I` the homogeneous coordinate ring of `X` (Corollary 5.16), the
image of `X` has homogeneous coordinate ring `S(X)^{(d)}` (`projDupleEmbedding_eq`,
`dupleQuotientEquiv`), and `S(X)^{(d)}` is integrally closed for large `d`
(`exists_isIntegrallyClosed_veroneseSubring`): `S(X)_n = Γ(X, 𝒪_X(n))` for large `n`
(Exercise 5.9) and `⨁_{n ≥ 0} Γ(X, 𝒪_X(n))` is the integral closure of `S(X)`
(Exercise 5.14(a)). -/
theorem exists_isProjectivelyNormal_image_projDupleMap [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Proj 𝒮) [IsClosedImmersion f] [ConnectedSpace X] [Hartshorne.IsNormal X] :
    ∃ d₀ : ℕ, 0 < d₀ ∧ ∀ (d : ℕ) [NeZero d], d₀ ≤ d →
      IsProjectivelyNormal (quasicoherentIdealSubsheafEquiv.symm (f ≫ projDupleMap d).ker) := by
  obtain ⟨e, he⟩ := exists_iso_projQuotientι_gammaStarIdeal f
  set I := gammaStarIdeal k r (quasicoherentIdealSubsheafEquiv.symm f.ker)
  have : ConnectedSpace (Proj (gradedQuotient 𝒮 I)) :=
    (Scheme.homeoOfIso e).surjective.connectedSpace (Scheme.homeoOfIso e).continuous
  have : Hartshorne.IsNormal (Proj (gradedQuotient 𝒮 I)) := isNormal_of_iso e.symm
  obtain ⟨d₀, hd₀, h⟩ := exists_isProjectivelyNormal_projDupleEmbedding_of_saturated I
    fun s hs => by
      rw [← saturation_gammaStarIdeal]
      exact mem_saturation.2 hs
  refine ⟨d₀, hd₀, fun d _ hd => ?_⟩
  rw [← he, Category.assoc, Scheme.Hom.ker_comp_of_isIso, projQuotientι_comp_projDupleMap]
  exact h d hd

end ClosedImmersion

end ProjectivelyNormalVeronese

end Hartshorne

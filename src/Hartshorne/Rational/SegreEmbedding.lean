/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Projective.Correspondence

/-!
# The Segre embedding

Hartshorne, *Algebraic Geometry*, I.2, Exercise 2.14 (p. 13).

The Segre map sends a pair of projective points with coordinate vectors `x`
and `y` to the projective class of the rank-one matrix `(xᵢ yⱼ)`.  Its image
is the projective zero set of the kernel of the substitution
`zᵢⱼ ↦ xᵢ yⱼ`; this kernel is homogeneous and prime, so the image is a
projective variety.

## Main results

* `Hartshorne.segreEmbedding_injective`
* `Hartshorne.range_segreEmbedding`
* `Hartshorne.isProjVariety_range_segreEmbedding`
-/

namespace Hartshorne

open MvPolynomial
open scoped Hartshorne

universe u

variable {k : Type u} [Field k] {σ τ : Type*}

/-- The rank-one matrix associated to two coordinate vectors. -/
def segreVector (x : σ → k) (y : τ → k) : σ × τ → k :=
  fun ij => x ij.1 * y ij.2

theorem segreVector_ne_zero {x : σ → k} {y : τ → k}
    (hx : x ≠ 0) (hy : y ≠ 0) : segreVector x y ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hy
  intro h
  have hij := congrFun h (i, j)
  simp only [segreVector, Pi.zero_apply] at hij
  rcases mul_eq_zero.mp hij with hi0 | hj0
  · exact hi hi0
  · exact hj hj0

/-- The Segre map on projective points. -/
noncomputable def segreMap
    (P : ProjectiveSpace k σ) (Q : ProjectiveSpace k τ) :
    ProjectiveSpace k (σ × τ) :=
  Projectivization.mk k (segreVector P.rep Q.rep)
    (segreVector_ne_zero P.rep_nonzero Q.rep_nonzero)

/-- The representative formula, which also states that the construction is
independent of the chosen homogeneous coordinates. -/
theorem segreMap_mk_mk {x : σ → k} {y : τ → k}
    (hx : x ≠ 0) (hy : y ≠ 0) :
    segreMap (Projectivization.mk k x hx) (Projectivization.mk k y hy) =
      Projectivization.mk k (segreVector x y) (segreVector_ne_zero hx hy) := by
  unfold segreMap
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep k x hx
  obtain ⟨b, hb⟩ := Projectivization.exists_smul_eq_mk_rep k y hy
  refine (Projectivization.mk_eq_mk_iff k _ _ _ _).2 ⟨a * b, ?_⟩
  funext ij
  have hax := congrFun ha ij.1
  have hby := congrFun hb ij.2
  simp only [Pi.smul_apply, Units.smul_def, smul_eq_mul] at hax hby ⊢
  simp only [segreVector]
  rw [← hax, ← hby]
  simp only [Units.val_mul]
  ring

/-- Equality after applying the Segre map recovers both projective factors. -/
theorem segreMap_eq_iff {P P' : ProjectiveSpace k σ}
    {Q Q' : ProjectiveSpace k τ} :
    segreMap P Q = segreMap P' Q' ↔ P = P' ∧ Q = Q' := by
  constructor
  · intro h
    have hmk : Projectivization.mk k (segreVector P.rep Q.rep)
          (segreVector_ne_zero P.rep_nonzero Q.rep_nonzero) =
        Projectivization.mk k (segreVector P'.rep Q'.rep)
          (segreVector_ne_zero P'.rep_nonzero Q'.rep_nonzero) := h
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff k _ _ _ _).1 hmk
    obtain ⟨i, hi⟩ := Function.ne_iff.mp P.rep_nonzero
    obtain ⟨j, hj⟩ := Function.ne_iff.mp Q.rep_nonzero
    have hcij := congrFun hc (i, j)
    simp only [Pi.smul_apply, Units.smul_def, smul_eq_mul, segreVector] at hcij
    have hc0 : (c : k) ≠ 0 := Units.ne_zero c
    have hi' : P'.rep i ≠ 0 := by
      intro hi'
      rw [hi', zero_mul] at hcij
      exact (mul_ne_zero hi hj) (by simpa using hcij.symm)
    have hj' : Q'.rep j ≠ 0 := by
      intro hj'
      rw [hj', mul_zero] at hcij
      exact (mul_ne_zero hi hj) (by simpa using hcij.symm)
    have hP : P = P' := by
      let a : k := (c : k) * Q'.rep j / Q.rep j
      have ha0 : a ≠ 0 := div_ne_zero (mul_ne_zero hc0 hj') hj
      have hasmul : a • P'.rep = P.rep := by
        funext l
        have hcl := congrFun hc (l, j)
        simp only [Pi.smul_apply, Units.smul_def, smul_eq_mul, segreVector] at hcl ⊢
        show a * P'.rep l = P.rep l
        dsimp [a]
        rw [div_mul_eq_mul_div, div_eq_iff hj]
        linear_combination hcl
      have := (Projectivization.mk_eq_mk_iff k _ _ P.rep_nonzero P'.rep_nonzero).2
        ⟨Units.mk0 a ha0, hasmul⟩
      simpa only [P.mk_rep, P'.mk_rep] using this
    have hQ : Q = Q' := by
      let b : k := (c : k) * P'.rep i / P.rep i
      have hb0 : b ≠ 0 := div_ne_zero (mul_ne_zero hc0 hi') hi
      have hbsmul : b • Q'.rep = Q.rep := by
        funext l
        have hcl := congrFun hc (i, l)
        simp only [Pi.smul_apply, Units.smul_def, smul_eq_mul, segreVector] at hcl ⊢
        show b * Q'.rep l = Q.rep l
        dsimp [b]
        rw [div_mul_eq_mul_div, div_eq_iff hi]
        linear_combination hcl
      have := (Projectivization.mk_eq_mk_iff k _ _ Q.rep_nonzero Q'.rep_nonzero).2
        ⟨Units.mk0 b hb0, hbsmul⟩
      simpa only [Q.mk_rep, Q'.mk_rep] using this
    exact ⟨hP, hQ⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The Segre map as a function on the product. -/
noncomputable def segreEmbedding :
    ProjectiveSpace k σ × ProjectiveSpace k τ → ProjectiveSpace k (σ × τ) :=
  fun PQ => segreMap PQ.1 PQ.2

theorem segreEmbedding_injective :
    Function.Injective (segreEmbedding (k := k) (σ := σ) (τ := τ)) := by
  intro PQ PQ' h
  obtain ⟨hP, hQ⟩ := segreMap_eq_iff.mp h
  exact Prod.ext hP hQ

/-- The polynomial substitution `z_(i,j) ↦ x_i y_j`. -/
noncomputable def segreRingHom :
    MvPolynomial (σ × τ) k →ₐ[k] MvPolynomial (Sum σ τ) k :=
  MvPolynomial.aeval fun ij => X (Sum.inl ij.1) * X (Sum.inr ij.2)

/-- The ideal of polynomial relations among rank-one matrices. -/
noncomputable def segreIdeal : Ideal (MvPolynomial (σ × τ) k) :=
  RingHom.ker (segreRingHom (k := k) (σ := σ) (τ := τ)).toRingHom

/-- A `2 × 2` minor of the generic matrix. -/
noncomputable def segreMinor (i l : σ) (j m : τ) : MvPolynomial (σ × τ) k :=
  X (i, j) * X (l, m) - X (i, m) * X (l, j)

theorem segreMinor_isHomogeneous (i l : σ) (j m : τ) :
    (segreMinor (k := k) i l j m).IsHomogeneous 2 := by
  exact ((isHomogeneous_X k (i, j)).mul (isHomogeneous_X k (l, m))).sub
    ((isHomogeneous_X k (i, m)).mul (isHomogeneous_X k (l, j)))

theorem segreMinor_mem_ideal (i l : σ) (j m : τ) :
    segreMinor (k := k) i l j m ∈ segreIdeal (k := k) (σ := σ) (τ := τ) := by
  simp [segreIdeal, segreRingHom, segreMinor]
  ring

theorem segreIdeal_isPrime :
    (segreIdeal (k := k) (σ := σ) (τ := τ)).IsPrime := by
  exact RingHom.ker_isPrime _

theorem segreRingHom_isHomogeneous {f : MvPolynomial (σ × τ) k} {n : ℕ}
    (hf : f.IsHomogeneous n) :
    (segreRingHom (k := k) (σ := σ) (τ := τ) f).IsHomogeneous (2 * n) := by
  apply hf.aeval
  intro ij
  simpa using (isHomogeneous_X k (Sum.inl ij.1)).mul
    (isHomogeneous_X k (Sum.inr ij.2))

theorem homogeneousComponent_mem_segreIdeal
    {f : MvPolynomial (σ × τ) k}
    (hf : f ∈ segreIdeal (k := k) (σ := σ) (τ := τ)) (n : ℕ) :
    homogeneousComponent n f ∈ segreIdeal (k := k) (σ := σ) (τ := τ) := by
  change segreRingHom (k := k) (σ := σ) (τ := τ) f = 0 at hf
  change segreRingHom (k := k) (σ := σ) (τ := τ)
      (homogeneousComponent n f) = 0
  by_cases hn : n ∈ Finset.range (f.totalDegree + 1)
  · have hsum :
        ∑ m ∈ Finset.range (f.totalDegree + 1),
            segreRingHom (k := k) (σ := σ) (τ := τ)
              (homogeneousComponent m f) = 0 := by
      rw [← map_sum, sum_homogeneousComponent, hf]
    have hcomp := congrArg
      (homogeneousComponent (2 * n) :
        MvPolynomial (Sum σ τ) k → MvPolynomial (Sum σ τ) k) hsum
    simp only [map_zero] at hcomp
    have hpiece (m : ℕ) :
        homogeneousComponent (2 * n)
            (segreRingHom (k := k) (σ := σ) (τ := τ)
              (homogeneousComponent m f)) =
          if n = m then
            segreRingHom (k := k) (σ := σ) (τ := τ)
              (homogeneousComponent m f)
          else 0 := by
      rw [homogeneousComponent_of_mem
        (segreRingHom_isHomogeneous (homogeneousComponent_isHomogeneous m f))]
      by_cases hnm : n = m
      · subst m
        simp
      · have htwice : 2 * n ≠ 2 * m := by omega
        simp [hnm, htwice]
    simp_rw [map_sum, hpiece] at hcomp
    simpa [hn] using hcomp
  · have hlt : f.totalDegree < n := by
      simpa [Finset.mem_range] using hn
    rw [homogeneousComponent_eq_zero n f hlt, map_zero]

theorem segreIdeal_isHomogeneous :
    IsHomogeneousIdeal (segreIdeal (k := k) (σ := σ) (τ := τ)) := by
  intro n f hf
  change (MvPolynomial.decomposition.decompose' f n :
    MvPolynomial (σ × τ) k) ∈ segreIdeal
  rw [MvPolynomial.decomposition.decompose'_apply]
  exact homogeneousComponent_mem_segreIdeal (k := k) (σ := σ) (τ := τ) hf n

theorem eval_segreVector_eq_eval_segreRingHom
    (x : σ → k) (y : τ → k) (f : MvPolynomial (σ × τ) k) :
    eval (segreVector x y) f =
      eval (Sum.elim x y)
        (segreRingHom (k := k) (σ := σ) (τ := τ) f) := by
  rw [segreRingHom, aeval_def, eval_eval₂]
  simp only [eval_mul, eval_X, Sum.elim_inl, Sum.elim_inr]
  have hc : (eval (Sum.elim x y)).comp
      (algebraMap k (MvPolynomial (Sum σ τ) k)) = RingHom.id k := by
    ext c
    simp
  rw [hc, eval₂_id]
  rfl

theorem segreMap_mem_projZeroSet_ideal
    (P : ProjectiveSpace k σ) (Q : ProjectiveSpace k τ) :
    segreMap P Q ∈
      projZeroSet (segreIdeal (k := k) (σ := σ) (τ := τ) :
        Set (MvPolynomial (σ × τ) k)) := by
  intro f hf
  change eval (segreMap P Q).rep f = 0
  rw [← sum_homogeneousComponent f, map_sum]
  apply Finset.sum_eq_zero
  intro n hn
  have hnker := homogeneousComponent_mem_segreIdeal
    (k := k) (σ := σ) (τ := τ) hf n
  have heval : eval (segreVector P.rep Q.rep)
      (homogeneousComponent n f) = 0 := by
    rw [eval_segreVector_eq_eval_segreRingHom]
    change segreRingHom (k := k) (σ := σ) (τ := τ)
      (homogeneousComponent n f) = 0 at hnker
    rw [hnker]
    simp
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep k
    (segreVector P.rep Q.rep)
    (segreVector_ne_zero P.rep_nonzero Q.rep_nonzero)
  unfold segreMap
  rw [← ha]
  change eval ((a : k) • segreVector P.rep Q.rep) (homogeneousComponent n f) = 0
  rw [(homogeneousComponent_isHomogeneous n f).eval_smul, heval, mul_zero]

/-- A nonzero matrix whose `2 × 2` minors vanish is a rank-one matrix. -/
theorem exists_segreVector_eq_of_minors {z : σ × τ → k} (hz : z ≠ 0)
    (hminor : ∀ i l j m,
      z (i, j) * z (l, m) - z (i, m) * z (l, j) = 0) :
    ∃ (x : σ → k) (y : τ → k),
      x ≠ 0 ∧ y ≠ 0 ∧ segreVector x y = z := by
  obtain ⟨⟨i, j⟩, hij⟩ := Function.ne_iff.mp hz
  have hij0 : z (i, j) ≠ 0 := by simpa using hij
  let x : σ → k := fun l => z (l, j)
  let y : τ → k := fun m => z (i, m) / z (i, j)
  have hx : x ≠ 0 := by
    apply Function.ne_iff.mpr
    exact ⟨i, hij⟩
  have hy : y ≠ 0 := by
    apply Function.ne_iff.mpr
    refine ⟨j, ?_⟩
    simp [y, hij0]
  refine ⟨x, y, hx, hy, funext fun lm => ?_⟩
  rcases lm with ⟨l, m⟩
  have h := hminor l i j m
  simp only [segreVector, x, y]
  rw [← mul_div_assoc, div_eq_iff hij0]
  exact sub_eq_zero.mp h

/-- The image is exactly the zero set of the kernel of the Segre substitution. -/
theorem range_segreEmbedding :
    Set.range (segreEmbedding (k := k) (σ := σ) (τ := τ)) =
      projZeroSet (segreIdeal (k := k) (σ := σ) (τ := τ) :
        Set (MvPolynomial (σ × τ) k)) := by
  apply Set.Subset.antisymm
  · rintro R ⟨⟨P, Q⟩, rfl⟩
    exact segreMap_mem_projZeroSet_ideal P Q
  · intro R hR
    have hminor : ∀ i l j m,
        R.rep (i, j) * R.rep (l, m) - R.rep (i, m) * R.rep (l, j) = 0 := by
      intro i l j m
      have h := hR (segreMinor (k := k) i l j m)
        (segreMinor_mem_ideal (k := k) i l j m)
      simpa [HomogeneousVanish, segreMinor] using h
    obtain ⟨x, y, hx, hy, hxy⟩ :=
      exists_segreVector_eq_of_minors R.rep_nonzero hminor
    refine ⟨(Projectivization.mk k x hx, Projectivization.mk k y hy), ?_⟩
    change segreMap (Projectivization.mk k x hx) (Projectivization.mk k y hy) = R
    rw [segreMap_mk_mk hx hy]
    have hmk : Projectivization.mk k (segreVector x y) (segreVector_ne_zero hx hy) =
        Projectivization.mk k R.rep R.rep_nonzero := by
      refine (Projectivization.mk_eq_mk_iff k _ _ _ _).2 ⟨1, ?_⟩
      simp [hxy]
    exact hmk.trans R.mk_rep

/-- The projective zero set of the Segre kernel is algebraic. -/
theorem isProjAlgebraicSet_projZeroSet_segreIdeal :
    IsProjAlgebraicSet
      (projZeroSet (segreIdeal (k := k) (σ := σ) (τ := τ) :
        Set (MvPolynomial (σ × τ) k))) := by
  let T : Set (MvPolynomial (σ × τ) k) :=
    {f | f ∈ segreIdeal (k := k) (σ := σ) (τ := τ) ∧
      ∃ n, f.IsHomogeneous n}
  refine ⟨T, ?_, ?_⟩
  · intro f hf
    exact hf.2
  · ext P
    constructor
    · intro hP f hf
      exact hP f hf.1
    · intro hP f hf
      change eval P.rep f = 0
      rw [← sum_homogeneousComponent f, map_sum]
      apply Finset.sum_eq_zero
      intro n hn
      exact hP (homogeneousComponent n f)
        ⟨homogeneousComponent_mem_segreIdeal hf n,
          n, homogeneousComponent_isHomogeneous n f⟩

/-- The Segre image is a projective variety. -/
theorem isProjVariety_range_segreEmbedding [IsAlgClosed k]
    [Finite σ] [Finite τ] [Nonempty σ] [Nonempty τ] :
    IsProjVariety (Set.range (segreEmbedding (k := k) (σ := σ) (τ := τ))) := by
  rw [range_segreEmbedding]
  let I := segreIdeal (k := k) (σ := σ) (τ := τ)
  have hAlg : IsProjAlgebraicSet
      (projZeroSet (I : Set (MvPolynomial (σ × τ) k))) :=
    isProjAlgebraicSet_projZeroSet_segreIdeal
  have hne : (projZeroSet (I : Set (MvPolynomial (σ × τ) k))).Nonempty := by
    rw [← range_segreEmbedding]
    exact Set.range_nonempty _
  have hJ : homogeneousVanishingIdeal
      (projZeroSet (I : Set (MvPolynomial (σ × τ) k))) = I := by
    rw [homogeneousVanishingIdeal_projZeroSet segreIdeal_isHomogeneous hne]
    exact segreIdeal_isPrime.radical
  refine ⟨?_, isClosed_iff_isProjAlgebraicSet.2 hAlg⟩
  rw [isIrreducible_iff_isPrime_homogeneousVanishingIdeal hAlg, hJ]
  exact segreIdeal_isPrime

/-- **Exercise 2.14.** The Segre coordinate formula is well defined, the
resulting map is injective, and its image is the projective variety cut out by
the kernel of `z_(i,j) ↦ x_i y_j`. -/
theorem segre_embedding [IsAlgClosed k]
    [Finite σ] [Finite τ] [Nonempty σ] [Nonempty τ] :
    (∀ (x : σ → k) (y : τ → k) (hx : x ≠ 0) (hy : y ≠ 0),
      segreMap (Projectivization.mk k x hx) (Projectivization.mk k y hy) =
        Projectivization.mk k (segreVector x y) (segreVector_ne_zero hx hy)) ∧
    Function.Injective (segreEmbedding (k := k) (σ := σ) (τ := τ)) ∧
    Set.range (segreEmbedding (k := k) (σ := σ) (τ := τ)) =
      projZeroSet (segreIdeal (k := k) (σ := σ) (τ := τ) :
        Set (MvPolynomial (σ × τ) k)) ∧
    IsProjVariety (Set.range (segreEmbedding (k := k) (σ := σ) (τ := τ))) := by
  exact ⟨fun _ _ hx hy => segreMap_mk_mk hx hy,
    segreEmbedding_injective, range_segreEmbedding,
    isProjVariety_range_segreEmbedding⟩

end Hartshorne

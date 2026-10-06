/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-!
# Determinants under a scaled perfect pairing

Hartshorne, *Algebraic Geometry*, Appendix C, Lemma 4.3 (p. 456).
-/

namespace Hartshorne

noncomputable section

open Module Polynomial

universe u v w

private lemma eval₂_reverse_matrix_charpoly
    {K : Type u} [Field K] {ι : Type w} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K)
    {L : Type*} [CommRing L] (i : K →+* L) (x : L) :
    eval₂ i x M.charpoly.reverse = Matrix.det (1 - x • M.map i) := by
  rw [Matrix.reverse_charpoly]
  change (eval₂RingHom i x) (Matrix.det _) = _
  rw [RingHom.map_det]
  congr 1
  ext a c
  by_cases h : a = c <;> simp [h] <;> ring

private lemma eval₂_reverse_charpoly
    {K : Type u} [Field K]
    {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (f : Module.End K V)
    {L : Type*} [CommRing L] (i : K →+* L) (x : L) :
    eval₂ i x f.charpoly.reverse =
      Matrix.det (1 - x • (LinearMap.toMatrix b b f).map i) := by
  rw [← LinearMap.charpoly_toMatrix f b]
  exact eval₂_reverse_matrix_charpoly _ _ _

private lemma scaled_inv_transpose_reverse_charpoly
    {K : Type u} [Field K] {ι : Type w} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K) (A : K) (hM : IsUnit M.det) (hA : A ≠ 0) :
    eval₂ (algebraMap K (RatFunc K)) RatFunc.X
        (A • (M⁻¹).transpose).charpoly.reverse =
      ((-1 : RatFunc K) ^ Fintype.card ι *
          (algebraMap K (RatFunc K) A) ^ Fintype.card ι *
          RatFunc.X ^ Fintype.card ι /
          algebraMap K (RatFunc K) M.det) *
        eval₂ (algebraMap K (RatFunc K))
          ((algebraMap K (RatFunc K) A * RatFunc.X)⁻¹)
          M.charpoly.reverse := by
  rw [eval₂_reverse_matrix_charpoly, eval₂_reverse_matrix_charpoly]
  let c : K →+* RatFunc K := algebraMap K (RatFunc K)
  let D : Matrix ι ι (RatFunc K) := M.map c
  let z : RatFunc K := c A * RatFunc.X
  have hcA : c A ≠ 0 := by
    simpa only [map_zero] using c.injective.ne hA
  have hz : z ≠ 0 := mul_ne_zero hcA RatFunc.X_ne_zero
  have hmap_inv : (M⁻¹).map c = D⁻¹ := by
    symm
    apply Matrix.inv_eq_right_inv
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv M hM]
    simp
  have hleft : (A • (M⁻¹).transpose).map c = c A • D.transpose⁻¹ := by
    calc
      _ = c A • ((M⁻¹).transpose.map c) := by ext; simp
      _ = c A • ((M⁻¹).map c).transpose := by rw [Matrix.transpose_map]
      _ = c A • (D⁻¹).transpose := by rw [hmap_inv]
      _ = c A • D.transpose⁻¹ := by rw [Matrix.transpose_nonsing_inv]
  rw [show algebraMap K (RatFunc K) = c from rfl, hleft]
  rw [smul_smul, mul_comm RatFunc.X (c A)]
  change (1 - z • D.transpose⁻¹).det =
    (-1) ^ Fintype.card ι * (c A) ^ Fintype.card ι *
        RatFunc.X ^ Fintype.card ι / c M.det *
      (1 - z⁻¹ • D).det
  have hDdet : IsUnit D.det := by
    rw [show D.det = c M.det by exact (c.map_det M).symm]
    exact hM.map c
  have hE : IsUnit D.transpose.det := by
    rwa [Matrix.det_transpose]
  have hfactor :
      1 - z • D.transpose⁻¹ =
        ((-z) • D.transpose⁻¹) * (1 - z⁻¹ • D.transpose) := by
    rw [mul_sub, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.nonsing_inv_mul _ hE]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [hz]
      ring
    · simp [hij, hz]
  rw [hfactor, Matrix.det_mul, Matrix.det_smul, Matrix.det_nonsing_inv,
    Matrix.det_transpose]
  have hdet_transpose :
      (1 - z⁻¹ • D.transpose).det = (1 - z⁻¹ • D).det := by
    calc
      _ = (1 - z⁻¹ • D).transpose.det := by
        congr 1
        ext i j
        by_cases hij : i = j
        · subst j
          simp
        · have hji : j ≠ i := Ne.symm hij
          simp [hij, hji]
      _ = _ := Matrix.det_transpose _
  rw [hdet_transpose, show D.det = c M.det by exact (c.map_det M).symm]
  simp only [div_eq_mul_inv]
  rw [Ring.inverse_eq_inv, neg_pow, mul_pow (c A) RatFunc.X]
  ring

/-- **Hartshorne Appendix C, Lemma 4.3.** Endomorphisms paired up to a
nonzero scalar by a perfect pairing are invertible. Their determinants and
reciprocal characteristic-determinant polynomials satisfy the displayed
functional-equation identities. -/
theorem scaledPerfectPairing_determinantIdentity
    {K : Type u} [Field K]
    {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {W : Type w} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (r : ℕ) (p : V →ₗ[K] W →ₗ[K] K) [p.IsPerfPair]
    (φ : Module.End K V) (ψ : Module.End K W) (A : K)
    (hV : finrank K V = r) (hW : finrank K W = r) (hA : A ≠ 0)
    (hpair : ∀ v w, p (φ v) (ψ w) = A * p v w) :
    Function.Bijective φ ∧
      Function.Bijective ψ ∧
      LinearMap.det ψ = A ^ r / LinearMap.det φ ∧
      eval₂ (algebraMap K (RatFunc K)) RatFunc.X ψ.charpoly.reverse =
        ((-1 : RatFunc K) ^ r *
            (algebraMap K (RatFunc K) A) ^ r * RatFunc.X ^ r /
            algebraMap K (RatFunc K) (LinearMap.det φ)) *
          eval₂ (algebraMap K (RatFunc K))
            ((algebraMap K (RatFunc K) A * RatFunc.X)⁻¹)
            φ.charpoly.reverse := by
  have hφinj : Function.Injective φ := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply (LinearMap.IsPerfPair.bijective_left p).injective
    ext w
    have h := hpair (x - y) w
    simp only [map_sub, hxy, sub_self, map_zero, LinearMap.zero_apply] at h
    have hz := (mul_eq_zero.mp h.symm).resolve_left hA
    simpa using hz
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply (LinearMap.IsPerfPair.bijective_right p).injective
    ext v
    have h := hpair v (x - y)
    simp only [map_sub, hxy, sub_self, map_zero] at h
    have hz := (mul_eq_zero.mp h.symm).resolve_left hA
    simpa using hz
  have hφ : Function.Bijective φ :=
    ⟨hφinj, LinearMap.injective_iff_surjective.mp hφinj⟩
  have hψ : Function.Bijective ψ :=
    ⟨hψinj, LinearMap.injective_iff_surjective.mp hψinj⟩
  let Φ : V ≃ₗ[K] V := LinearEquiv.ofBijective φ hφ
  let e : W ≃ₗ[K] Module.Dual K V := p.flip.toPerfPair
  have hconj : e.conj ψ = A • Φ.symm.toLinearMap.dualMap := by
    ext f v
    change p v (ψ (e.symm f)) = A * f (Φ.symm v)
    simpa [Φ, e] using hpair (Φ.symm v) (e.symm f)
  have hdet : LinearMap.det ψ = A ^ r / LinearMap.det φ := by
    calc
      LinearMap.det ψ = LinearMap.det (e.conj ψ) := by
        rw [LinearEquiv.conj_apply]
        exact (LinearMap.det_conj ψ e).symm
      _ = LinearMap.det (A • Φ.symm.toLinearMap.dualMap) := congrArg LinearMap.det hconj
      _ = A ^ r * LinearMap.det Φ.symm.toLinearMap.dualMap := by
        rw [LinearMap.det_smul, ← e.finrank_eq, hW]
      _ = A ^ r * LinearMap.det Φ.symm.toLinearMap := by
        rw [LinearMap.det_dualMap]
      _ = A ^ r * (LinearMap.det φ)⁻¹ := by
        rw [LinearEquiv.det_coe_symm]
        rfl
      _ = A ^ r / LinearMap.det φ := by rw [div_eq_mul_inv]
  refine ⟨hφ, hψ, hdet, ?_⟩
  let b := Module.Free.chooseBasis K V
  let M := LinearMap.toMatrix b b φ
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex K V) = r := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, hV]
  have hMinv : LinearMap.toMatrix b b Φ.symm.toLinearMap = M⁻¹ := by
    symm
    apply Matrix.inv_eq_right_inv
    rw [← LinearMap.toMatrix_comp]
    have hcomp : φ.comp Φ.symm.toLinearMap = LinearMap.id := by
      ext x
      exact Φ.apply_symm_apply x
    rw [hcomp, LinearMap.toMatrix_id]
  have hmatrix :
      LinearMap.toMatrix b.dualBasis b.dualBasis
          (A • Φ.symm.toLinearMap.dualMap) =
        A • (M⁻¹).transpose := by
    rw [map_smul, LinearMap.dualMap_def, LinearMap.toMatrix_transpose, hMinv]
  rw [← e.charpoly_conj ψ, hconj,
    ← LinearMap.charpoly_toMatrix (A • Φ.symm.toLinearMap.dualMap) b.dualBasis,
    hmatrix]
  have hMdet : IsUnit M.det := by
    rw [LinearMap.det_toMatrix]
    exact Φ.isUnit_det'
  have hformula := scaled_inv_transpose_reverse_charpoly M A hMdet hA
  rw [LinearMap.det_toMatrix b φ, LinearMap.charpoly_toMatrix φ b] at hformula
  simpa only [hcard] using hformula

end

end Hartshorne

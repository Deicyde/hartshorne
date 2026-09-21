/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Nonsingular.DeterminantalLocus
import Hartshorne.Nonsingular.IntrinsicNonsingular
import Hartshorne.Nonsingular.JacobianRankBound

/-!
# The affine singular locus is closed

Hartshorne, *Algebraic Geometry*, I.5, proof of Theorem 5.3 (p. 33).

For an affine variety of dimension `r`, a point is singular exactly when the
Jacobian matrix of any finite generating family has rank less than the
codimension.  Thus the singular locus is the preimage of a determinantal
rank-drop locus and is closed.  In the ambient affine space it is cut out by
the vanishing ideal together with the relevant Jacobian minors.
-/

namespace Hartshorne

open MvPolynomial

universe u v w

variable {k : Type u} [Field k] {σ : Type v} {Y : Set (σ → k)}

/-- The polynomial Jacobian matrix before evaluation at a point. -/
noncomputable def jacobianPolynomialMatrix {ι : Type w}
    (f : ι → MvPolynomial σ k) : Matrix ι σ (MvPolynomial σ k) :=
  fun i j => pderiv j (f i)

@[simp]
theorem jacobianPolynomialMatrix_map_eval {ι : Type w}
    (P : σ → k) (f : ι → MvPolynomial σ k) :
    (jacobianPolynomialMatrix f).map (MvPolynomial.eval P) =
      jacobianMatrix P f := by
  rfl

variable [IsAlgClosed k] [Finite σ]

/-- For fixed defining equations, the intrinsic singular locus is the
preimage of their determinantal rank-drop locus. -/
theorem affineSingularLocus_eq_preimage_matrixRankDropLocus
    [Fintype σ] (hY : IsAffineVariety Y) {ι : Type w} [Fintype ι]
    (f : ι → MvPolynomial σ k)
    (hf : Ideal.span (Set.range f) = vanishingIdeal k Y)
    {r : ℕ} (hdim : dim Y = (r : WithBot ℕ∞)) :
    Variety.SingularLocus
        (Variety.ofQuasiAffine hY.isQuasiAffineVariety) =
      Subtype.val ⁻¹'
        matrixRankDropLocus (jacobianPolynomialMatrix f) (Nat.card σ - r) := by
  classical
  ext P
  simp only [Variety.SingularLocus, Set.mem_ofPred_eq]
  rw [nonsingularAt_affine_iff hY P,
    not_isAffineNonsingularAt_iff_jacobianRank_lt hY
      (affinePoint hY.isQuasiAffineVariety P) hdim,
    ← jacobianMatrix_rank_eq_jacobianRank
      (affinePoint hY.isQuasiAffineVariety P) f hf]
  rfl

/-- The intrinsic singular locus of an affine variety of a specified dimension
is closed. -/
theorem isClosed_affineSingularLocus_of_dim_eq
    (hY : IsAffineVariety Y) {r : ℕ}
    (hdim : dim Y = (r : WithBot ℕ∞)) :
    IsClosed (Variety.SingularLocus
      (Variety.ofQuasiAffine hY.isQuasiAffineVariety)) := by
  classical
  let _ : Fintype σ := Fintype.ofFinite σ
  obtain ⟨n, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (vanishingIdeal k Y))
  rw [affineSingularLocus_eq_preimage_matrixRankDropLocus hY f hf hdim]
  exact (isClosed_matrixRankDropLocus (jacobianPolynomialMatrix f)
    (Nat.card σ - r)).preimage continuous_subtype_val

/-- The intrinsic singular locus of an affine variety is closed. -/
theorem isClosed_affineSingularLocus (hY : IsAffineVariety Y) :
    IsClosed (Variety.SingularLocus
      (Variety.ofQuasiAffine hY.isQuasiAffineVariety)) := by
  obtain ⟨r, hdim⟩ := hY.exists_dim_eq_natCast
  exact isClosed_affineSingularLocus_of_dim_eq hY hdim

/-- In ambient affine space, any finite generating family cuts out the affine
singular locus using the defining ideal and the relevant Jacobian minors. -/
theorem image_affineSingularLocus_eq_zeroSet_jacobianMinors
    [Fintype σ] (hY : IsAffineVariety Y) {ι : Type w} [Fintype ι]
    (f : ι → MvPolynomial σ k)
    (hf : Ideal.span (Set.range f) = vanishingIdeal k Y)
    {r : ℕ} (hdim : dim Y = (r : WithBot ℕ∞)) :
    Subtype.val '' Variety.SingularLocus
        (Variety.ofQuasiAffine hY.isQuasiAffineVariety) =
      zeroSet ((vanishingIdeal k Y : Set (MvPolynomial σ k)) ∪
        determinantalMinors (jacobianPolynomialMatrix f) (Nat.card σ - r)) := by
  classical
  rw [affineSingularLocus_eq_preimage_matrixRankDropLocus hY f hf hdim,
    matrixRankDropLocus_eq_zeroSet]
  ext P
  simp only [Set.mem_image, Set.mem_preimage, mem_zeroSet_iff, Set.mem_union]
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    intro g hg
    rcases hg with hg | hg
    · exact hg Q.1 Q.2
    · exact hQ g hg
  · intro hP
    have hPY : P ∈ Y := by
      rw [← hY.isAlgebraicSet.zeroLocus_vanishingIdeal]
      exact fun g hg => hP g (Or.inl hg)
    refine ⟨⟨P, hPY⟩, ?_, rfl⟩
    exact fun g hg => hP g (Or.inr hg)

/-- There is a finite family of defining equations whose Jacobian minors,
together with the defining ideal, cut out the affine singular locus. -/
theorem exists_generators_image_affineSingularLocus_eq_zeroSet
    (hY : IsAffineVariety Y) {r : ℕ}
    (hdim : dim Y = (r : WithBot ℕ∞)) :
    ∃ (n : ℕ) (f : Fin n → MvPolynomial σ k),
      Ideal.span (Set.range f) = vanishingIdeal k Y ∧
      Subtype.val '' Variety.SingularLocus
          (Variety.ofQuasiAffine hY.isQuasiAffineVariety) =
        zeroSet ((vanishingIdeal k Y : Set (MvPolynomial σ k)) ∪
          determinantalMinors (jacobianPolynomialMatrix f) (Nat.card σ - r)) := by
  classical
  let _ : Fintype σ := Fintype.ofFinite σ
  obtain ⟨n, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (vanishingIdeal k Y))
  exact ⟨n, f, hf,
    image_affineSingularLocus_eq_zeroSet_jacobianMinors hY f hf hdim⟩

end Hartshorne

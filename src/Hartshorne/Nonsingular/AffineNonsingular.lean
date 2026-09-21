/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Affine.DimensionCoordinateRing
import Hartshorne.Dimension.FgAlgebra
import Hartshorne.Nonsingular.JacobianRank

/-!
# Nonsingular points of an affine variety

Hartshorne, *Algebraic Geometry*, I.5 (pp. 31–32).

A point of an affine variety of dimension `r` in affine `n`-space is
nonsingular when its intrinsic Jacobian rank is `n - r`.  Since dimensions in
this development take values in `WithBot ℕ∞`, the definition below records the
equivalent subtraction-free equality `jacobianRank Y P + r = n` together with
the natural-number witness for `dim Y`.
-/

namespace Hartshorne

open MvPolynomial

universe u v w

variable {k : Type u} [Field k] {σ : Type v} [Finite σ]
  {Y : Set (σ → k)}

/-- A point is nonsingular in affine coordinates when the Jacobian rank plus
the dimension of the variety is the ambient dimension. -/
def IsAffineNonsingularAt (Y : Set (σ → k)) (P : Y) : Prop :=
  ∃ r : ℕ, dim Y = (r : WithBot ℕ∞) ∧ jacobianRank Y P + r = Nat.card σ

/-- An affine set is nonsingular in affine coordinates when all its points
are nonsingular. -/
def IsAffineNonsingular (Y : Set (σ → k)) : Prop :=
  ∀ P : Y, IsAffineNonsingularAt Y P

theorem isAffineNonsingularAt_iff_of_dim_eq (P : Y) {r : ℕ}
    (hdim : dim Y = (r : WithBot ℕ∞)) :
    IsAffineNonsingularAt Y P ↔ jacobianRank Y P + r = Nat.card σ := by
  constructor
  · rintro ⟨s, hs, hrank⟩
    have hsr : s = r := by
      exact_mod_cast hs.symm.trans hdim
    simpa [hsr] using hrank
  · exact fun hrank => ⟨r, hdim, hrank⟩

/-- A finite presentation of the vanishing ideal recovers Hartshorne's
matrix formulation of affine nonsingularity. -/
theorem isAffineNonsingularAt_iff_jacobianMatrix_rank [Fintype σ]
    {ι : Type w} [Finite ι] (P : Y) (f : ι → MvPolynomial σ k)
    (hf : Ideal.span (Set.range f) = vanishingIdeal k Y) :
    IsAffineNonsingularAt Y P ↔
      ∃ r : ℕ, dim Y = (r : WithBot ℕ∞) ∧
        (jacobianMatrix (P : σ → k) f).rank + r = Nat.card σ := by
  rw [IsAffineNonsingularAt, jacobianMatrix_rank_eq_jacobianRank P f hf]

/-- At a fixed natural-number dimension, affine nonsingularity is the
Jacobian rank equality at every point. -/
theorem isAffineNonsingular_iff_of_dim_eq {r : ℕ}
    (hdim : dim Y = (r : WithBot ℕ∞)) :
    IsAffineNonsingular Y ↔
      ∀ P : Y, jacobianRank Y P + r = Nat.card σ := by
  simp only [IsAffineNonsingular,
    isAffineNonsingularAt_iff_of_dim_eq _ hdim]

section AlgebraicallyClosed

variable [IsAlgClosed k]

/-- An affine variety in finite-dimensional affine space has a
natural-number-valued dimension. -/
theorem IsAffineVariety.exists_dim_eq_natCast (hY : IsAffineVariety Y) :
    ∃ r : ℕ, dim Y = (r : WithBot ℕ∞) := by
  let _ : Nontrivial (coordinateRing Y) :=
    Ideal.Quotient.nontrivial_iff.mpr
      (vanishingIdeal_ne_top hY.isIrreducible.nonempty)
  rw [dim_eq_ringKrullDim_coordinateRing hY.isAlgebraicSet]
  exact exists_ringKrullDim_eq_natCast k (coordinateRing Y)

end AlgebraicallyClosed

end Hartshorne

/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Nonsingular.CotangentDimension
import Hartshorne.Nonsingular.JacobianCriterion

/-!
# The Jacobian rank bound

Hartshorne, *Algebraic Geometry*, I.5, Proposition 5.2A and the proof of
Theorem 5.3 (p. 33).

The dimension of the cotangent space bounds the dimension of the local ring,
while the cotangent dimension plus the intrinsic Jacobian rank is the ambient
dimension.  Combining these statements bounds the Jacobian rank by the
codimension and identifies singularity with strict rank drop.
-/

namespace Hartshorne

universe u v

variable {k : Type u} [Field k] [IsAlgClosed k]
  {σ : Type v} [Finite σ] {Y : Set (σ → k)}

/-- The subtraction-free form of the Jacobian rank bound. -/
theorem jacobianRank_add_dim_le_ambient (hY : IsAffineVariety Y)
    (P : Y) {r : ℕ} (hdim : dim Y = (r : WithBot ℕ∞)) :
    jacobianRank Y P + r ≤ Nat.card σ := by
  let L := LocalRingAt hY.isIrreducible P
  let _ : IsNoetherianRing L := hY.isNoetherianRing_localRingAt P
  have hlocal := ringKrullDim_le_finrank_cotangentSpace L
  rw [ringKrullDim_localRingAt_eq_dim_finite hY P, hdim] at hlocal
  have hr : r ≤ Module.finrank (IsLocalRing.ResidueField L)
      (IsLocalRing.CotangentSpace L) := by
    exact_mod_cast hlocal
  have hsum :
      Module.finrank (IsLocalRing.ResidueField L)
          (IsLocalRing.CotangentSpace L) +
        jacobianRank Y P = Nat.card σ := by
    simpa only [jacobianRank] using
      finrank_localCotangent_add_finrank_gradientSpace hY P
  calc
    jacobianRank Y P + r = r + jacobianRank Y P := Nat.add_comm _ _
    _ ≤ Module.finrank (IsLocalRing.ResidueField L)
          (IsLocalRing.CotangentSpace L) + jacobianRank Y P :=
      Nat.add_le_add_right hr _
    _ = Nat.card σ := hsum

/-- The Jacobian rank is at most the codimension of an affine variety. -/
theorem jacobianRank_le_ambient_sub_dim (hY : IsAffineVariety Y)
    (P : Y) {r : ℕ} (hdim : dim Y = (r : WithBot ℕ∞)) :
    jacobianRank Y P ≤ Nat.card σ - r :=
  Nat.le_sub_of_add_le (jacobianRank_add_dim_le_ambient hY P hdim)

/-- Failure of affine nonsingularity is exactly strict Jacobian rank drop. -/
theorem not_isAffineNonsingularAt_iff_jacobianRank_lt
    (hY : IsAffineVariety Y) (P : Y) {r : ℕ}
    (hdim : dim Y = (r : WithBot ℕ∞)) :
    ¬ IsAffineNonsingularAt Y P ↔ jacobianRank Y P < Nat.card σ - r := by
  rw [isAffineNonsingularAt_iff_of_dim_eq P hdim]
  have hle := jacobianRank_add_dim_le_ambient hY P hdim
  omega

end Hartshorne

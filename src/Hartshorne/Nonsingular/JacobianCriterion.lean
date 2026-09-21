/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.LocalRingDimension
import Hartshorne.Nonsingular.AffineNonsingular
import Mathlib.Algebra.Field.ULift
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# The Jacobian criterion

Hartshorne, *Algebraic Geometry*, I.5, Theorem 5.1 (p. 32).

For an affine variety, nonsingularity defined by the rank of the Jacobian is
equivalent to regularity of the local ring.  The proof compares both conditions
using the cotangent-space dimension formula and the equality between the
dimension of the variety and that of its local ring.
-/

namespace Hartshorne

open MvPolynomial

universe u v

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The dimension of the germ local ring equals the dimension of the affine
variety for an arbitrary finite coordinate type. -/
theorem ringKrullDim_localRingAt_eq_dim_finite
    {σ : Type v} [Finite σ] {Y : Set (σ → k)}
    (hY : IsAffineVariety Y) (P : Y) :
    ringKrullDim (LocalRingAt hY.isIrreducible P) = dim Y := by
  have : IsDomain (coordinateRing Y) := isDomain_coordinateRing hY
  have : (maximalIdealAt Y P).IsMaximal := maximalIdealAt_isMaximal P
  let : Algebra (ULift.{v} k) k := ULift.algebra' k k
  let eAlg : ULift.{v} k →ₐ[ULift.{v} k] k :=
    { ULift.ringEquiv.toRingHom with
      commutes' := fun _ => rfl }
  let : Algebra.FiniteType (ULift.{v} k) k :=
    Algebra.FiniteType.of_surjective eAlg ULift.ringEquiv.surjective
  rw [ringKrullDim_localRingAt hY.isIrreducible P,
    dim_eq_ringKrullDim_coordinateRing hY.isAlgebraicSet]
  exact height_eq_ringKrullDim_of_isMaximal (ULift.{v} k)
    (coordinateRing Y) (maximalIdealAt Y P)

omit [IsAlgClosed k] in
/-- The germ local ring of an affine variety in finite-dimensional affine
space is Noetherian. -/
theorem IsAffineVariety.isNoetherianRing_localRingAt
    {σ : Type*} [Finite σ] {Y : Set (σ → k)}
    (hY : IsAffineVariety Y) (P : Y) :
    IsNoetherianRing (LocalRingAt hY.isIrreducible P) := by
  let m := maximalIdealAt Y P
  let _ : IsNoetherianRing (coordinateRing Y) :=
    Algebra.FiniteType.isNoetherianRing k (coordinateRing Y)
  let _ : IsNoetherianRing (Localization.AtPrime m) := inferInstance
  exact isNoetherianRing_of_ringEquiv _
    (localizationEquivLocalRing hY.isIrreducible P)

/-- **Hartshorne I.5, Theorem 5.1.** A point of an affine variety is
nonsingular in the Jacobian sense if and only if its local ring is regular. -/
theorem isAffineNonsingularAt_iff_isRegularLocalRing
    {σ : Type v} [Finite σ] {Y : Set (σ → k)}
    (hY : IsAffineVariety Y) (P : Y) :
    IsAffineNonsingularAt Y P ↔
      IsRegularLocalRing (LocalRingAt hY.isIrreducible P) := by
  let _ : IsNoetherianRing (LocalRingAt hY.isIrreducible P) :=
    hY.isNoetherianRing_localRingAt P
  have hcot := finrank_localCotangent_add_finrank_gradientSpace hY P
  constructor
  · rintro ⟨r, hdim, hrank⟩
    rw [IsRegularLocalRing.iff_finrank_cotangentSpace,
      ringKrullDim_localRingAt_eq_dim_finite hY P, hdim]
    norm_cast
    apply Nat.add_right_cancel
    calc
      Module.finrank
            (IsLocalRing.ResidueField (LocalRingAt hY.isIrreducible P))
            (IsLocalRing.CotangentSpace (LocalRingAt hY.isIrreducible P)) +
          Module.finrank k (definingIdealGradientSpace P) = Nat.card σ := hcot
      _ = jacobianRank Y P + r := hrank.symm
      _ = r + Module.finrank k (definingIdealGradientSpace P) := by
        rw [jacobianRank, Nat.add_comm]
  · intro hregular
    have hdim :=
      (IsRegularLocalRing.iff_finrank_cotangentSpace
        (LocalRingAt hY.isIrreducible P)).mp hregular
    rw [ringKrullDim_localRingAt_eq_dim_finite hY P] at hdim
    refine ⟨Module.finrank
        (IsLocalRing.ResidueField (LocalRingAt hY.isIrreducible P))
        (IsLocalRing.CotangentSpace (LocalRingAt hY.isIrreducible P)),
      hdim.symm, ?_⟩
    simpa only [jacobianRank, Nat.add_comm] using hcot

end Hartshorne

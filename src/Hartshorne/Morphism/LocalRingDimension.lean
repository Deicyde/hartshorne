/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.LocalRingLocalization
import Hartshorne.Dimension.DimFormula
import Hartshorne.Affine.DimensionCoordinateRing

/-!
# The last clause of Theorem 3.2(c)

Hartshorne, *Algebraic Geometry*, I.3, Theorem 3.2(c) (p. 17).

`dim 𝒪_P = dim Y` for a point of an affine variety.

The localisation clause of 3.2(c) already gives `dim 𝒪_P = height 𝔪_P`; what was
missing was `height 𝔪_P = dim Y`, which is Theorem 1.8A(b) applied to a maximal
ideal. The quotient by a maximal ideal is a field, so its dimension is zero and
the formula reads `height 𝔪_P = dim A(Y)`; Proposition 1.7 turns the right-hand
side into `dim Y`.

This was the last thing in the chapter waiting on the dimension formula that
belongs to §3 rather than §1.

## Main results

* `Hartshorne.height_maximalIdealAt_eq`
* `Hartshorne.ringKrullDim_localRingAt_eq_dim`
-/

namespace Hartshorne

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ} {Y : Set (Fin n → k)}

/-- **`height 𝔪_P = dim A(Y)`.**

Theorem 1.8A(b) at a maximal ideal: the quotient is a field, so it contributes
nothing and the height absorbs the whole dimension. -/
theorem height_maximalIdealAt_eq (hY : IsAffineVariety Y) (P : Y) :
    ((maximalIdealAt Y P).height : WithBot ℕ∞) = ringKrullDim (coordinateRing Y) := by
  haveI : IsDomain (coordinateRing Y) := isDomain_coordinateRing hY
  haveI : FiniteRingKrullDim (coordinateRing Y) :=
    finiteRingKrullDim_of_finiteType k (coordinateRing Y)
  haveI hmax : (maximalIdealAt Y P).IsMaximal := maximalIdealAt_isMaximal P
  haveI : (maximalIdealAt Y P).IsPrime := hmax.isPrime
  obtain ⟨h, hh⟩ : ∃ h : ℕ, (maximalIdealAt Y P).height = h :=
    ENat.ne_top_iff_exists.mp ((maximalIdealAt Y P).height_ne_top hmax.ne_top) |>.imp
      fun _ e => e.symm
  have hquot : ringKrullDim (coordinateRing Y ⧸ maximalIdealAt Y P) = 0 := by
    exact ringKrullDim_eq_zero_of_isField
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmax)
  have hform := height_add_ringKrullDim_quotient_eq k (coordinateRing Y)
    (maximalIdealAt Y P) h hh
  rw [hquot, add_zero] at hform
  rw [hh]
  exact hform

/-- **Theorem 3.2(c) in full**: `dim 𝒪_P = dim Y`. -/
theorem ringKrullDim_localRingAt_eq_dim (hY : IsAffineVariety Y) (P : Y) :
    ringKrullDim (LocalRingAt hY.isIrreducible P) = dim Y := by
  rw [ringKrullDim_localRingAt hY.isIrreducible P,
    dim_eq_ringKrullDim_coordinateRing hY.isAlgebraicSet]
  exact height_maximalIdealAt_eq hY P

end Hartshorne

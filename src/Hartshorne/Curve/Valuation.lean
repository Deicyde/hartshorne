/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Curve.LocalDVR
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

/-!
# Valuations associated to points on nonsingular curves

Hartshorne, *Algebraic Geometry*, I.6 (p. 41).

A nonsingular point on a curve determines a rank-one discrete valuation of the
function field, trivial on the base field, whose valuation subring is the image
of the point's local ring.
-/

namespace Hartshorne

open scoped WithZero

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

namespace Variety

/-- The discrete valuation of the function field associated to a nonsingular
point on a curve. -/
noncomputable def HasAffineOpenBasis.valuationAt
    {X : Variety k} (hX : X.HasAffineOpenBasis) (hcurve : X.IsCurve)
    (P : X.carrier) (hP : X.NonsingularAt P) :
    Valuation X.FunctionField ℤᵐ⁰ := by
  let _ : IsDiscreteValuationRing (X.LocalRingAt P) :=
    hX.isDiscreteValuationRing_localRingAt_of_nonsingularAt hcurve P hP
  let _ : IsFractionRing (X.LocalRingAt P) X.FunctionField :=
    hX.isFractionRing_localRingAt P
  exact (IsDiscreteValuationRing.maximalIdeal
    (X.LocalRingAt P)).valuation X.FunctionField

/-- The valuation subring of the function field associated to a nonsingular
point on a curve. -/
noncomputable def HasAffineOpenBasis.valuationSubringAt
    {X : Variety k} (hX : X.HasAffineOpenBasis) (hcurve : X.IsCurve)
    (P : X.carrier) (hP : X.NonsingularAt P) :
    ValuationSubring X.FunctionField :=
  (hX.valuationAt hcurve P hP).valuationSubring

/-- The valuation associated to a nonsingular curve point is rank-one
discrete. -/
theorem HasAffineOpenBasis.valuationAt_isRankOneDiscrete
    {X : Variety k} (hX : X.HasAffineOpenBasis) (hcurve : X.IsCurve)
    (P : X.carrier) (hP : X.NonsingularAt P) :
    Valuation.IsRankOneDiscrete (hX.valuationAt hcurve P hP) := by
  let _ : IsDiscreteValuationRing (X.LocalRingAt P) :=
    hX.isDiscreteValuationRing_localRingAt_of_nonsingularAt hcurve P hP
  let _ : IsFractionRing (X.LocalRingAt P) X.FunctionField :=
    hX.isFractionRing_localRingAt P
  unfold HasAffineOpenBasis.valuationAt
  infer_instance

/-- The valuation subring at a nonsingular curve point is exactly the image of
its local ring in the function field. -/
theorem HasAffineOpenBasis.valuationSubringAt_toSubring
    {X : Variety k} (hX : X.HasAffineOpenBasis) (hcurve : X.IsCurve)
    (P : X.carrier) (hP : X.NonsingularAt P) :
    (hX.valuationSubringAt hcurve P hP).toSubring =
      (X.localRingRange P).toSubring := by
  let _ : IsDiscreteValuationRing (X.LocalRingAt P) :=
    hX.isDiscreteValuationRing_localRingAt_of_nonsingularAt hcurve P hP
  let _ : IsFractionRing (X.LocalRingAt P) X.FunctionField :=
    hX.isFractionRing_localRingAt P
  unfold HasAffineOpenBasis.valuationSubringAt
    HasAffineOpenBasis.valuationAt
  rw [← IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring,
    ← RingHom.range_eq_map]
  rfl

/-- The valuation subring at a nonsingular curve point is a DVR. -/
theorem HasAffineOpenBasis.isDiscreteValuationRing_valuationSubringAt
    {X : Variety k} (hX : X.HasAffineOpenBasis) (hcurve : X.IsCurve)
    (P : X.carrier) (hP : X.NonsingularAt P) :
    IsDiscreteValuationRing (hX.valuationSubringAt hcurve P hP) := by
  let _ : Valuation.IsRankOneDiscrete (hX.valuationAt hcurve P hP) :=
    hX.valuationAt_isRankOneDiscrete hcurve P hP
  unfold HasAffineOpenBasis.valuationSubringAt
  infer_instance

/-- The ambient function field is the fraction field of the valuation subring
at a nonsingular curve point. -/
theorem HasAffineOpenBasis.isFractionRing_valuationSubringAt
    {X : Variety k} (hX : X.HasAffineOpenBasis) (hcurve : X.IsCurve)
    (P : X.carrier) (hP : X.NonsingularAt P) :
    IsFractionRing (hX.valuationSubringAt hcurve P hP)
      X.FunctionField :=
  inferInstance

/-- The valuation associated to a nonsingular curve point is trivial on the
embedded base field. -/
theorem HasAffineOpenBasis.valuationAt_isTrivialOn
    {X : Variety k} (hX : X.HasAffineOpenBasis) (hcurve : X.IsCurve)
    (P : X.carrier) (hP : X.NonsingularAt P) :
    Valuation.IsTrivialOn k (hX.valuationAt hcurve P hP) := by
  let _ : IsDiscreteValuationRing (X.LocalRingAt P) :=
    hX.isDiscreteValuationRing_localRingAt_of_nonsingularAt hcurve P hP
  let _ : IsFractionRing (X.LocalRingAt P) X.FunctionField :=
    hX.isFractionRing_localRingAt P
  apply Valuation.IsTrivialOn.of_le_one
  intro c
  unfold HasAffineOpenBasis.valuationAt
  rw [IsScalarTower.algebraMap_apply k (X.LocalRingAt P) X.FunctionField]
  exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ _

/-- Reconstructing a valuation from its valuation subring yields an equivalent
valuation. -/
theorem HasAffineOpenBasis.valuationSubringAt_valuation_isEquiv
    {X : Variety k} (hX : X.HasAffineOpenBasis) (hcurve : X.IsCurve)
    (P : X.carrier) (hP : X.NonsingularAt P) :
    (hX.valuationSubringAt hcurve P hP).valuation.IsEquiv
      (hX.valuationAt hcurve P hP) := by
  unfold HasAffineOpenBasis.valuationSubringAt
  exact (Valuation.isEquiv_valuation_valuationSubring _).symm

/-- The valuation reconstructed from the valuation subring is also trivial on
the embedded base field. -/
theorem HasAffineOpenBasis.valuationSubringAt_valuation_isTrivialOn
    {X : Variety k} (hX : X.HasAffineOpenBasis) (hcurve : X.IsCurve)
    (P : X.carrier) (hP : X.NonsingularAt P) :
    Valuation.IsTrivialOn k
      (hX.valuationSubringAt hcurve P hP).valuation :=
  (hX.valuationSubringAt_valuation_isEquiv hcurve P hP).isTrivialOn_iff.mpr
    (hX.valuationAt_isTrivialOn hcurve P hP)

end Variety

end Hartshorne

/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Curve.Basic
import Hartshorne.Curve.DVR
import Hartshorne.Morphism.LocalRingFunctionField
import Hartshorne.Nonsingular.IntrinsicNonsingular
import Hartshorne.Nonsingular.LocalRingDimension

/-!
# Local rings of nonsingular curves

Hartshorne, *Algebraic Geometry*, I.6 (p. 41).

The local ring at a nonsingular point of a curve is a discrete valuation ring.
-/

namespace Hartshorne

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

namespace Variety

/-- The local ring at a nonsingular point of a curve is a discrete valuation
ring. -/
theorem HasAffineOpenBasis.isDiscreteValuationRing_localRingAt_of_nonsingularAt
    {X : Variety k} (hX : X.HasAffineOpenBasis) (hcurve : X.IsCurve)
    (P : X.carrier) (hP : X.NonsingularAt P) :
    IsDiscreteValuationRing (X.LocalRingAt P) := by
  let _ : IsNoetherianRing (X.LocalRingAt P) :=
    hX.isNoetherianRing_localRingAt P
  have hdim : ringKrullDim (X.LocalRingAt P) = 1 :=
    (hX.ringKrullDim_localRingAt_eq P).trans hcurve
  exact ((dvr_characterizations (X.LocalRingAt P) hdim).out 2 0).mp hP

/-- Every local ring of a nonsingular curve is a discrete valuation ring. -/
theorem HasAffineOpenBasis.isDiscreteValuationRing_localRingAt_of_nonsingular
    {X : Variety k} (hX : X.HasAffineOpenBasis) (hcurve : X.IsCurve)
    (hns : X.Nonsingular) (P : X.carrier) :
    IsDiscreteValuationRing (X.LocalRingAt P) :=
  hX.isDiscreteValuationRing_localRingAt_of_nonsingularAt hcurve P (hns P)

end Variety

end Hartshorne

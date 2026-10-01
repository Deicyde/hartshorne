/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Affine.DimensionCoordinateRing
import Hartshorne.Intersection.AffineProductCoordinateRing
import Hartshorne.Intersection.TensorProductDimension

/-!
# Dimension of an affine product

Hartshorne, *Algebraic Geometry*, I.3, Exercise 3.15(d) (p. 22), as used in
the proof of Proposition I.7.1.

## Main result

* `Hartshorne.dim_affineProduct`
-/

namespace Hartshorne

open scoped TensorProduct

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
  {σ τ : Type} [Finite σ] [Finite τ]

/-- **Exercise I.3.15(d).** The dimension of a product of affine varieties is
the sum of their dimensions. -/
theorem dim_affineProduct {X : Set (σ → k)} {Y : Set (τ → k)}
    (hX : IsAffineVariety X) (hY : IsAffineVariety Y) :
    dim (affineProduct X Y) = dim X + dim Y := by
  have hXY : IsAffineVariety (affineProduct X Y) :=
    isAffineVariety_affineProduct hX hY
  have : IsDomain (coordinateRing X) := isDomain_coordinateRing hX
  have : IsDomain (coordinateRing Y) := isDomain_coordinateRing hY
  have : IsDomain (coordinateRing (affineProduct X Y)) :=
    isDomain_coordinateRing hXY
  let e := coordinateRing_affineProductEquiv X Y
  have : IsDomain (coordinateRing X ⊗[k] coordinateRing Y) :=
    e.symm.injective.isDomain
  calc
    dim (affineProduct X Y) =
        ringKrullDim (coordinateRing (affineProduct X Y)) :=
      dim_eq_ringKrullDim_coordinateRing hXY.isAlgebraicSet
    _ = ringKrullDim (coordinateRing X ⊗[k] coordinateRing Y) :=
      RingEquiv.ringKrullDim e.toRingEquiv
    _ = ringKrullDim (coordinateRing X) + ringKrullDim (coordinateRing Y) :=
      ringKrullDim_tensorProduct k (coordinateRing X) (coordinateRing Y)
    _ = dim X + dim Y := by
      rw [← dim_eq_ringKrullDim_coordinateRing hX.isAlgebraicSet,
        ← dim_eq_ringKrullDim_coordinateRing hY.isAlgebraicSet]

end Hartshorne

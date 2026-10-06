/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.Codimension
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Regularity in codimension one

Hartshorne, *Algebraic Geometry*, II.6, p. 130.

A scheme is regular in codimension one when every codimension-one point has a
regular local ring. Hartshorne's condition `(*)` additionally requires the
scheme to be Noetherian, integral, and separated.
-/

namespace AlgebraicGeometry

universe u

/-- A scheme is regular in codimension one when the stalk at every point of
coheight one is a regular local ring. -/
def Scheme.IsRegularInCodimensionOne (X : Scheme.{u}) : Prop :=
  ∀ x : X, Order.coheight x = 1 → IsRegularLocalRing (X.presheaf.stalk x)

/-- Hartshorne's condition `(*)`: Noetherian, integral, separated, and regular
in codimension one. -/
def Scheme.SatisfiesConditionStar (X : Scheme.{u}) : Prop :=
  IsNoetherian X ∧ IsIntegral X ∧ X.IsSeparated ∧ X.IsRegularInCodimensionOne

/-- Hartshorne's local-dimension formulation of regularity in codimension one
agrees with the coheight formulation. -/
theorem Scheme.isRegularInCodimensionOne_iff_ringKrullDim (X : Scheme.{u}) :
    X.IsRegularInCodimensionOne ↔
      ∀ x : X, ringKrullDim (X.presheaf.stalk x) = 1 →
        IsRegularLocalRing (X.presheaf.stalk x) := by
  constructor
  · intro h x hx
    apply h x
    rw [ringKrullDim_stalk_eq_coheight] at hx
    exact WithBot.coe_eq_coe.mp hx
  · intro h x hx
    apply h x
    rw [ringKrullDim_stalk_eq_coheight]
    exact WithBot.coe_eq_coe.mpr hx

namespace Scheme.SatisfiesConditionStar

/-- Condition `(*)` implies that the scheme is Noetherian. -/
theorem isNoetherian {X : Scheme.{u}} (h : X.SatisfiesConditionStar) : IsNoetherian X :=
  h.1

/-- Condition `(*)` implies that the scheme is integral. -/
theorem isIntegral {X : Scheme.{u}} (h : X.SatisfiesConditionStar) : IsIntegral X :=
  h.2.1

/-- Condition `(*)` implies that the scheme is separated. -/
theorem isSeparated {X : Scheme.{u}} (h : X.SatisfiesConditionStar) : X.IsSeparated :=
  h.2.2.1

/-- Condition `(*)` implies regularity in codimension one. -/
theorem isRegularInCodimensionOne {X : Scheme.{u}} (h : X.SatisfiesConditionStar) :
    X.IsRegularInCodimensionOne :=
  h.2.2.2

end Scheme.SatisfiesConditionStar

end AlgebraicGeometry

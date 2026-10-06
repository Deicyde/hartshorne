/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Curve.DVR
import Hartshorne.Scheme.RegularInCodimensionOne
import Mathlib.AlgebraicGeometry.OrderOfVanishing

/-!
# Codimension-one stalks and their valuations

Hartshorne, *Algebraic Geometry*, II.6, p. 130.

On a scheme satisfying Hartshorne's condition `(*)`, every codimension-one
stalk is a discrete valuation ring. Its canonical fraction field is the
function field of the scheme, and Mathlib's order of vanishing is the additive
normalization of the corresponding DVR valuation.
-/

noncomputable section

open WithZero

namespace AlgebraicGeometry

universe u

/-- A codimension-one stalk on a scheme satisfying Hartshorne's condition
`(*)` is a discrete valuation ring. -/
theorem Scheme.codimensionOneStalk_isDiscreteValuationRing
    {X : Scheme.{u}} (hX : X.SatisfiesConditionStar) {x : X}
    (hx : Order.coheight x = 1) :
    let _ : IsIntegral X := hX.isIntegral
    IsDiscreteValuationRing (X.presheaf.stalk x) := by
  let _ : IsNoetherian X := hX.isNoetherian
  let _ : IsIntegral X := hX.isIntegral
  have hdim : ringKrullDim (X.presheaf.stalk x) = 1 := by
    rw [ringKrullDim_stalk_eq_coheight]
    exact WithBot.coe_eq_coe.mpr hx
  exact ((Hartshorne.dvr_characterizations (X.presheaf.stalk x) hdim).out 2 0).mp
    (hX.isRegularInCodimensionOne x hx)

/-- For every stalk of a scheme satisfying condition `(*)`, the canonical map
to the function field exhibits the latter as its fraction field. -/
theorem Scheme.functionField_isFractionRing_of_stalk_of_satisfiesConditionStar
    {X : Scheme.{u}} (hX : X.SatisfiesConditionStar) (x : X) :
    let _ : IsIntegral X := hX.isIntegral
    IsFractionRing (X.presheaf.stalk x) X.functionField := by
  let _ : IsIntegral X := hX.isIntegral
  infer_instance

/-- The canonical algebra equivalence from the abstract fraction ring of a
stalk to the function field. -/
noncomputable def Scheme.fractionRingStalkEquivFunctionField
    {X : Scheme.{u}} (hX : X.SatisfiesConditionStar) (x : X) :
    let _ : IsIntegral X := hX.isIntegral
    FractionRing (X.presheaf.stalk x) ≃ₐ[X.presheaf.stalk x] X.functionField := by
  let _ : IsIntegral X := hX.isIntegral
  exact FractionRing.algEquiv _ _

/-- At a codimension-one point, `ordHom` is the inverse of the multiplicative
DVR valuation. The inverse converts Mathlib's valuation convention, in which a
uniformizer has value below one, to positive order of vanishing. -/
theorem Scheme.ordHom_eq_codimensionOneStalkValuation
    {X : Scheme.{u}} (hX : X.SatisfiesConditionStar) {x : X}
    (hx : Order.coheight x = 1) :
    let _ : IsNoetherian X := hX.isNoetherian
    let _ : IsIntegral X := hX.isIntegral
    let _ : IsDiscreteValuationRing (X.presheaf.stalk x) :=
      X.codimensionOneStalk_isDiscreteValuationRing hX hx
    X.ordHom x hx =
      MonoidWithZeroHom.comp MonoidWithZero.inverse
        ((IsDiscreteValuationRing.maximalIdeal (X.presheaf.stalk x)).valuation
          X.functionField).toMonoidWithZeroHom := by
  let _ : IsNoetherian X := hX.isNoetherian
  let _ : IsIntegral X := hX.isIntegral
  let _ : IsDiscreteValuationRing (X.presheaf.stalk x) :=
    X.codimensionOneStalk_isDiscreteValuationRing hX hx
  exact Ring.ordFrac_eq_inverse_comp_valuation

/-- Additive form of `ordHom_eq_codimensionOneStalkValuation`: `Scheme.ord`
is the normalized additive DVR valuation, including its value at zero. -/
theorem Scheme.ord_eq_codimensionOneStalkValuation
    {X : Scheme.{u}} (hX : X.SatisfiesConditionStar) {x : X}
    (hx : Order.coheight x = 1) :
    let _ : IsNoetherian X := hX.isNoetherian
    let _ : IsIntegral X := hX.isIntegral
    let _ : IsDiscreteValuationRing (X.presheaf.stalk x) :=
      X.codimensionOneStalk_isDiscreteValuationRing hX hx
    ∀ f : X.functionField,
      X.ord f x =
        Multiplicative.toAdd
          (((((IsDiscreteValuationRing.maximalIdeal (X.presheaf.stalk x)).valuation
            X.functionField) f)⁻¹).unzeroD 1) := by
  dsimp only
  let _ : IsNoetherian X := hX.isNoetherian
  let _ : IsIntegral X := hX.isIntegral
  let _ : IsDiscreteValuationRing (X.presheaf.stalk x) :=
    X.codimensionOneStalk_isDiscreteValuationRing hX hx
  intro f
  rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hx]
  change Multiplicative.toAdd ((Ring.ordFrac (X.presheaf.stalk x) f).unzeroD 1) = _
  rw [Ring.ordFrac_eq_valuation_inv]

end AlgebraicGeometry

/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.Normal
import Hartshorne.Scheme.WeilClassGroup
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-!
# Locally factorial schemes and locally principal Weil divisors

Hartshorne, *Algebraic Geometry*, II.6 (pp. 141--142).

Local factoriality is a condition on every local ring.  Local principality is stated directly in
terms of coefficients on an open neighbourhood, so it does not presuppose a separate restriction
construction for Weil divisors or any Cartier-divisor infrastructure.
-/

noncomputable section

namespace AlgebraicGeometry

universe u

/-- A scheme is locally factorial when every local ring is a unique factorization domain. -/
def Scheme.IsLocallyFactorial (X : Scheme.{u}) : Prop :=
  ∀ x : X,
    IsDomain (X.presheaf.stalk x) ∧
      UniqueFactorizationMonoid (X.presheaf.stalk x)

namespace Scheme.WeilDivisor

/-- A Weil divisor is locally principal when, near every point, its coefficients agree with the
orders of a single nonzero rational function.  This is the coefficientwise form of saying that
the restricted divisor is principal. -/
noncomputable def IsLocallyPrincipal
    {X : Scheme.{u}} [IsNoetherian X] [IsIntegral X]
    (D : X.WeilDivisor) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    ∃ f : X.functionFieldˣ, ∀ y : X, y ∈ U → D.1 y = X.ord (f : X.functionField) y

/-- Under condition `(*)`, the coefficientwise local-principality definition is equivalently
expressed using the existing principal Weil divisor. -/
theorem isLocallyPrincipal_iff_exists_principalDivisor
    {X : Scheme.{u}} (hX : X.SatisfiesConditionStar) (D : X.WeilDivisor) :
    let _ : IsNoetherian X := hX.isNoetherian
    let _ : IsIntegral X := hX.isIntegral
    IsLocallyPrincipal D ↔
      ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
        ∃ f : X.functionFieldˣ, ∀ y : X, y ∈ U →
          D.1 y = (X.principalDivisor hX f).1 y := by
  dsimp only
  let _ : IsNoetherian X := hX.isNoetherian
  let _ : IsIntegral X := hX.isIntegral
  simp only [IsLocallyPrincipal, X.principalDivisor_apply hX]

end Scheme.WeilDivisor

end AlgebraicGeometry

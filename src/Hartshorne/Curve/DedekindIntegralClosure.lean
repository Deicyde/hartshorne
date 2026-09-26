/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Curve.KrullAkizuki
import Hartshorne.Dimension.Integral
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Integral closures of Dedekind domains

This file proves Hartshorne I.6, Theorem 6.3A.  If `A` is a Dedekind domain,
`K` is its fraction field, and `L/K` is finite, then the integral closure of
`A` in `L` is again a Dedekind domain.  No separability assumption is made.

The Noetherian conclusion is the nonseparable content supplied by the
Krull--Akizuki theorem.  The remaining ingredients already hold for integral
closures in arbitrary finite field extensions.  We also retain Hartshorne's
exact dimension-one conclusion separately, since Mathlib's
`IsDedekindDomain` class records only dimension at most one and permits fields.
-/

namespace Hartshorne

noncomputable section

universe u v w

variable
  (A : Type u) [CommRing A]
  (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
  (L : Type w) [Field L] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L]

private theorem integralClosure_noZeroSMulDivisors :
    NoZeroSMulDivisors (integralClosure A L) L := by
  constructor
  intro c x hcx
  rw [Algebra.smul_def] at hcx
  rcases mul_eq_zero.mp hcx with hc | hx
  · exact Or.inl ((map_eq_zero_iff _
      (IsIntegralClosure.algebraMap_injective (integralClosure A L) A L)).mp hc)
  · exact Or.inr hx

/-- An integral closure in a finite extension of the fraction field has the
same Krull dimension as the base.  In particular, exact dimension one is
preserved without a separability hypothesis. -/
theorem ringKrullDim_integralClosure_eq_one_of_finite_extension
    [IsDomain A] [FiniteDimensional K L]
    (hdim : ringKrullDim A = 1) :
    ringKrullDim (integralClosure A L) = 1 := by
  have hAL : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  let _ : FaithfulSMul A (integralClosure A L) :=
    (faithfulSMul_iff_algebraMap_injective A (integralClosure A L)).2 (by
      intro x y hxy
      apply hAL
      rw [IsScalarTower.algebraMap_apply A (integralClosure A L) L,
        IsScalarTower.algebraMap_apply A (integralClosure A L) L, hxy])
  rw [ringKrullDim_eq_of_isIntegral A (integralClosure A L), hdim]

/-- **Hartshorne I.6, Theorem 6.3A.**  The integral closure of a Dedekind
domain in an arbitrary finite extension of its fraction field is a Dedekind
domain.  Unlike Mathlib's separable integral-closure theorem, this result makes
no separability assumption. -/
theorem integralClosure_isDedekindDomain_of_finite_extension
    [FiniteDimensional K L] [IsDedekindDomain A] :
    IsDedekindDomain (integralClosure A L) := by
  let _ : NoZeroSMulDivisors (integralClosure A L) L :=
    integralClosure_noZeroSMulDivisors A L
  let _ : IsNoetherianRing (integralClosure A L) :=
    krullAkizuki_isNoetherianRing A K L (integralClosure A L)
  let _ : Ring.DimensionLEOne (integralClosure A L) :=
    krullAkizuki_dimensionLEOne A K L (integralClosure A L)
  let _ : IsIntegrallyClosed (integralClosure A L) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension K
  exact { toIsDomain := inferInstance, toIsDedekindRing := {} }

end

end Hartshorne

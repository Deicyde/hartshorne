/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Characterizations of discrete valuation rings

Hartshorne, *Algebraic Geometry*, I.6, Theorem 6.2A (p. 40).

For a Noetherian local domain of dimension one, being a DVR, being integrally
closed, being regular local, and having principal maximal ideal are equivalent.
-/

namespace Hartshorne

open IsLocalRing

/-- A Noetherian, integrally closed domain of dimension one localized at a
nonzero prime ideal is a discrete valuation ring. -/
theorem dedekind_localization_dvr
    (A : Type*) [CommRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [IsDomain A] (hdim : ringKrullDim A = 1)
    (P : Ideal A) [P.IsPrime] (hP : P ≠ ⊥) :
    IsDiscreteValuationRing (Localization.AtPrime P) := by
  let : Ring.DimensionLEOne A :=
    ⟨fun {Q} hQ hQprime =>
      Ring.krullDimLE_one_iff_of_noZeroDivisors.mp
        (Ring.krullDimLE_iff.mpr hdim.le) Q hQ hQprime⟩
  let : IsDedekindDomain A :=
    { toIsDomain := inferInstance
      toIsDedekindRing := {} }
  exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
    A hP (Localization.AtPrime P)

/-- **Hartshorne I.6, Theorem 6.2A.** The four standard characterizations of a
discrete valuation ring among Noetherian local domains of dimension one. -/
theorem dvr_characterizations
    (A : Type*) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
    (hdim : ringKrullDim A = 1) :
    List.TFAE
      [IsDiscreteValuationRing A,
        IsIntegrallyClosed A,
        IsRegularLocalRing A,
        (maximalIdeal A).IsPrincipal] := by
  have hnf : ¬ IsField A :=
    fun hA ↦ zero_ne_one ((ringKrullDim_eq_zero_of_isField hA).symm.trans hdim)
  have hdvr := IsDiscreteValuationRing.TFAE A hnf
  tfae_have 1 ↔ 2 := by
    constructor
    · intro h
      have h' : IsIntegrallyClosed A ∧
          ∃! P : Ideal A, P ≠ ⊥ ∧ P.IsPrime := (hdvr.out 0 3).mp h
      exact h'.1
    · intro h
      apply (hdvr.out 0 3).mpr
      refine ⟨h, maximalIdeal A, ⟨?_, inferInstance⟩, ?_⟩
      · exact isField_iff_maximalIdeal_eq.not.mp hnf
      · intro P hP
        exact IsLocalRing.eq_maximalIdeal
          (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp
            (Ring.krullDimLE_iff.mpr hdim.le) P hP.1 hP.2)
  tfae_have 1 ↔ 3 := by
    constructor
    · intro h
      rw [IsRegularLocalRing.iff_finrank_cotangentSpace, hdim]
      exact_mod_cast (IsLocalRing.finrank_CotangentSpace_eq_one_iff.mpr h)
    · intro h
      apply IsLocalRing.finrank_CotangentSpace_eq_one_iff.mp
      have h' := (IsRegularLocalRing.iff_finrank_cotangentSpace A).mp h
      rw [hdim] at h'
      exact_mod_cast h'
  tfae_have 1 ↔ 4 := hdvr.out 0 4
  tfae_finish

end Hartshorne

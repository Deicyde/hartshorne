/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Affine.DimensionCoordinateRing
import Hartshorne.Curve.Basic
import Hartshorne.Curve.DVR
import Hartshorne.Morphism.AffineGermCompare
import Hartshorne.Morphism.LocalRingDimension
import Hartshorne.Morphism.LocalRingLocalization
import Hartshorne.Nonsingular.IntrinsicNonsingular
import Mathlib.RingTheory.DedekindDomain.Dvr

/-!
# Coordinate rings of nonsingular affine curves

Hartshorne, *Algebraic Geometry*, I.6, Proposition 6.7 (pp. 42--43).

The coordinate ring of a nonsingular affine curve has Krull dimension exactly
one and is a Dedekind domain.
-/

namespace Hartshorne

open MvPolynomial TopologicalSpace

universe u v

variable {k : Type u} [Field k] [IsAlgClosed k]
  {σ : Type v} [Finite σ] {Y : Set (σ → k)}

/-- The coordinate ring of an affine curve has Krull dimension exactly one. -/
theorem IsAffineVariety.ringKrullDim_coordinateRing_eq_one
    (hY : IsAffineVariety Y)
    (hcurve :
      (Variety.ofQuasiAffine hY.isQuasiAffineVariety).IsCurve) :
    ringKrullDim (coordinateRing Y) = 1 := by
  rw [← dim_eq_ringKrullDim_coordinateRing hY.isAlgebraicSet]
  exact hcurve

/-- The coordinate ring of a nonsingular affine curve is a Dedekind domain. -/
theorem IsAffineVariety.isDedekindDomain_coordinateRing_of_nonsingular
    (hY : IsAffineVariety Y)
    (hcurve :
      (Variety.ofQuasiAffine hY.isQuasiAffineVariety).IsCurve)
    (hns :
      (Variety.ofQuasiAffine hY.isQuasiAffineVariety).Nonsingular) :
    IsDedekindDomain (coordinateRing Y) := by
  let _ : IsDomain (coordinateRing Y) := isDomain_coordinateRing hY
  let _ : IsNoetherianRing (coordinateRing Y) :=
    Algebra.FiniteType.isNoetherianRing k (coordinateRing Y)
  have hdim : ringKrullDim (coordinateRing Y) = 1 :=
    hY.ringKrullDim_coordinateRing_eq_one hcurve
  let _ : Ring.KrullDimLE 1 (coordinateRing Y) :=
    Ring.krullDimLE_iff.mpr hdim.le
  let _ : IsDedekindDomainDvr (coordinateRing Y) :=
    { toIsNoetherian := inferInstance
      is_dvr_at_nonzero_prime := by
        intro p hp hpPrime
        let _ : p.IsPrime := hpPrime
        have hpMax : p.IsMaximal := hpPrime.isMaximal_of_ne_bot hp
        obtain ⟨P, hP⟩ :=
          maximalIdealAt_surjective hY.isAlgebraicSet hpMax
        subst p
        let X := Variety.ofQuasiAffine hY.isQuasiAffineVariety
        let P' : X.carrier := ⟨P.1, P.2⟩
        have hregular :
            IsRegularLocalRing (LocalRingAt hY.isIrreducible P) := by
          change IsRegularLocalRing
            (LocalRingAt hY.isIrreducible
              (affinePoint hY.isQuasiAffineVariety P'))
          exact (isRegularLocalRing_iff_of_ringEquiv
            (localRingEquivAffine hY.isQuasiAffineVariety P')).mp (hns P')
        let _ : IsDomain (LocalRingAt hY.isIrreducible P) :=
          (localizationEquivLocalRing hY.isIrreducible P).symm.toMulEquiv.isDomain
            (Localization.AtPrime (maximalIdealAt Y P))
        let _ : IsNoetherianRing (LocalRingAt hY.isIrreducible P) :=
          hY.isNoetherianRing_localRingAt P
        have hlocaldim :
            ringKrullDim (LocalRingAt hY.isIrreducible P) = 1 :=
          (ringKrullDim_localRingAt_eq_dim_finite hY P).trans hcurve
        let _ : IsDiscreteValuationRing (LocalRingAt hY.isIrreducible P) :=
          ((dvr_characterizations _ hlocaldim).out 2 0).mp hregular
        exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
          (localizationEquivLocalRing hY.isIrreducible P).symm }
  infer_instance

end Hartshorne

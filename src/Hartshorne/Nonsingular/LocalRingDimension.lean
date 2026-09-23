/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.LocalRingDimension
import Hartshorne.Nonsingular.LocalRingOpen
import Hartshorne.Rational.VarietyDimension

/-!
# Dimension of local rings of a variety

Hartshorne, *Algebraic Geometry*, I.3, Theorem 3.2(c), transported through an
affine open neighbourhood for use in I.6.
-/

namespace Hartshorne

open TopologicalSpace

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

namespace Variety

/-- The local ring at every point of a variety with an affine-open basis has
the same Krull dimension as the variety. -/
theorem HasAffineOpenBasis.ringKrullDim_localRingAt_eq
    {X : Variety k} (hX : X.HasAffineOpenBasis) (P : X.carrier) :
    ringKrullDim (LocalRingAt X P) = topologicalKrullDim X.carrier := by
  obtain ⟨V, hV, hPV, -, σ, hσ, Z, hZ, φ, hφ⟩ := hX ⊤ P trivial
  let _ : Finite σ := hσ
  let Q : (X.restrict V hV).carrier := ⟨P, hPV⟩
  let hVaff : (X.restrict V hV).IsAffine := ⟨σ, hσ, Z, hZ, φ, hφ⟩
  let eOpen : LocalRingAt (X.restrict V hV) Q ≃+* LocalRingAt X P :=
    localRingEquivRestrict Q
  let eIso : LocalRingAt (Variety.ofQuasiAffine hZ.isQuasiAffineVariety) (φ Q)
      ≃+* LocalRingAt (X.restrict V hV) Q :=
    RingEquiv.ofBijective (φ.localRingHom Q)
      (VarietyHom.bijective_localRingHom_of_isIso hφ Q)
  let eAffine : LocalRingAt (Variety.ofQuasiAffine hZ.isQuasiAffineVariety) (φ Q)
      ≃+* Hartshorne.LocalRingAt hZ.isIrreducible
        (affinePoint hZ.isQuasiAffineVariety (φ Q)) :=
    localRingEquivAffine hZ.isQuasiAffineVariety (φ Q)
  let eLocal : Hartshorne.LocalRingAt hZ.isIrreducible
        (affinePoint hZ.isQuasiAffineVariety (φ Q)) ≃+* LocalRingAt X P :=
    (eAffine.symm.trans eIso).trans eOpen
  have hlocal : ringKrullDim (LocalRingAt X P) = dim Z :=
    (ringKrullDim_eq_of_ringEquiv eLocal).symm.trans
      (ringKrullDim_localRingAt_eq_dim_finite hZ
        (affinePoint hZ.isQuasiAffineVariety (φ Q)))
  have hVdimZ : topologicalKrullDim (X.restrict V hV).carrier = dim Z :=
    hφ.topologicalKrullDim_eq.trans (dim_def Z).symm
  obtain ⟨rX, hXdim, hXtr⟩ := hX.exists_dimension_eq_trdeg
  obtain ⟨rV, hVdim, hVtr⟩ := hVaff.exists_dimension_eq_trdeg
  let eF := RationalMapFunctionField.openFunctionFieldAlgEquiv X V hV
  have hr : rV = rX := by
    have : (rV : Cardinal) = rX :=
      hVtr.symm.trans (eF.trdeg_eq.symm.trans hXtr)
    exact_mod_cast this
  calc
    ringKrullDim (LocalRingAt X P) = dim Z := hlocal
    _ = topologicalKrullDim (X.restrict V hV).carrier := hVdimZ.symm
    _ = (rV : WithBot ℕ∞) := hVdim
    _ = (rX : WithBot ℕ∞) := by rw [hr]
    _ = topologicalKrullDim X.carrier := hXdim.symm

end Variety

end Hartshorne

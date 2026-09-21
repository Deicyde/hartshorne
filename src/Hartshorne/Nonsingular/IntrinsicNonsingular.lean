/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Nonsingular.JacobianCriterion
import Hartshorne.Nonsingular.LocalRingOpen

/-!
# Intrinsic nonsingularity

Hartshorne, *Algebraic Geometry*, I.5 (p. 32).

A point of a variety is nonsingular when its local ring is regular.  The
definition is intrinsic: it is unchanged on restriction to an open
neighbourhood and is preserved by isomorphisms.  On an affine variety it agrees
with the Jacobian definition.
-/

namespace Hartshorne

open TopologicalSpace

universe u v

variable {k : Type u} [Field k]

/-- Regularity is invariant under a ring equivalence. -/
theorem isRegularLocalRing_iff_of_ringEquiv
    {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    IsRegularLocalRing R ↔ IsRegularLocalRing S := by
  constructor
  · intro hR
    let _ : IsRegularLocalRing R := hR
    exact IsRegularLocalRing.of_ringEquiv e
  · intro hS
    let _ : IsRegularLocalRing S := hS
    exact IsRegularLocalRing.of_ringEquiv e.symm

namespace Variety

/-- A point of a variety is nonsingular when its local ring is regular. -/
def NonsingularAt (X : Variety.{u, v} k) (P : X.carrier) : Prop :=
  IsRegularLocalRing (LocalRingAt X P)

/-- A variety is nonsingular when it is nonsingular at every point. -/
def Nonsingular (X : Variety.{u, v} k) : Prop :=
  ∀ P : X.carrier, NonsingularAt X P

/-- The singular locus of a variety. -/
def SingularLocus (X : Variety.{u, v} k) : Set X.carrier :=
  {P | ¬ NonsingularAt X P}

/-- A variety is singular when it is not nonsingular. -/
def Singular (X : Variety.{u, v} k) : Prop :=
  ¬ Nonsingular X

/-- Nonsingularity is unchanged after restricting to an open neighbourhood of
the point. -/
theorem nonsingularAt_restrict_iff {X : Variety.{u, v} k}
    {U : Opens X.carrier} {hU : (U : Set X.carrier).Nonempty}
    (P : (X.restrict U hU).carrier) :
    NonsingularAt (X.restrict U hU) P ↔ NonsingularAt X P.1 := by
  exact isRegularLocalRing_iff_of_ringEquiv (localRingEquivRestrict P)

/-- An isomorphism of varieties preserves nonsingularity at corresponding
points. -/
theorem nonsingularAt_iff_of_isIso {X Z : Variety.{u, v} k}
    {f : VarietyHom X Z} (hf : f.IsIso) (P : X.carrier) :
    NonsingularAt X P ↔ NonsingularAt Z (f P) := by
  let e : LocalRingAt Z (f P) ≃+* LocalRingAt X P :=
    RingEquiv.ofBijective (f.localRingHom P)
      (VarietyHom.bijective_localRingHom_of_isIso hf P)
  exact (isRegularLocalRing_iff_of_ringEquiv e).symm

/-- Isomorphic varieties are simultaneously nonsingular. -/
theorem nonsingular_iff_of_isIso {X Z : Variety.{u, v} k}
    {f : VarietyHom X Z} (hf : f.IsIso) :
    Nonsingular X ↔ Nonsingular Z := by
  constructor
  · intro hX Q
    obtain ⟨P, rfl⟩ := hf.bijective.surjective Q
    exact (nonsingularAt_iff_of_isIso hf P).mp (hX P)
  · intro hZ P
    exact (nonsingularAt_iff_of_isIso hf P).mpr (hZ (f P))

end Variety

section Affine

variable [IsAlgClosed k] {σ : Type v} [Finite σ] {Y : Set (σ → k)}

/-- On an affine variety, intrinsic nonsingularity agrees with the Jacobian
definition. -/
theorem nonsingularAt_affine_iff (hY : IsAffineVariety Y)
    (P : (Variety.ofQuasiAffine hY.isQuasiAffineVariety).carrier) :
    Variety.NonsingularAt (Variety.ofQuasiAffine hY.isQuasiAffineVariety) P ↔
      IsAffineNonsingularAt Y
        (affinePoint hY.isQuasiAffineVariety P) := by
  rw [Variety.NonsingularAt,
    isAffineNonsingularAt_iff_isRegularLocalRing hY]
  exact isRegularLocalRing_iff_of_ringEquiv
    (localRingEquivAffine hY.isQuasiAffineVariety P)

end Affine

end Hartshorne

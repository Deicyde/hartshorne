/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Rational.RationalMapFunctionFieldEquivalence
import Hartshorne.Nonsingular.LocalRingOpen

/-!
# Local rings inside the function field

Hartshorne, *Algebraic Geometry*, I.6 (p. 41).

For a variety admitting an affine-open basis, its function field is the
fraction field of the local ring at every point.  This file also installs the
canonical domain and algebra structures needed to express that result.
-/

namespace Hartshorne

universe u v

variable {k : Type u} [Field k]

open TopologicalSpace

namespace Variety

/-- The local ring of a variety at any point is a domain. -/
noncomputable instance instIsDomainLocalRingAt
    (X : Variety.{u, v} k) (P : X.carrier) : IsDomain (X.LocalRingAt P) :=
  (X.localToFunctionFieldAlgHom_injective P).isDomain
    (X.localToFunctionFieldAlgHom P)

end Variety

namespace VarietyHom

variable {X Y : Variety.{u, v} k}

/-- The map on function fields induced by a dominant morphism is compatible
with the maps from the corresponding local rings. -/
theorem functionFieldHom_localToFunctionFieldAlgHom
    (f : VarietyHom X Y) (hd : Dense (Set.range f.toFun))
    (P : X.carrier) (a : Y.LocalRingAt (f P)) :
    f.functionFieldHom hd (Y.localToFunctionFieldAlgHom (f P) a) =
      X.localToFunctionFieldAlgHom P (f.localRingHom P a) := by
  refine Quotient.inductionOn a ?_
  intro r
  exact Quotient.sound fun _ _ _ => rfl

end VarietyHom

namespace Variety

/-- The canonical algebra structure of the function field over a local ring. -/
noncomputable instance instAlgebraLocalRingAtFunctionField
    (X : Variety.{u, v} k) (P : X.carrier) :
    Algebra (X.LocalRingAt P) X.FunctionField :=
  (X.localToFunctionFieldAlgHom P).toRingHom.toAlgebra

instance instIsScalarTowerLocalRingAtFunctionField
    (X : Variety.{u, v} k) (P : X.carrier) :
    IsScalarTower k (X.LocalRingAt P) X.FunctionField :=
  IsScalarTower.of_algebraMap_eq fun c =>
    (X.localToFunctionFieldAlgHom P).commutes c |>.symm

instance instFaithfulSMulLocalRingAtFunctionField
    (X : Variety.{u, v} k) (P : X.carrier) :
    FaithfulSMul (X.LocalRingAt P) X.FunctionField :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (X.localToFunctionFieldAlgHom_injective P)

end Variety

/-- The affine function-field equivalence is compatible with the canonical
map out of a local ring. -/
theorem functionFieldEquivAffine_localToFunctionField
    {σ : Type*} {Y : Set (σ → k)} (hY : IsQuasiAffineVariety Y)
    (P : (Variety.ofQuasiAffine hY).carrier)
    (a : (Variety.ofQuasiAffine hY).LocalRingAt P) :
    functionFieldEquivAffine hY
        ((Variety.ofQuasiAffine hY).localToFunctionFieldAlgHom P a) =
      localToFunctionField hY.isIrreducible (affinePoint hY P)
        (localRingEquivAffine hY P a) := by
  refine Quotient.inductionOn a ?_
  intro r
  rfl

/-- A coordinate-ring element has the same image in the affine function field
whether it is mapped directly or first viewed in a local ring. -/
theorem localToFunctionField_coordToLocal
    {σ : Type*} {Y : Set (σ → k)} (hY : IsQuasiAffineVariety Y)
    (P : Y) (a : coordinateRing Y) :
    localToFunctionField hY.isIrreducible P (coordToLocal hY.isIrreducible P a) =
      coordToRational hY.isIrreducible a := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  rfl

/-- The function-field equivalence for restriction to an open is compatible
with the canonical maps from local rings. -/
theorem RationalMapFunctionField.openFunctionFieldAlgEquiv_localToFunctionField
    {X : Variety k} (U : Opens X.carrier)
    (hU : (U : Set X.carrier).Nonempty)
    (P : (X.restrict U hU).carrier)
    (a : (X.restrict U hU).LocalRingAt P) :
    RationalMapFunctionField.openFunctionFieldAlgEquiv X U hU
        (X.localToFunctionFieldAlgHom P.1
          (Variety.localRingEquivRestrict P a)) =
      (X.restrict U hU).localToFunctionFieldAlgHom P a := by
  let j := X.inclHom U hU
  have hnat := VarietyHom.functionFieldHom_localToFunctionFieldAlgHom
    j (X.dense_range_inclHom_open U hU) P
      (Variety.localRingEquivRestrict P a)
  rw [show j.localRingHom P (Variety.localRingEquivRestrict P a) = a by
    exact (Variety.localRingEquivRestrict P).symm_apply_apply a] at hnat
  exact hnat

/-- The function-field equivalence induced by an isomorphism is compatible
with the canonical maps from local rings. -/
theorem RationalMapFunctionField.functionFieldAlgEquivOfIsIso_localToFunctionField
    {X Y : Variety k} (f : VarietyHom X Y) (hf : f.IsIso)
    (P : X.carrier) (a : Y.LocalRingAt (f P)) :
    (RationalMapFunctionField.functionFieldAlgEquivOfIsIso f hf).symm
        (X.localToFunctionFieldAlgHom P (f.localRingHom P a)) =
      Y.localToFunctionFieldAlgHom (f P) a := by
  let e := RationalMapFunctionField.functionFieldAlgEquivOfIsIso f hf
  apply e.injective
  rw [e.apply_symm_apply]
  exact (VarietyHom.functionFieldHom_localToFunctionFieldAlgHom
    f hf.bijective.2.denseRange P a).symm

/-- On an affine variety, the function field is the fraction field of every
local ring. -/
theorem isFractionRing_localRingAt_ofQuasiAffine
    [IsAlgClosed k] {σ : Type*} [Finite σ] {Y : Set (σ → k)}
    (hY : IsAffineVariety Y)
    (P : (Variety.ofQuasiAffine hY.isQuasiAffineVariety).carrier) :
    IsFractionRing
      ((Variety.ofQuasiAffine hY.isQuasiAffineVariety).LocalRingAt P)
      (Variety.ofQuasiAffine hY.isQuasiAffineVariety).FunctionField := by
  let X := Variety.ofQuasiAffine hY.isQuasiAffineVariety
  apply IsFractionRing.of_field
  intro z
  let eK := functionFieldEquivAffine hY.isQuasiAffineVariety
  let eL := localRingEquivAffine hY.isQuasiAffineVariety P
  let _ : IsDomain (coordinateRing Y) := isDomain_coordinateRing hY
  let _ : IsFractionRing (coordinateRing Y) (FunctionField hY.isIrreducible) :=
    isFractionRing_functionField hY.isIrreducible
  let _ : Field (FunctionField hY.isIrreducible) :=
    IsFractionRing.toField (coordinateRing Y)
  obtain ⟨a, b, -, hab⟩ := IsFractionRing.div_surjective (coordinateRing Y) (eK z)
  refine ⟨eL.symm (coordToLocal hY.isIrreducible (affinePoint _ P) a),
    eL.symm (coordToLocal hY.isIrreducible (affinePoint _ P) b), ?_⟩
  apply eK.injective
  rw [map_div₀]
  rw [show eK (algebraMap (X.LocalRingAt P) X.FunctionField
        (eL.symm (coordToLocal hY.isIrreducible (affinePoint _ P) a))) =
      coordToRational hY.isIrreducible a by
    change eK (X.localToFunctionFieldAlgHom P
      (eL.symm (coordToLocal hY.isIrreducible (affinePoint _ P) a))) = _
    rw [functionFieldEquivAffine_localToFunctionField]
    rw [eL.apply_symm_apply]
    exact localToFunctionField_coordToLocal hY.isQuasiAffineVariety (affinePoint _ P) a]
  rw [show eK (algebraMap (X.LocalRingAt P) X.FunctionField
        (eL.symm (coordToLocal hY.isIrreducible (affinePoint _ P) b))) =
      coordToRational hY.isIrreducible b by
    change eK (X.localToFunctionFieldAlgHom P
      (eL.symm (coordToLocal hY.isIrreducible (affinePoint _ P) b))) = _
    rw [functionFieldEquivAffine_localToFunctionField]
    rw [eL.apply_symm_apply]
    exact localToFunctionField_coordToLocal hY.isQuasiAffineVariety (affinePoint _ P) b]
  exact hab.symm

/-- The function field of a variety admitting an affine-open basis is the
fraction field of its local ring at every point. -/
theorem Variety.HasAffineOpenBasis.isFractionRing_localRingAt
    [IsAlgClosed k] {X : Variety k} (hX : X.HasAffineOpenBasis)
    (P : X.carrier) :
    IsFractionRing (X.LocalRingAt P) X.FunctionField := by
  obtain ⟨V, hV, hPV, -, σ, hσ, Z, hZ, φ, hφ⟩ := hX ⊤ P trivial
  let _ : Finite σ := hσ
  let Q : (X.restrict V hV).carrier := ⟨P, hPV⟩
  let A := Variety.ofQuasiAffine hZ.isQuasiAffineVariety
  let eOpenK := RationalMapFunctionField.openFunctionFieldAlgEquiv X V hV
  let eIsoK := (RationalMapFunctionField.functionFieldAlgEquivOfIsIso φ hφ).symm
  let eK := eOpenK.trans eIsoK
  let eOpenL := Variety.localRingEquivRestrict Q
  let eIsoL : A.LocalRingAt (φ Q) ≃+* (X.restrict V hV).LocalRingAt Q :=
    RingEquiv.ofBijective (φ.localRingHom Q)
      (VarietyHom.bijective_localRingHom_of_isIso hφ Q)
  let eL := eIsoL.trans eOpenL
  let _ : IsFractionRing (A.LocalRingAt (φ Q)) A.FunctionField :=
    isFractionRing_localRingAt_ofQuasiAffine hZ (φ Q)
  apply IsFractionRing.of_field
  intro z
  obtain ⟨a, b, -, hab⟩ :=
    IsFractionRing.div_surjective (A.LocalRingAt (φ Q)) (eK z)
  refine ⟨eL a, eL b, ?_⟩
  apply eK.injective
  rw [map_div₀]
  change eK z = eK (X.localToFunctionFieldAlgHom P (eL a)) /
    eK (X.localToFunctionFieldAlgHom P (eL b))
  have hcompat (c : A.LocalRingAt (φ Q)) :
      eK (X.localToFunctionFieldAlgHom P (eL c)) =
        A.localToFunctionFieldAlgHom (φ Q) c := by
    change eIsoK (eOpenK (X.localToFunctionFieldAlgHom Q.1
      (eOpenL (eIsoL c)))) = _
    rw [RationalMapFunctionField.openFunctionFieldAlgEquiv_localToFunctionField]
    exact RationalMapFunctionField.functionFieldAlgEquivOfIsIso_localToFunctionField
      φ hφ Q c
  rw [hcompat a, hcompat b]
  exact hab.symm

end Hartshorne

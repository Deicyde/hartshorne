/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Curve.DVRAffineModel
import Hartshorne.Nonsingular.DefiningIdealCotangent

/-!
# Residue fields of function-field DVRs

Hartshorne, *Algebraic Geometry*, I.6 (p. 42).

For a one-dimensional function field over an algebraically closed field, the
residue field of every function-field DVR is canonically identified with the
constant field.  The associated residue evaluation agrees with evaluation at
the point in any compatible nonsingular affine model.
-/

namespace Hartshorne

noncomputable section

universe u v

namespace FunctionFieldDVR

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

/-- Corollary 6.6 supplies an identification of the residue field of a
function-field DVR with the constant field. -/
private theorem nonempty_residueFieldAlgEquiv [IsAlgClosed k]
    [Algebra.EssFiniteType k K]
    (htrdeg : Algebra.trdeg k K = 1) (R : FunctionFieldDVR k K) :
    Nonempty
      (IsLocalRing.ResidueField R.toValuationSubring ≃ₐ[k] k) := by
  obtain ⟨n, Y, hY, P, _, eR, _, _, _⟩ :=
    R.exists_nonsingular_affine_model htrdeg
  exact ⟨(IsLocalRing.ResidueField.mapAlgEquiv eR).symm.trans
    (Hartshorne.residueFieldAlgEquiv (hY := hY.isIrreducible) (P := P))⟩

/-- There is at most one `k`-algebra equivalence from a function-field DVR's
residue field to `k`. -/
private theorem residueFieldAlgEquiv_unique
    (R : FunctionFieldDVR k K)
    (e f : IsLocalRing.ResidueField R.toValuationSubring ≃ₐ[k] k) :
    e = f := by
  ext y
  have hy : algebraMap k (IsLocalRing.ResidueField R.toValuationSubring)
      (e y) = y := by
    apply e.injective
    simp
  rw [← hy]
  simp

/-- The canonical identification of the residue field of a function-field
DVR with the algebraically closed constant field. -/
noncomputable def residueFieldEquiv [IsAlgClosed k]
    [Algebra.EssFiniteType k K]
    (htrdeg : Algebra.trdeg k K = 1) (R : FunctionFieldDVR k K) :
    IsLocalRing.ResidueField R.toValuationSubring ≃ₐ[k] k :=
  Classical.choice (nonempty_residueFieldAlgEquiv htrdeg R)

/-- The canonical residue evaluation: first pass to the residue field, then
identify that residue field with the constant field. -/
noncomputable def residueAt [IsAlgClosed k]
    [Algebra.EssFiniteType k K]
    (htrdeg : Algebra.trdeg k K = 1) (R : FunctionFieldDVR k K) :
    R.toValuationSubring →ₐ[k] k :=
  (residueFieldEquiv htrdeg R).toAlgHom.comp
    (IsScalarTower.toAlgHom k R.toValuationSubring
      (IsLocalRing.ResidueField R.toValuationSubring))

/-- Residue evaluation fixes the constant field. -/
@[simp]
theorem residueAt_algebraMap [IsAlgClosed k]
    [Algebra.EssFiniteType k K]
    (htrdeg : Algebra.trdeg k K = 1) (R : FunctionFieldDVR k K)
    (c : k) :
    residueAt htrdeg R (algebraMap k R.toValuationSubring c) = c :=
  (residueAt htrdeg R).commutes c

/-- The canonical residue-field equivalence is the one transported through
any affine-model equivalence supplied by Corollary 6.6. -/
theorem residueFieldEquiv_eq_of_affineModel [IsAlgClosed k]
    [Algebra.EssFiniteType k K]
    (htrdeg : Algebra.trdeg k K = 1) (R : FunctionFieldDVR k K)
    {n : ℕ} {Y : Set (Fin n → k)} (hY : IsAffineVariety Y) (P : Y)
    (eR : LocalRingAt hY.isIrreducible P ≃ₐ[k]
      R.toValuationSubring) :
    residueFieldEquiv htrdeg R =
      (IsLocalRing.ResidueField.mapAlgEquiv eR).symm.trans
        (Hartshorne.residueFieldAlgEquiv
          (hY := hY.isIrreducible) (P := P)) :=
  residueFieldAlgEquiv_unique R _ _

/-- In the affine model of Corollary 6.6, residue evaluation is pointwise
evaluation at the corresponding rational point.  The statement uses the same
affine variety, point, and local-ring equivalence as that model theorem. -/
@[simp]
theorem residueAt_affineModel [IsAlgClosed k]
    [Algebra.EssFiniteType k K]
    (htrdeg : Algebra.trdeg k K = 1) (R : FunctionFieldDVR k K)
    {n : ℕ} {Y : Set (Fin n → k)} (hY : IsAffineVariety Y) (P : Y)
    (eR : LocalRingAt hY.isIrreducible P ≃ₐ[k]
      R.toValuationSubring)
    (z : LocalRingAt hY.isIrreducible P) :
    residueAt htrdeg R (eR z) = evalAtPoint z := by
  rw [residueAt, residueFieldEquiv_eq_of_affineModel htrdeg R hY P eR]
  have hresidue :
      (IsLocalRing.ResidueField.mapAlgEquiv eR).symm
          (IsLocalRing.residue R.toValuationSubring (eR z)) =
        IsLocalRing.residue (LocalRingAt hY.isIrreducible P) z := by
    apply (IsLocalRing.ResidueField.mapAlgEquiv eR).injective
    simp
  change (Hartshorne.residueFieldAlgEquiv
      (hY := hY.isIrreducible) (P := P))
        ((IsLocalRing.ResidueField.mapAlgEquiv eR).symm
          (IsLocalRing.residue R.toValuationSubring (eR z))) =
    evalAtPoint z
  rw [hresidue]
  exact Hartshorne.residueFieldAlgEquiv_mk z

end FunctionFieldDVR

end

end Hartshorne

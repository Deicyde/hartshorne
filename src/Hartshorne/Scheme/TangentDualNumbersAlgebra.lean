/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.DualNumber
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.DualNumber
import Mathlib.RingTheory.Ideal.Cotangent

/-!
# Tangent vectors and dual-number lifts: the local algebra

This file packages the algebraic heart of Hartshorne II, Exercise 2.8.  For a local `k`-algebra
with a `k`-rational residue map `ρ : A →ₐ[k] k`, linear functionals on `𝔪 / 𝔪²`, `k`-derivations
`A → k`, and lifts `A →ₐ[k] k[ε]` of `ρ` are naturally equivalent.
-/

namespace Hartshorne

open IsLocalRing TrivSqZeroExt

universe u

variable {k A : Type u} [Field k] [CommRing A] [IsLocalRing A] [Algebra k A]

/-- The `k`-algebra maps to the dual numbers whose reduction is `ρ`. -/
def DualNumberLocalLift (ρ : A →ₐ[k] k) :=
  { φ : A →ₐ[k] DualNumber k // (fstHom k k k).comp φ = ρ }

omit [IsLocalRing A] in
private lemma residueAlgHom_surjective (ρ : A →ₐ[k] k) : Function.Surjective ρ := by
  intro r
  exact ⟨algebraMap k A r, by simp⟩

private lemma residueAlgHom_ker (ρ : A →ₐ[k] k) [IsLocalHom ρ] :
    RingHom.ker ρ.toRingHom = maximalIdeal A :=
  IsLocalRing.ker_eq_maximalIdeal ρ.toRingHom (residueAlgHom_surjective ρ)

/-- The maximal-ideal part of an element, obtained by subtracting its scalar residue. -/
private noncomputable def maximalIdealPart (ρ : A →ₐ[k] k) [IsLocalHom ρ] :
    A →ₗ[k] maximalIdeal A where
  toFun a := ⟨a - algebraMap k A (ρ a), by
    rw [← residueAlgHom_ker ρ, RingHom.mem_ker]
    simp⟩
  map_add' a b := by
    ext
    simp
    ring
  map_smul' r a := by
    ext
    simp [Algebra.smul_def]
    ring

private lemma maximalIdealPart_toCotangent_mul
    (ρ : A →ₐ[k] k) [IsLocalHom ρ] (a b : A) :
    (maximalIdeal A).toCotangent (maximalIdealPart ρ (a * b)) =
      ρ a • (maximalIdeal A).toCotangent (maximalIdealPart ρ b) +
        ρ b • (maximalIdeal A).toCotangent (maximalIdealPart ρ a) := by
  let q := (maximalIdeal A).toCotangent.restrictScalars k
  change q (maximalIdealPart ρ (a * b)) =
    ρ a • q (maximalIdealPart ρ b) + ρ b • q (maximalIdealPart ρ a)
  rw [← q.map_smul, ← q.map_smul, ← q.map_add]
  apply (maximalIdeal A).toCotangent_eq.mpr
  rw [pow_two]
  convert Ideal.mul_mem_mul (maximalIdealPart ρ a).2 (maximalIdealPart ρ b).2 using 1
  dsimp [maximalIdealPart]
  simp only [Algebra.smul_def, map_mul]
  ring

/-- Derivations with the `A`-module structure on `k` induced by `ρ`. -/
abbrev ResidueDerivation (ρ : A →ₐ[k] k) :=
  letI : Algebra A k := ρ.toRingHom.toAlgebra
  Derivation k A k

section ResidueAction

variable (ρ : A →ₐ[k] k) [IsLocalHom ρ]

/-- A cotangent functional gives a derivation by taking the maximal-ideal part of each element. -/
private noncomputable def cotangentDualToDerivation
    (l : CotangentSpace A →ₗ[k] k) : ResidueDerivation ρ := by
  letI : Algebra A k := ρ.toRingHom.toAlgebra
  let f : A →ₗ[k] k := l.comp
    (((maximalIdeal A).toCotangent.restrictScalars k).comp (maximalIdealPart ρ))
  refine Derivation.mk' f fun a b ↦ ?_
  change l ((maximalIdeal A).toCotangent (maximalIdealPart ρ (a * b))) =
    a • l ((maximalIdeal A).toCotangent (maximalIdealPart ρ b)) +
      b • l ((maximalIdeal A).toCotangent (maximalIdealPart ρ a))
  rw [maximalIdealPart_toCotangent_mul ρ, map_add, map_smul, map_smul]
  rfl

/-- A derivation restricts to the maximal ideal and annihilates its square. -/
private noncomputable def derivationToCotangentDual
    (d : ResidueDerivation ρ) : CotangentSpace A →ₗ[k] k := by
  letI : Algebra A k := ρ.toRingHom.toAlgebra
  let f : maximalIdeal A →ₗ[k] k :=
    d.toLinearMap.comp ((maximalIdeal A).subtype.restrictScalars k)
  refine Ideal.Cotangent.lift f fun x y ↦ ?_
  have hx : ρ (x : A) = 0 := by
    rw [← RingHom.mem_ker]
    change (x : A) ∈ RingHom.ker ρ.toRingHom
    rw [residueAlgHom_ker ρ]
    exact x.2
  have hy : ρ (y : A) = 0 := by
    rw [← RingHom.mem_ker]
    change (y : A) ∈ RingHom.ker ρ.toRingHom
    rw [residueAlgHom_ker ρ]
    exact y.2
  change d ((x : A) * (y : A)) = 0
  rw [d.leibniz]
  change ρ (x : A) * d (y : A) + ρ (y : A) * d (x : A) = 0
  simp [hx, hy]

/-- Linear functionals on `𝔪 / 𝔪²` are naturally equivalent to `k`-derivations to the residue
field. -/
noncomputable def cotangentDualEquivDerivation :
    (CotangentSpace A →ₗ[k] k) ≃ ResidueDerivation ρ where
  toFun := cotangentDualToDerivation ρ
  invFun := derivationToCotangentDual ρ
  left_inv l := by
    let _ : Algebra A k := ρ.toRingHom.toAlgebra
    ext z
    obtain ⟨z, rfl⟩ := (maximalIdeal A).toCotangent_surjective z
    dsimp [derivationToCotangentDual, cotangentDualToDerivation]
    change l ((maximalIdeal A).toCotangent (maximalIdealPart ρ (z : A))) =
      l ((maximalIdeal A).toCotangent z)
    apply l.congr_arg
    apply (maximalIdeal A).toCotangent_eq.mpr
    have hz : ρ (z : A) = 0 := by
      rw [← RingHom.mem_ker]
      change (z : A) ∈ RingHom.ker ρ.toRingHom
      rw [residueAlgHom_ker ρ]
      exact z.2
    simp [maximalIdealPart, hz]
  right_inv d := by
    let _ : Algebra A k := ρ.toRingHom.toAlgebra
    ext a
    dsimp [cotangentDualToDerivation, derivationToCotangentDual]
    change d ((maximalIdealPart ρ a : maximalIdeal A) : A) = d a
    simp [maximalIdealPart]

/-- A derivation determines the `ε`-coefficient of a lift to the dual numbers. -/
private noncomputable def derivationToDualNumberLocalLift
    (d : ResidueDerivation ρ) : DualNumberLocalLift ρ := by
  letI : Algebra A k := ρ.toRingHom.toAlgebra
  let φ : A →ₐ[k] DualNumber k :=
    { toFun := fun a ↦ (ρ a, d a)
      map_one' := by
        apply TrivSqZeroExt.ext
        · exact ρ.map_one
        · exact d.map_one_eq_zero
      map_mul' := fun a b ↦ by
        apply TrivSqZeroExt.ext
        · exact ρ.map_mul a b
        · change d (a * b) = ρ a * d b + d a * ρ b
          rw [d.leibniz]
          change ρ a * d b + ρ b * d a = ρ a * d b + d a * ρ b
          ring
      map_zero' := by
        apply TrivSqZeroExt.ext
        · exact ρ.map_zero
        · exact d.map_zero
      map_add' := fun a b ↦ by
        apply TrivSqZeroExt.ext
        · exact ρ.map_add a b
        · exact d.map_add a b
      commutes' := fun r ↦ by
        apply TrivSqZeroExt.ext
        · change ρ (algebraMap k A r) = r
          simp
        · simp [TrivSqZeroExt.algebraMap_eq_inl'] }
  exact ⟨φ, by ext; rfl⟩

/-- The `ε`-coefficient of a dual-number lift is a derivation. -/
private noncomputable def dualNumberLocalLiftToDerivation
    (φ : DualNumberLocalLift ρ) : ResidueDerivation ρ := by
  letI : Algebra A k := ρ.toRingHom.toAlgebra
  let f : A →ₗ[k] k := (sndHom k k).comp φ.1.toLinearMap
  refine Derivation.mk' f fun a b ↦ ?_
  have ha := DFunLike.congr_fun φ.2 a
  have hb := DFunLike.congr_fun φ.2 b
  change snd (φ.1 (a * b)) = a • snd (φ.1 b) + b • snd (φ.1 a)
  rw [map_mul, DualNumber.snd_mul]
  change fst (φ.1 a) * snd (φ.1 b) + snd (φ.1 a) * fst (φ.1 b) =
    ρ a * snd (φ.1 b) + ρ b * snd (φ.1 a)
  simp only [AlgHom.coe_comp, Function.comp_apply] at ha hb
  change fst (φ.1 a) = ρ a at ha
  change fst (φ.1 b) = ρ b at hb
  rw [ha, hb]
  ring

/-- Derivations are naturally equivalent to lifts of the residue map to the dual numbers. -/
noncomputable def derivationEquivDualNumberLocalLift :
    ResidueDerivation ρ ≃ DualNumberLocalLift ρ where
  toFun := derivationToDualNumberLocalLift ρ
  invFun := dualNumberLocalLiftToDerivation ρ
  left_inv d := by
    let _ : Algebra A k := ρ.toRingHom.toAlgebra
    ext a
    change d a = d a
    rfl
  right_inv φ := by
    let _ : Algebra A k := ρ.toRingHom.toAlgebra
    apply Subtype.ext
    ext a
    · change ρ a = (fstHom k k k) (φ.1 a)
      exact (DFunLike.congr_fun φ.2 a).symm
    · change snd (φ.1 a) = snd (φ.1 a)
      rfl

/-- Dual-number lifts of a rational residue map are naturally equivalent to cotangent vectors. -/
noncomputable def dualNumberLocalLiftEquivCotangentDual :
    DualNumberLocalLift ρ ≃ (CotangentSpace A →ₗ[k] k) :=
  (derivationEquivDualNumberLocalLift ρ).symm.trans (cotangentDualEquivDerivation ρ).symm

end ResidueAction

end Hartshorne

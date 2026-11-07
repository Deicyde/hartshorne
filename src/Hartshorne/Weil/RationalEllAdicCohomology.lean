/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.RightDerivedLongExactSequence
import Hartshorne.Weil.ClassicalEllAdicCohomology
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Rational `ℓ`-adic cohomology

For a scheme `X`, a prime `ℓ` and a degree `i`, the classical integral group
`H^i_classical(X, ℤ_ℓ) = lim_r H^i_et(X, ℤ/ℓ^r)` of
`Hartshorne.Weil.ClassicalEllAdicCohomology` is a plain abelian group.  This file makes it a
module over Mathlib's `ℓ`-adic integers `ℤ_[ℓ]` and defines

`H^i_et(X, ℚ_ℓ) = H^i_classical(X, ℤ_ℓ) ⊗_{ℤ_ℓ} ℚ_ℓ`

as a `ℚ_[ℓ]`-module.

## The `ℤ_ℓ`-module structure

Multiplication by `ℓ^r` is zero on the constant sheaf `ℤ/ℓ^r`, and the right derived functors
of global sections are additive, so `ℓ^r` kills `H^i_et(X, ℤ/ℓ^r)`.  Hence an `ℓ`-adic integer
`a` acts on `H^i_et(X, ℤ/ℓ^r)` as multiplication by any natural number lifting its reduction
`a mod ℓ^r`; we use the canonical lift `(PadicInt.toZModPow r a).val`.  These actions commute
with the transition maps of the inverse system, so they define an action on the inverse limit,
characterised by `classicalEllAdicCohomology_π_smul`.  The underlying abelian group is the
existing `classicalEllAdicCohomology`, unchanged.

## The tensor product

Mathlib's tensor product `ℚ_[ℓ] ⊗[ℤ_[ℓ]] M` carries its `ℚ_[ℓ]`-module structure through the
left factor, so the definition below writes the scalar extension with `ℚ_[ℓ]` on the left; it
is canonically isomorphic to `M ⊗[ℤ_[ℓ]] ℚ_[ℓ]` by commutativity of the tensor product.

## Hypotheses

The construction needs `ℓ` prime (for Mathlib's `ℤ_[ℓ]` and `ℚ_[ℓ]`) but not that `ℓ` is
invertible on `X`; as for the constant torsion sheaves and the classical inverse system, that
hypothesis enters only the later theorems about `ℓ`-adic cohomology.
-/

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

universe u

variable (X : Scheme.{u}) (ℓ : ℕ)

/-- Multiplication by `ℓ ^ r` is zero on the constant sheaf `ℤ/ℓ^r` on the small étale site. -/
theorem constantTorsionEtaleSheaf_pow_nsmul_id (r : ℕ) :
    (ℓ ^ r) • 𝟙 (X.constantTorsionEtaleSheaf ℓ r) = 0 := by
  have h : (ℓ ^ r) • 𝟙 (AddCommGrpCat.of (ZMod (ℓ ^ r))) = 0 := by
    ext x
    simp
  unfold constantTorsionEtaleSheaf
  rw [← CategoryTheory.Functor.map_id, ← CategoryTheory.Functor.map_id,
    ← CategoryTheory.Functor.map_nsmul, ← CategoryTheory.Functor.map_nsmul, h,
    CategoryTheory.Functor.map_zero, CategoryTheory.Functor.map_zero]

/-- Multiplication by `ℓ ^ r` is zero on `H^i_et(X, ℤ/ℓ^r)`. -/
theorem torsionEtaleCohomology_pow_nsmul_id (r i : ℕ) :
    (ℓ ^ r) • 𝟙 (X.torsionEtaleCohomology ℓ r i) = 0 := by
  unfold torsionEtaleCohomology
  rw [← CategoryTheory.Functor.map_id, ← CategoryTheory.Functor.map_nsmul,
    constantTorsionEtaleSheaf_pow_nsmul_id, CategoryTheory.Functor.map_zero]

/-- On `H^i_et(X, ℤ/ℓ^r)`, multiplication by a natural number depends only on its class
modulo `ℓ ^ r`. -/
theorem torsionEtaleCohomology_nsmul_id_congr {r i m n : ℕ}
    (h : (m : ZMod (ℓ ^ r)) = n) :
    m • 𝟙 (X.torsionEtaleCohomology ℓ r i) = n • 𝟙 (X.torsionEtaleCohomology ℓ r i) := by
  have key : ∀ k : ℕ, k • 𝟙 (X.torsionEtaleCohomology ℓ r i) =
      (k % ℓ ^ r) • 𝟙 (X.torsionEtaleCohomology ℓ r i) := fun k ↦ by
    conv_lhs => rw [← Nat.mod_add_div k (ℓ ^ r)]
    rw [add_nsmul, mul_comm (ℓ ^ r), mul_smul, X.torsionEtaleCohomology_pow_nsmul_id,
      smul_zero, add_zero]
  rw [key m, key n, (ZMod.natCast_eq_natCast_iff' m n (ℓ ^ r)).mp h]

variable [Fact ℓ.Prime]

/-- The canonical natural-number lift of the reduction of an `ℓ`-adic integer modulo `ℓ ^ r`
reduces back to it. -/
private theorem natCast_val_toZModPow (r : ℕ) (a : ℤ_[ℓ]) :
    ((PadicInt.toZModPow r a).val : ZMod (ℓ ^ r)) = PadicInt.toZModPow r a :=
  have : NeZero (ℓ ^ r) := ⟨pow_ne_zero r (Fact.out : ℓ.Prime).ne_zero⟩
  ZMod.natCast_zmod_val _

/-- The action of the `ℓ`-adic integers on `H^i_et(X, ℤ/ℓ^r)`: an `ℓ`-adic integer acts as
multiplication by the canonical natural-number lift of its reduction modulo `ℓ ^ r`. -/
noncomputable def torsionEtaleCohomologyPadicIntAction (r i : ℕ) :
    ℤ_[ℓ] →+* End (X.torsionEtaleCohomology ℓ r i) where
  toFun a := (PadicInt.toZModPow r a).val • 𝟙 _
  map_one' := by
    refine (X.torsionEtaleCohomology_nsmul_id_congr ℓ (n := 1) ?_).trans (one_smul ℕ _)
    rw [natCast_val_toZModPow, map_one, Nat.cast_one]
  map_mul' a b := by
    rw [End.mul_def, Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.id_comp,
      ← mul_smul]
    refine X.torsionEtaleCohomology_nsmul_id_congr ℓ ?_
    rw [Nat.cast_mul, natCast_val_toZModPow, natCast_val_toZModPow, natCast_val_toZModPow,
      map_mul, mul_comm]
  map_zero' := by
    change (PadicInt.toZModPow r 0).val • 𝟙 _ = 0
    rw [map_zero, ZMod.val_zero, zero_smul]
  map_add' a b := by
    refine (X.torsionEtaleCohomology_nsmul_id_congr ℓ (n := _ + _) ?_).trans (add_nsmul _ _ _)
    rw [Nat.cast_add, natCast_val_toZModPow, natCast_val_toZModPow, natCast_val_toZModPow,
      map_add]

theorem torsionEtaleCohomologyPadicIntAction_apply (r i : ℕ) (a : ℤ_[ℓ]) :
    X.torsionEtaleCohomologyPadicIntAction ℓ r i a = (PadicInt.toZModPow r a).val • 𝟙 _ :=
  rfl

/-- The action of `ℤ_[ℓ]` on the groups `H^i_et(X, ℤ/ℓ^r)` commutes with every morphism
`H^i_et(X, ℤ/ℓ^s) ⟶ H^i_et(X, ℤ/ℓ^r)` of abelian groups, for `r ≤ s`. -/
theorem comp_torsionEtaleCohomologyPadicIntAction {r s i : ℕ} (h : r ≤ s)
    (g : X.torsionEtaleCohomology ℓ s i ⟶ X.torsionEtaleCohomology ℓ r i) (a : ℤ_[ℓ]) :
    g ≫ X.torsionEtaleCohomologyPadicIntAction ℓ r i a =
      X.torsionEtaleCohomologyPadicIntAction ℓ s i a ≫ g := by
  have hcast : ((PadicInt.toZModPow s a).val : ZMod (ℓ ^ r)) =
      ((PadicInt.toZModPow r a).val : ZMod (ℓ ^ r)) := by
    have : NeZero (ℓ ^ s) := ⟨pow_ne_zero s (Fact.out : ℓ.Prime).ne_zero⟩
    rw [natCast_val_toZModPow, ZMod.natCast_val, ← ZMod.castHom_apply (h := pow_dvd_pow ℓ h)]
    exact RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow r s h) a
  have e := congrArg (g ≫ ·) (X.torsionEtaleCohomology_nsmul_id_congr ℓ (i := i) hcast)
  simp only [Preadditive.comp_nsmul, Category.comp_id] at e
  rw [torsionEtaleCohomologyPadicIntAction_apply, torsionEtaleCohomologyPadicIntAction_apply,
    Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.comp_id, Category.id_comp]
  exact e.symm

/-- The action of `ℤ_[ℓ]` on the classical inverse system `r ↦ H^i_et(X, ℤ/ℓ^r)`. -/
noncomputable def torsionEtaleCohomologySystemPadicIntAction (i : ℕ) :
    ℤ_[ℓ] →+* End (X.torsionEtaleCohomologySystem ℓ i) where
  toFun a :=
    { app r := X.torsionEtaleCohomologyPadicIntAction ℓ r.unop i a
      naturality _ _ f :=
        X.comp_torsionEtaleCohomologyPadicIntAction ℓ (leOfHom f.unop) _ a }
  map_one' := by
    refine NatTrans.ext (funext fun r ↦ ?_)
    exact map_one (X.torsionEtaleCohomologyPadicIntAction ℓ r.unop i)
  map_mul' a b := by
    refine NatTrans.ext (funext fun r ↦ ?_)
    exact map_mul (X.torsionEtaleCohomologyPadicIntAction ℓ r.unop i) a b
  map_zero' := by
    refine NatTrans.ext (funext fun r ↦ ?_)
    exact map_zero (X.torsionEtaleCohomologyPadicIntAction ℓ r.unop i)
  map_add' a b := by
    refine NatTrans.ext (funext fun r ↦ ?_)
    exact map_add (X.torsionEtaleCohomologyPadicIntAction ℓ r.unop i) a b

/-- The action of `ℤ_[ℓ]` on `H^i_classical(X, ℤ_ℓ)`, induced on the inverse limit by the
actions on the stages `H^i_et(X, ℤ/ℓ^r)`. -/
noncomputable def classicalEllAdicCohomologyPadicIntAction (i : ℕ) :
    ℤ_[ℓ] →+* End (X.classicalEllAdicCohomology ℓ i) where
  toFun a := limMap (X.torsionEtaleCohomologySystemPadicIntAction ℓ i a)
  map_one' := by
    rw [map_one]
    exact lim.map_id _
  map_mul' a b := by
    rw [map_mul]
    exact lim.map_comp _ _
  map_zero' := by
    change limMap (X.torsionEtaleCohomologySystemPadicIntAction ℓ i 0) =
      (0 : limit (X.torsionEtaleCohomologySystem ℓ i) ⟶ limit _)
    refine limit.hom_ext fun r ↦ ?_
    rw [limMap_π, map_zero, NatTrans.app_zero, Limits.comp_zero, Limits.zero_comp]
  map_add' a b := by
    change limMap (X.torsionEtaleCohomologySystemPadicIntAction ℓ i (a + b)) =
      (limMap (X.torsionEtaleCohomologySystemPadicIntAction ℓ i a) +
        limMap (X.torsionEtaleCohomologySystemPadicIntAction ℓ i b) :
          limit (X.torsionEtaleCohomologySystem ℓ i) ⟶ limit _)
    refine limit.hom_ext fun r ↦ ?_
    rw [Preadditive.add_comp, limMap_π, limMap_π, limMap_π, map_add, NatTrans.app_add,
      Preadditive.comp_add]

/-- The `ℤ_[ℓ]`-module structure on `H^i_classical(X, ℤ_ℓ)`. -/
noncomputable instance classicalEllAdicCohomologyModule (i : ℕ) :
    Module ℤ_[ℓ] (X.classicalEllAdicCohomology ℓ i) where
  smul a x := (X.classicalEllAdicCohomologyPadicIntAction ℓ i a).hom x
  one_smul x := by
    change (X.classicalEllAdicCohomologyPadicIntAction ℓ i 1).hom x = x
    rw [map_one]
    rfl
  mul_smul a b x := by
    change (X.classicalEllAdicCohomologyPadicIntAction ℓ i (a * b)).hom x = _
    rw [map_mul]
    rfl
  smul_zero a := map_zero _
  smul_add a x y := map_add _ x y
  add_smul a b x := by
    change (X.classicalEllAdicCohomologyPadicIntAction ℓ i (a + b)).hom x = _
    rw [map_add]
    rfl
  zero_smul x := by
    change (X.classicalEllAdicCohomologyPadicIntAction ℓ i 0).hom x = 0
    rw [map_zero]
    rfl

/-- The projection `H^i_classical(X, ℤ_ℓ) → H^i_et(X, ℤ/ℓ^r)` sends `a • x` to the multiple of
the projection of `x` by the canonical natural-number lift of `a mod ℓ^r`. -/
theorem classicalEllAdicCohomology_π_smul (i : ℕ) (r : ℕᵒᵖ) (a : ℤ_[ℓ])
    (x : X.classicalEllAdicCohomology ℓ i) :
    (limit.π (X.torsionEtaleCohomologySystem ℓ i) r).hom (a • x) =
      (PadicInt.toZModPow r.unop a).val •
        (limit.π (X.torsionEtaleCohomologySystem ℓ i) r).hom x := by
  change (limMap (X.torsionEtaleCohomologySystemPadicIntAction ℓ i a) ≫
    limit.π (X.torsionEtaleCohomologySystem ℓ i) r).hom x = _
  rw [limMap_π]
  change (limit.π (X.torsionEtaleCohomologySystem ℓ i) r ≫
    ((PadicInt.toZModPow r.unop a).val • 𝟙 _)).hom x = _
  rw [Preadditive.comp_nsmul, Category.comp_id, AddCommGrpCat.hom_nsmul]
  rfl

/-- Rational `ℓ`-adic cohomology `H^i_et(X, ℚ_ℓ) = H^i_classical(X, ℤ_ℓ) ⊗_{ℤ_ℓ} ℚ_ℓ`, as a
`ℚ_[ℓ]`-module: the scalar extension to `ℚ_[ℓ]` of the `ℤ_[ℓ]`-module
`H^i_classical(X, ℤ_ℓ) = lim_r H^i_et(X, ℤ/ℓ^r)`. -/
noncomputable def rationalEllAdicCohomology (i : ℕ) : ModuleCat.{u} ℚ_[ℓ] :=
  ModuleCat.of ℚ_[ℓ] (TensorProduct ℤ_[ℓ] ℚ_[ℓ] (X.classicalEllAdicCohomology ℓ i))

end AlgebraicGeometry.Scheme

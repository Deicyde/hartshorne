import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Localization.FractionRing

/-!
# The rings of ℓ-adic coefficients

This file packages the standard descriptions

* `ℤ_[ℓ] = lim n, ZMod (ℓ ^ n)`, and
* `ℚ_[ℓ] = Frac(ℤ_[ℓ])`.

The inverse system is indexed by all natural numbers.  Thus its zeroth object is
`ZMod (ℓ ^ 0) = ZMod 1`, the trivial ring.  This is the harmless initial
stage of Mathlib's convention; deleting it gives Hartshorne's positive-indexed
inverse system.
-/

open CategoryTheory CategoryTheory.Limits
open Opposite

namespace Hartshorne

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The inverse system `n ↦ ZMod (ℓ ^ n)`, with reduction maps from higher
powers to lower powers. -/
noncomputable def ellAdicReductionSystem : Functor ℕᵒᵖ CommRingCat where
  obj n := CommRingCat.of (ZMod (ℓ ^ n.unop))
  map {m n} f := CommRingCat.ofHom <|
    ZMod.castHom (pow_dvd_pow ℓ (leOfHom f.unop)) (ZMod (ℓ ^ n.unop))
  map_id n := by
    apply CommRingCat.hom_ext
    exact ZMod.castHom_self
  map_comp {m n k} f g := by
    apply CommRingCat.hom_ext
    exact (ZMod.castHom_comp
      (pow_dvd_pow ℓ (leOfHom g.unop))
      (pow_dvd_pow ℓ (leOfHom f.unop))).symm

/-- The canonical cone from the ring of `ℓ`-adic integers to its finite
quotients. -/
noncomputable def padicIntLimitCone : Cone (ellAdicReductionSystem ℓ) where
  pt := CommRingCat.of ℤ_[ℓ]
  π :=
    { app := fun n ↦ CommRingCat.ofHom (PadicInt.toZModPow n.unop)
      naturality := by
        intro m n f
        apply CommRingCat.hom_ext
        exact (PadicInt.zmod_cast_comp_toZModPow (p := ℓ)
          n.unop m.unop (leOfHom f.unop)).symm }

/-- The canonical cone from `ℤ_[ℓ]` to the rings `ZMod (ℓ ^ n)` is a
limit cone. -/
noncomputable def padicIntLimitConeIsLimit :
    IsLimit (padicIntLimitCone ℓ) where
  lift s := CommRingCat.ofHom <| PadicInt.lift (p := ℓ) (by
    intro m n h
    have w := s.w ((homOfLE h).op)
    exact congrArg CommRingCat.Hom.hom w)
  fac s n := by
    apply CommRingCat.hom_ext
    exact PadicInt.lift_spec (p := ℓ) _ n.unop
  uniq s g hg := by
    apply CommRingCat.hom_ext
    symm
    apply PadicInt.lift_unique (p := ℓ)
    intro n
    exact congrArg CommRingCat.Hom.hom (hg (op n))

/-- The canonical scalar map from the `ℓ`-adic integers to the `ℓ`-adic
numbers. -/
noncomputable def ellAdicScalarExtension : ℤ_[ℓ] →+* ℚ_[ℓ] :=
  algebraMap ℤ_[ℓ] ℚ_[ℓ]

/-- Mathlib's `ℓ`-adic numbers are canonically the fraction field of its
`ℓ`-adic integers. -/
noncomputable def fractionRingEquivPadic :
    FractionRing ℤ_[ℓ] ≃ₐ[ℤ_[ℓ]] ℚ_[ℓ] :=
  FractionRing.algEquiv ℤ_[ℓ] ℚ_[ℓ]

/-- The two universal properties characterizing the standard `ℓ`-adic
coefficient rings. -/
structure EllAdicCoefficientPackage : Prop where
  reductionLimit : Nonempty (IsLimit (padicIntLimitCone ℓ))
  fractionField : IsFractionRing ℤ_[ℓ] ℚ_[ℓ]

/-- The standard Mathlib `ℓ`-adic integer and number rings form an
`ℓ`-adic coefficient package. -/
theorem ellAdicCoefficientPackage : EllAdicCoefficientPackage ℓ :=
  ⟨⟨padicIntLimitConeIsLimit ℓ⟩, inferInstance⟩

end Hartshorne

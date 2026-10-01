/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Dimension.FgAlgebra
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.Flat.Basic

/-!
# Dimension of a tensor product of affine domains

Hartshorne, *Algebraic Geometry*, I.3, Exercise 3.15(d) (p. 22).

Noether normalisations of the two factors tensor to an injective integral
extension from a polynomial ring on the sum of the two sets of variables.
Krull dimension is invariant under that extension.

## Main result

* `Hartshorne.ringKrullDim_tensorProduct`
-/

namespace Hartshorne

open scoped TensorProduct

attribute [local instance 1100] Module.Free.of_divisionRing Module.Flat.of_free

universe u v w

/-- **Exercise I.3.15(d), algebraic input**: the dimension of a tensor product
of finite-type domains over a field is the sum of their dimensions, provided
the tensor product is again a domain. -/
theorem ringKrullDim_tensorProduct
    (k : Type u) [Field k]
    (A : Type v) [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    (B : Type w) [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
    [IsDomain (A ⊗[k] B)] :
    ringKrullDim (A ⊗[k] B) = ringKrullDim A + ringKrullDim B := by
  classical
  obtain ⟨m, f, hf, hfint⟩ := exists_integral_inj_algHom_of_fg k A
  obtain ⟨n, g, hg, hgint⟩ := exists_integral_inj_algHom_of_fg k B

  let P := MvPolynomial (Fin m) k
  let Q := MvPolynomial (Fin n) k
  let R := P ⊗[k] Q
  let T := A ⊗[k] B

  let _ : Algebra P A := f.toRingHom.toAlgebra
  let _ : IsScalarTower k P A :=
    IsScalarTower.of_algebraMap_eq fun c => (f.commutes c).symm
  let _ : Algebra.IsIntegral P A := ⟨hfint⟩
  let _ : FaithfulSMul P A :=
    (faithfulSMul_iff_algebraMap_injective P A).2 hf

  let _ : Algebra Q B := g.toRingHom.toAlgebra
  let _ : IsScalarTower k Q B :=
    IsScalarTower.of_algebraMap_eq fun c => (g.commutes c).symm
  let _ : Algebra.IsIntegral Q B := ⟨hgint⟩
  let _ : FaithfulSMul Q B :=
    (faithfulSMul_iff_algebraMap_injective Q B).2 hg

  let h : R →ₐ[k] T := Algebra.TensorProduct.map f g
  let _ : Algebra R T := h.toRingHom.toAlgebra
  let _ : IsScalarTower k R T :=
    IsScalarTower.of_algebraMap_eq fun c => (h.commutes c).symm

  have hinj : Function.Injective h := by
    exact TensorProduct.map_injective_of_flat_flat f.toLinearMap g.toLinearMap hf hg
  let _ : FaithfulSMul R T :=
    (faithfulSMul_iff_algebraMap_injective R T).2 hinj

  have hcompLeft :
      (algebraMap R T).comp
          (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := P) (B := Q)).toRingHom =
        (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := A) (B := B)).toRingHom.comp
          (algebraMap P A) := by
    change h.toRingHom.comp Algebra.TensorProduct.includeLeftRingHom =
      Algebra.TensorProduct.includeLeftRingHom.comp f.toRingHom
    exact congrArg AlgHom.toRingHom (Algebra.TensorProduct.map_comp_includeLeft f g)

  have hcompRight :
      (algebraMap R T).comp
          (Algebra.TensorProduct.includeRight (R := k) (A := P) (B := Q)).toRingHom =
        (Algebra.TensorProduct.includeRight (R := k) (A := A) (B := B)).toRingHom.comp
          (algebraMap Q B) := by
    change h.toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := k) (A := P) (B := Q)).toRingHom =
      (Algebra.TensorProduct.includeRight (R := k) (A := A) (B := B)).toRingHom.comp g.toRingHom
    exact congrArg AlgHom.toRingHom (Algebra.TensorProduct.map_comp_includeRight f g)

  have hleft (a : A) : IsIntegral R
      ((Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := A) (B := B)) a) :=
    (Algebra.IsIntegral.isIntegral a).map_of_comp_eq
      (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := P) (B := Q)).toRingHom
      (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := A) (B := B)).toRingHom
      hcompLeft

  have hright (b : B) : IsIntegral R
      ((Algebra.TensorProduct.includeRight (R := k) (A := A) (B := B)) b) :=
    (Algebra.IsIntegral.isIntegral b).map_of_comp_eq
      (Algebra.TensorProduct.includeRight (R := k) (A := P) (B := Q)).toRingHom
      (Algebra.TensorProduct.includeRight (R := k) (A := A) (B := B)).toRingHom
      hcompRight

  let _ : Algebra.IsIntegral R T := by
    constructor
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact isIntegral_zero
    | tmul a b =>
        simpa only [Algebra.TensorProduct.includeLeft_apply,
          Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
          mul_one, one_mul] using (hleft a).mul (hright b)
    | add x y hx hy => exact hx.add hy

  have hdimA : ringKrullDim A = m := by
    rw [ringKrullDim_eq_of_isIntegral P A,
      MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  have hdimB : ringKrullDim B = n := by
    rw [ringKrullDim_eq_of_isIntegral Q B,
      MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  have hdimR : ringKrullDim R = m + n := by
    rw [ringKrullDim_eq_of_ringEquiv
      (MvPolynomial.tensorEquivSum k (Fin m) (Fin n) k).toRingEquiv,
      MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp

  change ringKrullDim T = ringKrullDim A + ringKrullDim B
  rw [ringKrullDim_eq_of_isIntegral R T, hdimR, hdimA, hdimB]

end Hartshorne

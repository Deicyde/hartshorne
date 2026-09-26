/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Curve.PolynomialNormalization
import Mathlib.RingTheory.NoetherNormalization

/-!
# Finiteness of integral closures of affine domains

This file proves Hartshorne I.3, Theorem 3.9A.  Over an algebraically closed
field, the integral closure of a finite-type domain in an arbitrary finite
extension of its fraction field is module-finite.  No separability hypothesis
is imposed.

The proof uses finite injective Noether normalization.  After passing from the
normalizing polynomial ring to its fraction field, finiteness is transported
through the given tower of fields.  Polynomial normalization finiteness then
gives a finite spanning family; restricting scalars from the polynomial ring
to the original affine algebra reuses that same family.
-/

namespace Hartshorne

noncomputable section

universe u v w x

/-- The integral closure of a finite-type domain over an algebraically closed
field in any finite extension of its fraction field is module-finite.  This is
Hartshorne I.3, Theorem 3.9A, without a separability assumption. -/
theorem moduleFinite_integralClosure_of_finiteType
    (k : Type u) [Field k] [IsAlgClosed k]
    (A : Type v) [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A]
    (K : Type w) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type x) [Field L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [FiniteDimensional K L] :
    Module.Finite A (integralClosure A L) := by
  obtain ⟨n, g, hg, hfinite⟩ := exists_finite_inj_algHom_of_fg k A
  let P := MvPolynomial (Fin n) k
  let _ : Algebra P A := g.toRingHom.toAlgebra
  let _ : Module.Finite P A := hfinite
  let _ : FaithfulSMul P A :=
    (faithfulSMul_iff_algebraMap_injective P A).2 hg

  let _ : Algebra P K :=
    ((algebraMap A K).comp (algebraMap P A)).toAlgebra
  let _ : IsScalarTower P A K := IsScalarTower.of_algebraMap_eq' rfl
  let _ : FaithfulSMul P K := FaithfulSMul.trans P A K

  let _ : Algebra P L :=
    ((algebraMap A L).comp (algebraMap P A)).toAlgebra
  let _ : IsScalarTower P A L := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower P K L := IsScalarTower.to₁₃₄ P A K L

  let F := FractionRing P
  let _ : Algebra F K := FractionRing.liftAlgebra P K
  let _ : IsScalarTower P F K :=
    FractionRing.isScalarTower_liftAlgebra P K
  let _ : Algebra F L :=
    ((algebraMap K L).comp (algebraMap F K)).toAlgebra
  let _ : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower P F L := IsScalarTower.to₁₂₄ P F K L

  let _ : FaithfulSMul P (FractionRing A) :=
    FaithfulSMul.trans P A (FractionRing A)
  let _ : Algebra F (FractionRing A) :=
    FractionRing.liftAlgebra P (FractionRing A)
  let _ : IsScalarTower P F (FractionRing A) :=
    FractionRing.isScalarTower_liftAlgebra P (FractionRing A)
  let _ : FiniteDimensional F (FractionRing A) := inferInstance

  let eAK : FractionRing A ≃ₐ[A] K := FractionRing.algEquiv A K
  have hmaps :
      eAK.toRingEquiv.toRingHom.comp (algebraMap F (FractionRing A)) =
        algebraMap F K := by
    apply IsFractionRing.ringHom_ext (A := P)
    intro p
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [← IsScalarTower.algebraMap_apply P F (FractionRing A),
      IsScalarTower.algebraMap_apply P A (FractionRing A)]
    change eAK (algebraMap A (FractionRing A) (algebraMap P A p)) = _
    rw [eAK.commutes, ← IsScalarTower.algebraMap_apply P A K,
      ← IsScalarTower.algebraMap_apply P F K]
  let e : FractionRing A ≃ₐ[F] K :=
    { eAK.toRingEquiv with
      commutes' := fun z => DFunLike.congr_fun hmaps z }
  let _ : FiniteDimensional F K := Module.Finite.equiv e.toLinearEquiv
  let _ : FiniteDimensional F L := Module.Finite.trans K L

  let B := integralClosure P L
  let _ : Module.Finite P B :=
    moduleFinite_integralClosure_mvPolynomial k n F L
  let aToB : A →ₐ[P] B := IsIntegralClosure.lift P B L
  let _ : Algebra A B := aToB.toRingHom.toAlgebra
  let _ : IsScalarTower P A B :=
    IsScalarTower.of_algebraMap_eq fun p => (aToB.commutes p).symm
  let _ : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap A L a = algebraMap B L (aToB a)
    exact (IsIntegralClosure.algebraMap_lift P B L a).symm
  let _ : Module.Finite A B :=
    Module.Finite.of_restrictScalars_finite P A B
  let _ : IsIntegralClosure B A L :=
    IsIntegralClosure.tower_top (R := P)
  let eB : B ≃ₐ[A] integralClosure A L :=
    IsIntegralClosure.equiv (R := A) (A := B) (B := L)
      (integralClosure A L)
  exact Module.Finite.equiv eB.toLinearEquiv

/-- The normalization in `moduleFinite_integralClosure_of_finiteType` is
again a finite-type algebra over the ground field.  The displayed algebra
structure is the composite `k → A → integralClosure A L`. -/
theorem finiteType_integralClosure_of_finiteType
    (k : Type u) [Field k] [IsAlgClosed k]
    (A : Type v) [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A]
    (K : Type w) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type x) [Field L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [FiniteDimensional K L] :
    letI : Algebra k (integralClosure A L) :=
      ((algebraMap A (integralClosure A L)).comp (algebraMap k A)).toAlgebra
    Algebra.FiniteType k (integralClosure A L) := by
  let _ : Algebra k (integralClosure A L) :=
    ((algebraMap A (integralClosure A L)).comp (algebraMap k A)).toAlgebra
  let _ : IsScalarTower k A (integralClosure A L) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let _ : Module.Finite A (integralClosure A L) :=
    moduleFinite_integralClosure_of_finiteType k A K L
  exact Algebra.FiniteType.trans (S := A) inferInstance
    (Module.Finite.finiteType (integralClosure A L))

end

end Hartshorne

/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Curve.PurelyInseparableNormalization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Finiteness of normalizations of polynomial rings

The integral closure of a polynomial ring over an algebraically closed field
in an arbitrary finite extension of its fraction field is finite.  No
separability hypothesis is imposed: we first normalize in the maximal
separable intermediate field and then use the purely inseparable finiteness
theorem for the remaining extension.
-/

namespace Hartshorne

noncomputable section

universe u v w

/-- The integral closure of a finite-variable polynomial ring over an
algebraically closed field in any finite extension of its fraction field is a
finite module. -/
theorem moduleFinite_integralClosure_mvPolynomial
    (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (K : Type v) (L : Type w) [Field K] [Field L]
    [Algebra (MvPolynomial (Fin n) k) K]
    [IsFractionRing (MvPolynomial (Fin n) k) K]
    [Algebra K L] [Algebra (MvPolynomial (Fin n) k) L]
    [IsScalarTower (MvPolynomial (Fin n) k) K L]
    [FiniteDimensional K L] :
    Module.Finite (MvPolynomial (Fin n) k)
      (integralClosure (MvPolynomial (Fin n) k) L) := by
  let P := MvPolynomial (Fin n) k
  let M := separableClosure K L
  let C := integralClosure P M
  let B := integralClosure P L
  let _ : IsScalarTower P M L :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let _ : Module.Finite P C :=
    IsIntegralClosure.finite P K M C
  let _ : IsIntegrallyClosed C :=
    integralClosure.isIntegrallyClosedOfFiniteExtension K
  let _ : IsFractionRing C M :=
    integralClosure.isFractionRing_of_finite_extension K M
  let _ : Algebra k C :=
    ((algebraMap P C).comp (algebraMap k P)).toAlgebra
  let _ : IsScalarTower k P C :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let _ : Algebra.FiniteType k C :=
    Algebra.FiniteType.trans (S := P) inferInstance
      (Module.Finite.finiteType C)
  let E := integralClosure C L
  let smulCE : SMul C E := (Subalgebra.algebra E).toSMul
  let _ : Algebra C E := { Subalgebra.algebra E with toSMul := smulCE }
  let smulEL : SMul E L := (Subalgebra.toAlgebra E).toSMul
  let _ : Algebra E L := { Subalgebra.toAlgebra E with toSMul := smulEL }
  let _ : IsScalarTower C E L :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let _ : Module.Finite C E :=
    moduleFinite_integralClosure_of_isPurelyInseparable k C M L
  let cToB : C →ₐ[P] B := IsIntegralClosure.lift P B L
  let _ : Algebra C B := cToB.toRingHom.toAlgebra
  let _ : IsScalarTower P C B :=
    IsScalarTower.of_algebraMap_eq fun x => (cToB.commutes x).symm
  let _ : IsScalarTower C B L := IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap C L c = algebraMap B L (cToB c)
    exact (IsIntegralClosure.algebraMap_lift P B L c).symm
  let _ : IsIntegralClosure B C L :=
    IsIntegralClosure.tower_top (R := P)
  let e : E ≃ₐ[C] B :=
    IsIntegralClosure.equiv (R := C) (A := E) (B := L) B
  let _ : Module.Finite C B := Module.Finite.equiv e.toLinearEquiv
  exact Module.Finite.trans C B

end

end Hartshorne

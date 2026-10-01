/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.AffineProduct
import Hartshorne.Affine.CoordinateRing
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# The coordinate ring of an affine product

Hartshorne, *Algebraic Geometry*, I.3, Exercise 3.15(b) (p. 22).

The polynomial tensor-product equivalence sends the two families of variables
to the left and right coordinates. Passing to the quotients by the two
vanishing ideals gives the coordinate ring of the affine product.

## Main result

* `Hartshorne.coordinateRing_affineProductEquiv`
-/

namespace Hartshorne

open MvPolynomial
open scoped TensorProduct

variable {k : Type*} [Field k] {σ τ : Type*}

/-- Evaluation at a point of a set descends to its coordinate ring. -/
noncomputable def coordinateEval (X : Set (σ → k)) (x : X) :
    coordinateRing X →ₐ[k] k :=
  Ideal.Quotient.liftₐ (vanishingIdeal k X) (MvPolynomial.aeval x.1) fun _ hf => hf x.1 x.2

@[simp]
theorem coordinateEval_mk (X : Set (σ → k)) (x : X) (f : MvPolynomial σ k) :
    coordinateEval X x (Ideal.Quotient.mk (vanishingIdeal k X) f) = eval x.1 f := by
  rfl

/-- The canonical map from polynomials on the ambient product affine space to
the tensor product of the two coordinate rings. -/
noncomputable def affineProductCoordinateMap (X : Set (σ → k)) (Y : Set (τ → k)) :
    MvPolynomial (Sum σ τ) k →ₐ[k] coordinateRing X ⊗[k] coordinateRing Y :=
  (Algebra.TensorProduct.map
      (Ideal.Quotient.mkₐ k (vanishingIdeal k X))
      (Ideal.Quotient.mkₐ k (vanishingIdeal k Y))).comp
    (MvPolynomial.tensorEquivSum k σ τ k).symm.toAlgHom

/-- Evaluate a tensor of coordinate functions at a pair of points. -/
noncomputable def coordinateTensorEval (X : Set (σ → k)) (Y : Set (τ → k))
    (x : X) (y : Y) : coordinateRing X ⊗[k] coordinateRing Y →ₐ[k] k :=
  Algebra.TensorProduct.lift (coordinateEval X x) (coordinateEval Y y)
    fun _ _ => Commute.all _ _

@[simp]
theorem coordinateTensorEval_tmul (X : Set (σ → k)) (Y : Set (τ → k))
    (x : X) (y : Y) (f : coordinateRing X) (g : coordinateRing Y) :
    coordinateTensorEval X Y x y (f ⊗ₜ[k] g) = coordinateEval X x f * coordinateEval Y y g := by
  rfl

private theorem coordinateEval_separates (X : Set (σ → k)) (f : coordinateRing X)
    (hf : ∀ x : X, coordinateEval X x f = 0) : f = 0 := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective f
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  intro x hx
  simpa using hf ⟨x, hx⟩

private noncomputable def tensorRightEval {A B : Type*} [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (g : B →ₐ[k] k) : A ⊗[k] B →ₐ[k] A :=
  Algebra.TensorProduct.lift (AlgHom.id k A) ((Algebra.ofId k A).comp g)
    fun _ _ => Commute.all _ _

@[simp]
private theorem tensorRightEval_tmul {A B : Type*} [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (g : B →ₐ[k] k) (a : A) (b : B) :
    tensorRightEval g (a ⊗ₜ[k] b) = g b • a := by
  simp [tensorRightEval, Algebra.smul_def, mul_comm]

private theorem basis_repr_tensorRightEval {A B : Type*} [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] {ι : Type*} [DecidableEq ι]
    (bA : Module.Basis ι k A) (g : B →ₐ[k] k) (t : A ⊗[k] B) (i : ι) :
    bA.repr (tensorRightEval g t) i =
      g ((TensorProduct.equivFinsuppOfBasisLeft bA t) i) := by
  induction t with
  | zero => simp
  | tmul a b =>
      simp [tensorRightEval_tmul, map_smul, mul_comm]
  | add x y hx hy => simp [hx, hy]

private theorem coordinateEval_tensorRightEval
    (X : Set (σ → k)) (Y : Set (τ → k)) (x : X) (y : Y)
    (t : coordinateRing X ⊗[k] coordinateRing Y) :
    coordinateEval X x (tensorRightEval (coordinateEval Y y) t) =
      coordinateTensorEval X Y x y t := by
  induction t with
  | zero => simp
  | tmul f g => simp [tensorRightEval_tmul, coordinateTensorEval_tmul, mul_comm]
  | add a b ha hb => simp [ha, hb]

private theorem coordinateTensorEval_separates
    (X : Set (σ → k)) (Y : Set (τ → k))
    (t : coordinateRing X ⊗[k] coordinateRing Y)
    (ht : ∀ x : X, ∀ y : Y, coordinateTensorEval X Y x y t = 0) : t = 0 := by
  classical
  let bX := Module.Free.chooseBasis k (coordinateRing X)
  let c := TensorProduct.equivFinsuppOfBasisLeft bX t
  have hright (y : Y) : tensorRightEval (coordinateEval Y y) t = 0 := by
    apply coordinateEval_separates X
    intro x
    rw [coordinateEval_tensorRightEval]
    exact ht x y
  have hc : c = 0 := by
    ext i
    apply coordinateEval_separates Y
    intro y
    rw [← basis_repr_tensorRightEval bX (coordinateEval Y y) t i, hright y]
    simp
  apply (TensorProduct.equivFinsuppOfBasisLeft bX).injective
  simpa [c] using hc

@[simp]
theorem coordinateTensorEval_affineProductCoordinateMap
    (X : Set (σ → k)) (Y : Set (τ → k)) (x : X) (y : Y)
    (f : MvPolynomial (Sum σ τ) k) :
    coordinateTensorEval X Y x y (affineProductCoordinateMap X Y f) =
      eval (affineProductPoint x.1 y.1) f := by
  change ((coordinateTensorEval X Y x y).comp (affineProductCoordinateMap X Y)) f =
    MvPolynomial.aeval (affineProductPoint x.1 y.1) f
  congr 1
  ext s
  cases s with
  | inl i =>
      have hX : (MvPolynomial.tensorEquivSum k σ τ k).symm (MvPolynomial.X (Sum.inl i)) =
          MvPolynomial.X i ⊗ₜ[k] 1 := by
        apply (MvPolynomial.tensorEquivSum k σ τ k).injective
        simp
      simp [affineProductCoordinateMap, coordinateTensorEval, coordinateEval,
        affineProductPoint, hX]
  | inr j =>
      have hX : (MvPolynomial.tensorEquivSum k σ τ k).symm (MvPolynomial.X (Sum.inr j)) =
          1 ⊗ₜ[k] MvPolynomial.X j := by
        apply (MvPolynomial.tensorEquivSum k σ τ k).injective
        simp
      simp [affineProductCoordinateMap, coordinateTensorEval, coordinateEval,
        affineProductPoint, hX]

private theorem affineProductCoordinateMap_surjective
    (X : Set (σ → k)) (Y : Set (τ → k)) :
    Function.Surjective (affineProductCoordinateMap X Y) := by
  exact (Algebra.TensorProduct.map_surjective
      (Ideal.Quotient.mkₐ k (vanishingIdeal k X))
      (Ideal.Quotient.mkₐ k (vanishingIdeal k Y))
      Ideal.Quotient.mk_surjective Ideal.Quotient.mk_surjective).comp
    (MvPolynomial.tensorEquivSum k σ τ k).symm.surjective

private theorem affineProductCoordinateMap_ker
    (X : Set (σ → k)) (Y : Set (τ → k)) :
    RingHom.ker (affineProductCoordinateMap X Y) =
      vanishingIdeal k (affineProduct X Y) := by
  apply le_antisymm
  · intro f hf z hz
    let x : X := ⟨fun i => z (Sum.inl i), hz.1⟩
    let y : Y := ⟨fun j => z (Sum.inr j), hz.2⟩
    have hzero := congrArg (coordinateTensorEval X Y x y) hf
    rw [coordinateTensorEval_affineProductCoordinateMap] at hzero
    have hpoint : affineProductPoint x.1 y.1 = z := by
      funext s
      cases s <;> rfl
    simpa [hpoint] using hzero
  · intro f hf
    apply coordinateTensorEval_separates X Y
    intro x y
    rw [coordinateTensorEval_affineProductCoordinateMap]
    apply hf
    exact ⟨x.2, y.2⟩

/-- **Exercise I.3.15(b)**: the coordinate ring of the affine product is
canonically the tensor product of the coordinate rings of its factors. -/
noncomputable def coordinateRing_affineProductEquiv
    (X : Set (σ → k)) (Y : Set (τ → k)) :
    coordinateRing (affineProduct X Y) ≃ₐ[k]
      coordinateRing X ⊗[k] coordinateRing Y :=
  (Ideal.quotientEquivAlgOfEq k (affineProductCoordinateMap_ker X Y).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      (affineProductCoordinateMap_surjective X Y))

@[simp]
theorem coordinateRing_affineProductEquiv_mk
    (X : Set (σ → k)) (Y : Set (τ → k))
    (f : MvPolynomial (Sum σ τ) k) :
    coordinateRing_affineProductEquiv X Y
        (Ideal.Quotient.mk (vanishingIdeal k (affineProduct X Y)) f) =
      affineProductCoordinateMap X Y f := by
  rfl

end Hartshorne

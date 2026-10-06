/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.CodimensionOneStalkDVR
import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
import Mathlib.Data.Finsupp.Basic

/-!
# Weil divisors

Hartshorne, *Algebraic Geometry*, II.6, p. 130.

Prime divisors are represented by their codimension-one generic points. Weil
divisors are integer-valued algebraic cycles supported on those points. On a
scheme satisfying Hartshorne's condition `(*)`, compactness turns the locally
finite support of an algebraic cycle into finite support, recovering the usual
free abelian group on prime divisors.
-/

noncomputable section

open Filter Set TopologicalSpace

namespace AlgebraicGeometry

universe u v

/-- A prime divisor represented by its unique codimension-one generic point. -/
abbrev Scheme.PrimeDivisor (X : Scheme.{u}) :=
  { x : X // Order.coheight x = 1 }

namespace Scheme.PrimeDivisor

/-- The irreducible closed subset represented by a prime divisor's generic
point. -/
noncomputable def irreducibleClosed {X : Scheme.{u}} (P : X.PrimeDivisor) :
    IrreducibleCloseds X :=
  irreducibleSetEquivPoints.symm P.1

@[simp]
theorem coe_irreducibleClosed {X : Scheme.{u}} (P : X.PrimeDivisor) :
    (P.irreducibleClosed : Set X) = closure {P.1} :=
  coe_irreducibleEquivPoints_symm_apply P.1

theorem coheight_irreducibleClosed {X : Scheme.{u}} (P : X.PrimeDivisor) :
    Order.coheight P.irreducibleClosed = 1 := by
  rw [irreducibleClosed,
    Order.coheight_orderIso (irreducibleSetEquivPoints (α := X)).symm]
  exact P.2

end Scheme.PrimeDivisor

/-- Prime divisors, viewed as codimension-one generic points, are equivalent
to codimension-one irreducible closed subsets. -/
noncomputable def Scheme.primeDivisorEquivIrreducibleClosed (X : Scheme.{u}) :
    X.PrimeDivisor ≃
      { Z : IrreducibleCloseds X // Order.coheight Z = 1 } where
  toFun P := ⟨P.irreducibleClosed, P.coheight_irreducibleClosed⟩
  invFun Z :=
    ⟨irreducibleSetEquivPoints Z.1, by
      rw [Order.coheight_orderIso (irreducibleSetEquivPoints (α := X))]
      exact Z.2⟩
  left_inv P := by
    apply Subtype.ext
    exact (irreducibleSetEquivPoints (α := X)).apply_symm_apply P.1
  right_inv Z := by
    apply Subtype.ext
    exact (irreducibleSetEquivPoints (α := X)).symm_apply_apply Z.1

/-- The additive subgroup of algebraic cycles supported at codimension-one
points. -/
def Scheme.weilDivisorAddSubgroup (X : Scheme.{u}) :
    AddSubgroup (AlgebraicCycle X ℤ) where
  carrier D := ∀ x, Order.coheight x ≠ 1 → D x = 0
  zero_mem' _ _ := rfl
  add_mem' {D E} hD hE x hx := by
    change D x + E x = 0
    rw [hD x hx, hE x hx, zero_add]
  neg_mem' {D} hD x hx := by
    change -D x = 0
    rw [hD x hx, neg_zero]

/-- The additive group of Weil divisors on `X`. -/
abbrev Scheme.WeilDivisor (X : Scheme.{u}) :=
  X.weilDivisorAddSubgroup

namespace Scheme.WeilDivisor

/-- A Weil divisor is effective when every coefficient is nonnegative. -/
def IsEffective {X : Scheme.{u}} (D : X.WeilDivisor) : Prop :=
  ∀ x, 0 ≤ D.1 x

theorem isEffective_iff {X : Scheme.{u}} (D : X.WeilDivisor) :
    IsEffective D ↔ ∀ P : X.PrimeDivisor, 0 ≤ D.1 P.1 := by
  constructor
  · exact fun h P ↦ h P.1
  · intro h x
    by_cases hx : Order.coheight x = 1
    · exact h ⟨x, hx⟩
    · rw [D.2 x hx]

end Scheme.WeilDivisor

/-- On a scheme satisfying condition `(*)`, local finiteness of a support is
equivalent to finiteness. -/
theorem Scheme.locallyFiniteSupport_iff_finite_of_satisfiesConditionStar
    {X : Scheme.{u}} (hX : X.SatisfiesConditionStar)
    {A : Type v} [Zero A] (f : X → A) :
    LocallyFiniteSupport f ↔ f.support.Finite := by
  let _ : IsNoetherian X := hX.isNoetherian
  constructor
  · intro h
    have H := h.finite_inter_support_of_isCompact
      (W := Set.univ) isCompact_univ
    simpa using H
  · intro h x
    exact ⟨Set.univ, univ_mem, by simpa using h⟩

/-- Weil divisors on a scheme satisfying condition `(*)` have finite support. -/
theorem Scheme.WeilDivisor.support_finite
    {X : Scheme.{u}} (hX : X.SatisfiesConditionStar) (D : X.WeilDivisor) :
    D.1.support.Finite :=
  (X.locallyFiniteSupport_iff_finite_of_satisfiesConditionStar hX D.1).mp
    D.1.locallyFiniteSupport

private noncomputable def weilDivisorToFinsupp
    {X : Scheme.{u}} (hX : X.SatisfiesConditionStar) (D : X.WeilDivisor) :
    X.PrimeDivisor →₀ ℤ := by
  classical
  have hpre : (Subtype.val ⁻¹' D.1.support : Set X.PrimeDivisor).Finite :=
    (Scheme.WeilDivisor.support_finite hX D).preimage Subtype.val_injective.injOn
  exact Finsupp.onFinset hpre.toFinset (fun P ↦ D.1 P.1) fun P hP ↦ by
    rw [hpre.mem_toFinset]
    exact hP

@[simp]
private theorem weilDivisorToFinsupp_apply
    {X : Scheme.{u}} (hX : X.SatisfiesConditionStar)
    (D : X.WeilDivisor) (P : X.PrimeDivisor) :
    weilDivisorToFinsupp hX D P = D.1 P.1 := by
  classical
  simp [weilDivisorToFinsupp]

private noncomputable def weilDivisorOfFinsupp
    {X : Scheme.{u}} (F : X.PrimeDivisor →₀ ℤ) : X.WeilDivisor := by
  classical
  let f : X →₀ ℤ := F.extendDomain
  let D : AlgebraicCycle X ℤ :=
    { toFun := f
      supportWithinDomain' := subset_univ _
      supportLocallyFiniteWithinDomain' := fun _ _ ↦
        ⟨Set.univ, univ_mem, by
          rw [univ_inter]
          rw [show Function.support (f : X → ℤ) = (f.support : Set X) by
            ext y
            simp]
          exact f.support.finite_toSet⟩ }
  refine ⟨D, ?_⟩
  intro x hx
  change F.extendDomain x = 0
  rw [Finsupp.extendDomain_apply
    (P := fun y : X ↦ Order.coheight y = 1), dif_neg hx]

@[simp]
private theorem weilDivisorOfFinsupp_apply
    {X : Scheme.{u}} (F : X.PrimeDivisor →₀ ℤ) (x : X) :
    (weilDivisorOfFinsupp F).1 x =
      if hx : Order.coheight x = 1 then F ⟨x, hx⟩ else 0 := by
  classical
  change F.extendDomain x = _
  rw [Finsupp.extendDomain_apply
    (P := fun y : X ↦ Order.coheight y = 1)]

/-- On a scheme satisfying condition `(*)`, Weil divisors form the free
abelian group on prime divisors. -/
noncomputable def Scheme.weilDivisorAddEquivFinsupp
    {X : Scheme.{u}} (hX : X.SatisfiesConditionStar) :
    X.WeilDivisor ≃+ (X.PrimeDivisor →₀ ℤ) where
  toFun := weilDivisorToFinsupp hX
  invFun := weilDivisorOfFinsupp
  left_inv D := by
    apply Subtype.ext
    apply Function.locallyFinsuppWithin.ext
    intro x
    by_cases hx : Order.coheight x = 1
    · rw [weilDivisorOfFinsupp_apply, dif_pos hx,
        weilDivisorToFinsupp_apply]
    · rw [weilDivisorOfFinsupp_apply, dif_neg hx, D.2 x hx]
  right_inv F := by
    ext P
    rw [weilDivisorToFinsupp_apply, weilDivisorOfFinsupp_apply, dif_pos P.2]
  map_add' D E := by
    ext P
    simp [weilDivisorToFinsupp_apply]

end AlgebraicGeometry

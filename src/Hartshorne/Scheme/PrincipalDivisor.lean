/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.WeilDivisor
import Mathlib.AlgebraicGeometry.OrderOfVanishing

/-!
# Principal Weil divisors

Hartshorne, *Algebraic Geometry*, II.6, Lemma 6.1 and the following
definition (p. 131).
-/

noncomputable section

open Filter Set TopologicalSpace

namespace AlgebraicGeometry

universe u

private theorem finite_codimensionOne_compl
    {X : Scheme.{u}} [IsNoetherian X] [IsIntegral X]
    (U : X.Opens) [Nonempty U] :
    {x : X | Order.coheight x = 1 ∧ x ∉ (U : Set X)}.Finite := by
  obtain ⟨T, hTfin, hTclosed, hTirr, hTC⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible U.isOpen.isClosed_compl
  let _ : Fintype T := hTfin.fintype
  let g : T → X := fun t ↦ (hTirr t.1 t.2).genericPoint
  refine (Set.finite_range g).subset ?_
  intro x hx
  have hxC : x ∈ (U : Set X)ᶜ := hx.2
  have hclosureC : closure ({x} : Set X) ⊆ Uᶜ :=
    closure_minimal (by simpa) U.isOpen.isClosed_compl
  let Tf : Finset (Set X) := hTfin.toFinset
  have hTfclosed : ∀ t ∈ Tf, IsClosed t := by
    intro t ht
    exact hTclosed t (hTfin.mem_toFinset.mp ht)
  have hclosureUnion : closure ({x} : Set X) ⊆ ⋃₀ (Tf : Set (Set X)) := by
    rw [hTfin.coe_toFinset, ← hTC]
    exact hclosureC
  obtain ⟨t, htTf, hclosuret⟩ :=
    (isIrreducible_iff_sUnion_isClosed.mp isIrreducible_singleton.closure)
      Tf hTfclosed hclosureUnion
  have htT : t ∈ T := hTfin.mem_toFinset.mp htTf
  let Z : IrreducibleCloseds X := irreducibleSetEquivPoints.symm x
  let W : IrreducibleCloseds X := ⟨t, hTirr t htT, hTclosed t htT⟩
  have hZW : Z ≤ W := by
    change (Z : Set X) ⊆ t
    simpa [Z] using hclosuret
  have hZcoheight : Order.coheight Z = 1 := by
    change Order.coheight (irreducibleSetEquivPoints.symm x) = 1
    rw [Order.coheight_orderIso (irreducibleSetEquivPoints (α := X)).symm]
    exact hx.1
  have hZW_eq : Z = W := by
    apply le_antisymm hZW
    by_contra hWZ
    have hlt : Z < W := ⟨hZW, hWZ⟩
    have hWle : Order.coheight W ≤ 1 := by
      rw [← hZcoheight]
      exact Order.coheight_anti hZW
    have hWfin : Order.coheight W < ⊤ := lt_of_le_of_lt hWle (by simp)
    have hcoheight_lt : Order.coheight W < Order.coheight Z :=
      Order.coheight_strictAnti hlt hWfin
    rw [hZcoheight] at hcoheight_lt
    have hWzero : Order.coheight W = 0 :=
      Order.lt_one_iff.mp hcoheight_lt
    let Wtop : IrreducibleCloseds X :=
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
    have hWtop : W = Wtop :=
      (Order.coheight_eq_zero.mp hWzero).eq_of_le (Set.subset_univ _)
    have htC : t ⊆ Uᶜ := by
      rw [hTC]
      exact subset_sUnion_of_mem htT
    obtain ⟨y, hy⟩ := (inferInstance : Nonempty U)
    have hyW : y ∈ (W : Set X) := by
      rw [hWtop]
      change y ∈ (Set.univ : Set X)
      trivial
    exact (show y ∉ (U : Set X) from htC hyW) hy
  refine ⟨⟨t, htT⟩, ?_⟩
  change irreducibleSetEquivPoints W = x
  rw [← hZW_eq]
  exact (irreducibleSetEquivPoints (α := X)).apply_symm_apply x

/-- **Hartshorne II.6, Lemma 6.1.** A nonzero rational function has nonzero
order at only finitely many codimension-one points. -/
theorem Scheme.finite_support_ord_of_satisfiesConditionStar
    {X : Scheme.{u}} (hX : X.SatisfiesConditionStar) :
    let _ : IsNoetherian X := hX.isNoetherian
    let _ : IsIntegral X := hX.isIntegral
    ∀ {f : X.functionField}, f ≠ 0 →
      (Function.support fun x : X ↦ X.ord f x).Finite := by
  dsimp only
  let _ : IsNoetherian X := hX.isNoetherian
  let _ : IsIntegral X := hX.isIntegral
  intro f hf
  obtain ⟨U, _, fU, hU, hUf, hfU⟩ := exists_isUnit_germ_eq X f hf
  let _ : Nonempty U := hU
  refine (finite_codimensionOne_compl U).subset ?_
  intro x hx
  change X.ord f x ≠ 0 at hx
  constructor
  · by_contra hcodim
    exact hx (X.ord_eq_zero_of_coheight_neq_one hcodim f)
  · intro hxU
    apply hx
    rw [← hUf]
    exact X.ord_of_isUnit hfU hxU

private noncomputable def principalDivisorOfNonzero
    {X : Scheme.{u}} [IsNoetherian X] [IsIntegral X]
    (hX : X.SatisfiesConditionStar) (f : X.functionField) (hf : f ≠ 0) :
    X.WeilDivisor := by
  let coeff : X → ℤ := fun x ↦ X.ord f x
  have hfin : coeff.support.Finite :=
    X.finite_support_ord_of_satisfiesConditionStar hX hf
  let D : AlgebraicCycle X ℤ :=
    { toFun := coeff
      supportWithinDomain' := subset_univ _
      supportLocallyFiniteWithinDomain' := fun _ _ ↦
        ⟨Set.univ, univ_mem, by simpa [coeff] using hfin⟩ }
  refine ⟨D, ?_⟩
  intro x hx
  exact X.ord_eq_zero_of_coheight_neq_one hx f

/-- The principal Weil divisor of a nonzero rational function, represented as
a unit of the function field. -/
noncomputable def Scheme.principalDivisor
    {X : Scheme.{u}} (hX : X.SatisfiesConditionStar) :
    let _ : IsNoetherian X := hX.isNoetherian
    let _ : IsIntegral X := hX.isIntegral
    X.functionFieldˣ → X.WeilDivisor := by
  dsimp only
  let _ : IsNoetherian X := hX.isNoetherian
  let _ : IsIntegral X := hX.isIntegral
  exact fun f ↦ principalDivisorOfNonzero hX f f.ne_zero

@[simp]
theorem Scheme.principalDivisor_apply
    {X : Scheme.{u}} (hX : X.SatisfiesConditionStar) :
    let _ : IsNoetherian X := hX.isNoetherian
    let _ : IsIntegral X := hX.isIntegral
    ∀ (f : X.functionFieldˣ) (x : X),
      (X.principalDivisor hX f).1 x = X.ord (f : X.functionField) x := by
  dsimp only
  let _ : IsNoetherian X := hX.isNoetherian
  let _ : IsIntegral X := hX.isIntegral
  intro f x
  rfl

/-- Principal divisors define a homomorphism from the multiplicative group of
the function field, written additively, to the Weil divisor group. -/
noncomputable def Scheme.principalDivisorHom
    {X : Scheme.{u}} (hX : X.SatisfiesConditionStar) :
    let _ : IsNoetherian X := hX.isNoetherian
    let _ : IsIntegral X := hX.isIntegral
    Additive X.functionFieldˣ →+ X.WeilDivisor := by
  dsimp only
  let _ : IsNoetherian X := hX.isNoetherian
  let _ : IsIntegral X := hX.isIntegral
  refine
    { toFun := fun f ↦ X.principalDivisor hX f.toMul
      map_zero' := ?_
      map_add' := ?_ }
  · apply Subtype.ext
    apply Function.locallyFinsuppWithin.ext
    intro x
    change X.ord (1 : X.functionField) x = 0
    have h := X.ord_mul (x := x) (f := (1 : X.functionField))
      (g := (1 : X.functionField)) one_ne_zero one_ne_zero
    have h' : X.ord (1 : X.functionField) x + 0 =
        X.ord (1 : X.functionField) x + X.ord (1 : X.functionField) x := by
      simpa using h
    have hzero : 0 = X.ord (1 : X.functionField) x :=
      add_left_cancel h'
    exact hzero.symm
  · intro f g
    apply Subtype.ext
    apply Function.locallyFinsuppWithin.ext
    intro x
    change X.ord ((f.toMul * g.toMul : X.functionFieldˣ) : X.functionField) x =
      X.ord (f.toMul : X.functionField) x + X.ord (g.toMul : X.functionField) x
    exact X.ord_mul f.toMul.ne_zero g.toMul.ne_zero

end AlgebraicGeometry

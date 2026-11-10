/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.CartierDivisorPullback
import Hartshorne.Scheme.FiniteCurveDivisorPullback
import Hartshorne.Scheme.RegularLocalFactorial

/-!
# Pulling back the invertible sheaf of a divisor along a finite morphism of curves

A sheaf-level form of Hartshorne, *Algebraic Geometry*, II, Exercise 6.8(b) (p. 148), which
implies it: the exercise states that `f^* : Pic Y → Pic X` corresponds to `f^* : Cl Y → Cl X`
under the isomorphisms of (6.16).

Let `f : X ⟶ Y` be a finite morphism of nonsingular curves. For every Weil divisor `D` on `Y`,
`f^* 𝒪_Y(D) ≅ 𝒪_X(f^* D)`, where on the left `f^*` is the pullback of sheaves of modules and on
the right `f^* : Div Y → Div X` is the pullback of divisors along a finite morphism of curves.

A nonsingular curve is locally factorial, so a Weil divisor `D` corresponds to a Cartier divisor,
whose invertible sheaf is `𝒪_Y(D)`. Near a point `Q` of `Y`, `D` is the divisor of a rational
function `g` (a power of a local parameter at `Q`), and then near every point `P` over `Q`, `f^*D`
is the divisor of `f^# g`, because `ord_P(f^# g) = ord_Q(g) · ord_P(t)`. Hence the Cartier divisor
of `f^*D` is locally the pullback of a local equation of the Cartier divisor of `D`, and the
canonical map `f^* 𝒪_Y(D) ⟶ 𝒪_X(f^*D)` is an isomorphism
(`AlgebraicGeometry.Scheme.isIso_cartierPullbackMap`).
-/

noncomputable section

open CategoryTheory Order TopologicalSpace

namespace AlgebraicGeometry

universe u

namespace Scheme.IsNonsingularCurve

section OneCurve

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X]

/-- A nonsingular curve is locally factorial. -/
theorem isLocallyFactorial (hX : X.IsNonsingularCurve k) : X.IsLocallyFactorial :=
  X.isLocallyFactorial_of_isRegularLocalRing hX.isRegularLocalRing_stalk

/-- The invertible sheaf `𝒪_X(D)` of a Weil divisor `D` on a nonsingular curve: the invertible
sheaf of the Cartier divisor corresponding to `D` on the locally factorial scheme `X`. -/
def divisorSheaf (hX : X.IsNonsingularCurve k) (D : X.WeilDivisor) : X.Modules :=
  letI := hX.satisfiesConditionStar.isNoetherian
  letI := hX.satisfiesConditionStar.isSeparated
  (weilCartierEquiv hX.isLocallyFactorial D).sheaf

/-- A divisor on a nonsingular curve is locally principal: every point `Q` has an open
neighbourhood `V` with a rational function `g` such that `D` is the divisor of `g` on `V`. -/
theorem exists_eq_ord_of_mem (hX : X.IsNonsingularCurve k) (D : X.WeilDivisor) (Q : X) :
    letI := hX.satisfiesConditionStar.isNoetherian
    ∃ (V : X.Opens) (g : X.functionFieldˣ), Q ∈ V ∧
      ∀ y ∈ V, coheight y = 1 → D.1 y = X.ord (g : X.functionField) y := by
  let := hX.satisfiesConditionStar.isNoetherian
  obtain ⟨g, hg⟩ : ∃ g : X.functionFieldˣ, X.ord (g : X.functionField) Q = D.1 Q := by
    by_cases hQ : coheight Q = 1
    · have ht := hX.irreducible_localParameter hQ
      have ht0 : algebraMap _ X.functionField (hX.localParameter Q) ≠ 0 := by
        simpa [map_ne_zero_iff _ (IsFractionRing.injective _ _)] using ht.ne_zero
      refine ⟨Units.mk0 _ ht0 ^ D.1 Q, ?_⟩
      rw [Units.val_zpow_eq_zpow_val, Units.val_mk0, X.ord_eq_iff hQ (zpow_ne_zero _ ht0),
        map_zpow₀, ordHom_algebraMap_of_irreducible hX hQ ht, WithZero.exp,
        ← WithZero.coe_zpow, ← ofAdd_zsmul, smul_eq_mul, mul_one]
    · exact ⟨1, by rw [Units.val_one, X.ord_eq_zero_of_coheight_neq_one hQ, D.2 Q hQ]⟩
  set E := D - X.principalDivisor hX.satisfiesConditionStar g
  have hE : ∀ y, E.1 y = D.1 y - X.ord (g : X.functionField) y := fun y ↦ by
    change D.1 y - (X.principalDivisor hX.satisfiesConditionStar g).1 y = _
    rw [principalDivisor_apply]
  have hclosed : IsClosed (Function.support E.1) := by
    rw [← Set.biUnion_of_singleton (Function.support E.1)]
    refine (Scheme.WeilDivisor.support_finite E).isClosed_biUnion fun y hy ↦ ?_
    refine (hX.isClosed_singleton_iff_coheight_eq_one y).mpr ?_
    by_contra h
    exact hy (E.2 y h)
  refine ⟨⟨(Function.support E.1)ᶜ, hclosed.isOpen_compl⟩, g, ?_, fun y hy _ ↦ ?_⟩
  · change Q ∉ Function.support E.1
    rw [Function.notMem_support, hE, hg, sub_self]
  · have h : E.1 y = 0 := Function.notMem_support.mp hy
    rw [hE, sub_eq_zero] at h
    exact h

end OneCurve

section TwoCurves

variable {k : Type u} [Field k] {X Y : Scheme.{u}} [X.Over (Spec (.of k))]
  [Y.Over (Spec (.of k))] [IsIntegral X] [IsIntegral Y]

/-- Near every point, the Cartier divisor of `f^*D` is the pullback of a local equation of the
Cartier divisor of `D`. -/
theorem cartierPullbackData_finiteCurveDivisorPullback (hX : X.IsNonsingularCurve k)
    (hY : Y.IsNonsingularCurve k) (f : X ⟶ Y) [IsFinite f] (D : Y.WeilDivisor) :
    letI := hX.satisfiesConditionStar.isNoetherian
    letI := hX.satisfiesConditionStar.isSeparated
    letI := hY.satisfiesConditionStar.isNoetherian
    letI := hY.satisfiesConditionStar.isSeparated
    CartierPullbackData f (hX.apply_genericPoint_eq hY f) (weilCartierEquiv hY.isLocallyFactorial D)
      (weilCartierEquiv hX.isLocallyFactorial (hX.finiteCurveDivisorPullback hY f D)) := by
  let := hX.satisfiesConditionStar.isNoetherian
  let := hX.satisfiesConditionStar.isSeparated
  let := hY.satisfiesConditionStar.isNoetherian
  let := hY.satisfiesConditionStar.isSeparated
  refine cartierPullbackData_weilCartierEquiv f _ hX.isLocallyFactorial hY.isLocallyFactorial
    D _ fun x ↦ ?_
  obtain ⟨V, g, hQV, hV⟩ := hY.exists_eq_ord_of_mem D (f x)
  refine ⟨V, f ⁻¹ᵁ V, g, hQV, le_rfl, hV, fun z hz hz1 ↦ ?_⟩
  have hfz := hX.coheight_apply_eq_one hY f hz1
  have ht := hY.irreducible_localParameter hfz
  rw [finiteCurveDivisorPullback_apply, hV (f z) hz hfz,
    hX.finiteCurvePullbackMultiplicity_eq hY f hz1 ht]
  exact (hX.ord_finiteCurveFunctionFieldMap hY f hz1 ht g.ne_zero).symm

/-- The canonical isomorphism `f^* 𝒪_Y(D) ≅ 𝒪_X(f^*D)` for a finite morphism `f : X ⟶ Y` of
nonsingular curves and a Weil divisor `D` on `Y`; it is adjoint to `s ↦ f^# s` on rational
functions. -/
def pullbackDivisorSheafIso (hX : X.IsNonsingularCurve k) (hY : Y.IsNonsingularCurve k)
    (f : X ⟶ Y) [IsFinite f] (D : Y.WeilDivisor) :
    (Scheme.Modules.pullback f).obj (hY.divisorSheaf D) ≅
      hX.divisorSheaf (hX.finiteCurveDivisorPullback hY f D) :=
  letI := hX.satisfiesConditionStar.isNoetherian
  letI := hX.satisfiesConditionStar.isSeparated
  letI := hY.satisfiesConditionStar.isNoetherian
  letI := hY.satisfiesConditionStar.isSeparated
  @asIso _ _ _ _ (cartierPullbackMap (hX.cartierPullbackData_finiteCurveDivisorPullback hY f D))
    (isIso_cartierPullbackMap (hX.cartierPullbackData_finiteCurveDivisorPullback hY f D))

/-- **A sheaf-level form of Hartshorne Exercise II.6.8(b), which implies it.** For a finite
morphism `f : X ⟶ Y` of nonsingular curves and a Weil divisor `D` on `Y`,
`f^* 𝒪_Y(D) ≅ 𝒪_X(f^*D)`. -/
theorem nonempty_pullbackDivisorSheafIso (hX : X.IsNonsingularCurve k)
    (hY : Y.IsNonsingularCurve k) (f : X ⟶ Y) [IsFinite f] (D : Y.WeilDivisor) :
    Nonempty ((Scheme.Modules.pullback f).obj (hY.divisorSheaf D) ≅
      hX.divisorSheaf (hX.finiteCurveDivisorPullback hY f D)) :=
  ⟨hX.pullbackDivisorSheafIso hY f D⟩

end TwoCurves

end Scheme.IsNonsingularCurve

end AlgebraicGeometry

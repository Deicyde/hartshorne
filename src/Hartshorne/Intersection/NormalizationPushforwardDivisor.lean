/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.NormalizationFibreOrder

/-!
# Pushing forward principal divisors along the normalization of a subvariety

Let `X` be a variety over `k`, `i : V ⟶ X` an integral closed subvariety with normalization
`ν : Ṽ ⟶ V`, and `g` a nonzero rational function on `V`. The coefficient of the pushforward to `X`
of the principal divisor of `ν^♯ g` on `Ṽ` at the image of a point `y` of `V` is the order
`ord_y(g)` (`subvarietyNormalizationPushforward_principalDivisor_apply`): by the fibre order
formula, the orders on `Ṽ` over `y`, weighted by residue degrees, add up to `ord_y(g)`.

Finite morphisms between integral schemes of finite type over a field that send the generic
point to the generic point preserve codimensions of points (`coheight_apply_eq_of_isFinite`).
-/

universe u

open AlgebraicGeometry CategoryTheory Order

namespace Hartshorne

/-- A finite morphism `f : W ⟶ Y` of integral schemes of finite type over a field, sending the
generic point to the generic point, preserves codimensions of points, provided `dim W` is
finite. -/
theorem coheight_apply_eq_of_isFinite {k : Type u} [Field k] {W Y : Scheme.{u}} [IsIntegral W]
    [IsIntegral Y] (sW : W ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) (hsW : FiniteType sW)
    (hsY : FiniteType sY) (f : W ⟶ Y) [IsFinite f] (hf : f (genericPoint W) = genericPoint Y)
    {N : ℕ} (hN : topologicalKrullDim W = N) (w : W) : coheight (f w) = coheight w := by
  have hmin : ∀ x : W, ∀ z, z ≤ x → f z = f x → z = x := fun x z hz hfz ↦
    ((f.isDiscrete_preimage_singleton (f x)).eq_of_specializes (show x ⤳ z from hz) rfl hfz).symm
  have hform : ∀ (Z : Scheme.{u}) [IsIntegral Z] (s : Z ⟶ Spec (.of k)), FiniteType s →
      ∀ z : Z, (((height z + coheight z : ℕ∞)) : WithBot ℕ∞) = topologicalKrullDim Z := by
    intro Z _ s hs z
    have h := dimension_codimension_formula s hs (closure {z}) isClosed_closure
      ⟨z, subset_closure rfl⟩
    rw [FlatEquidimensional.topologicalKrullDim_closure_singleton,
      codim_closure_singleton_eq_coheight] at h
    rw [← h]
    rfl
  have h1 := hform W sW hsW w
  have h2 := hform Y sY hsY (f w)
  have h3 := hform W sW hsW (genericPoint W)
  have h4 := hform Y sY hsY (genericPoint Y)
  rw [coheight_genericPoint, add_zero] at h3 h4
  have hh := FlatEquidimensional.height_eq_height_of_forall sW sY hsW hsY f w (hmin w)
  have hξ := FlatEquidimensional.height_eq_height_of_forall sW sY hsW hsY f (genericPoint W)
    (hmin _)
  rw [hf] at hξ
  rw [hN] at h1 h3
  rw [← h4, ← hξ, h3, ← hh] at h2
  have e1 : height w + coheight w = N := by exact_mod_cast h1
  have e2 : height w + coheight (f w) = N := by exact_mod_cast h2
  have hne : height w ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top N) (le_self_add.trans e1.le)
  exact WithTop.add_left_cancel hne (e2.trans e1.symm)

/-- Closed immersions have residue degree one. -/
private theorem residueDegree_eq_one_of_isClosedImmersion {X Y : Scheme.{u}} (e : Y ⟶ X)
    [IsClosedImmersion e] (y : Y) : e.residueDegree y = 1 := by
  have h := rawCyclePushforwardCoeff_eq_one_of_isClosedImmersion e y
  rw [rawCyclePushforwardCoeff_eq_ite] at h
  split_ifs at h with h'
  · exact absurd h zero_ne_one
  · exact_mod_cast h

section Coefficient

variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsIntegral X]
  (hp : FiniteType p) [IsSeparated p] {n : ℕ} (hn : topologicalKrullDim X = n) {V : Scheme.{u}}
  [IsIntegral V] (i : V ⟶ X) [IsClosedImmersion i] {r : ℕ} (hV : codim (Set.range i) + 1 = r)

/-- **Coefficients of pushed principal divisors.** Let `i : V ⟶ X` be an integral closed
subvariety of a variety `X` over `k`, with normalization `ν : Ṽ ⟶ V`, and let `g` be a nonzero
rational function on `V`. The coefficient at `x ∈ X` of the pushforward to `X` of the principal
divisor of `ν^♯ g` on `Ṽ` is `∑_{i(y) = x} ord_y(g)`: the order of `g` at the point of `V` over
`x`, if any, and `0` otherwise. -/
theorem subvarietyNormalizationPushforward_principalDivisor_apply [IsLocallyNoetherian V]
    (hν : absoluteNormalizationMap V (genericPoint (absoluteNormalization V)) = genericPoint V)
    (g : V.functionField) (hg : g ≠ 0) (x : X) :
    (subvarietyNormalizationPushforward p hp hn i hV
      (weilDivisorToCodimOneCycles (satisfiesConditionStar_absoluteNormalization p hp i)
        ((absoluteNormalization V).principalDivisor
          (satisfiesConditionStar_absoluteNormalization p hp i)
          (Units.mk0 ((absoluteNormalizationMap V).genericFunctionFieldMap hν g)
            ((map_ne_zero_iff _ ((absoluteNormalizationMap V).genericFunctionFieldMap
              hν).hom.injective).mpr hg)))) : AlgebraicCycle X ℤ) x =
      ∑ᶠ y ∈ i ⁻¹' {x}, V.ord g y := by
  classical
  set hS := satisfiesConditionStar_absoluteNormalization p hp i
  have := hS.isNoetherian
  have := hp.1
  have := hp.2
  have hVp : FiniteType (i ≫ p) := ⟨inferInstance, inferInstance⟩
  set ν' := absoluteNormalizationMap V
  set ν := subvarietyNormalizationMap i
  have hfinν' := isFinite_absoluteNormalizationMap_of_isClosedImmersion p hp i
  have hfinν := isFinite_subvarietyNormalizationMap p hp i
  have hp' := finiteType_subvarietyNormalizationMap_comp p hp i
  set G := ν'.genericFunctionFieldMap hν g
  have hcoeff : ∀ w, rawCyclePushforwardCoeff ν w = ν'.residueDegree w := by
    intro w
    have hmin : ∀ z, z ≤ w → ν z = ν w → z = w := fun z hz hzw ↦
      ((ν.isDiscrete_preimage_singleton (ν w)).eq_of_specializes (show w ⤳ z from hz) rfl
        hzw).symm
    have hh := FlatEquidimensional.height_eq_height_of_forall (ν ≫ p) p hp' hp ν w hmin
    rw [rawCyclePushforwardCoeff_eq_ite, if_neg (by rw [← hh]; exact lt_irrefl _)]
    change (((ν' ≫ i).residueDegree w : ℕ) : ℤ) = _
    rw [residueDegree_comp, residueDegree_eq_one_of_isClosedImmersion, one_mul]
  -- the coefficient is a sum over the fibre of `ν` over `x`
  have hL : (subvarietyNormalizationPushforward p hp hn i hV
      (weilDivisorToCodimOneCycles hS ((absoluteNormalization V).principalDivisor hS
        (Units.mk0 G ((map_ne_zero_iff _ (ν'.genericFunctionFieldMap
          hν).hom.injective).mpr hg)))) : AlgebraicCycle X ℤ) x =
      ∑ᶠ w ∈ ν ⁻¹' {x}, (absoluteNormalization V).ord G w * (ν'.residueDegree w : ℤ) := by
    rw [coe_subvarietyNormalizationPushforward, Function.locallyFinsuppWithin.coe_sum,
      Finset.sum_apply]
    simp only [Function.locallyFinsuppWithin.coe_zsmul, Pi.smul_apply,
      rawCyclePushforwardGenerator, Function.locallyFinsuppWithin.single_apply, smul_eq_mul]
    rw [← finsum_eq_sum_of_support_subset]
    · rw [finsum_mem_def]
      refine finsum_congr fun w ↦ ?_
      by_cases hw : ν w = x
      · rw [Set.indicator_of_mem (show w ∈ ν ⁻¹' {x} from hw), if_pos hw.symm, hcoeff]
        rfl
      · rw [Set.indicator_of_notMem (show w ∉ ν ⁻¹' {x} from hw), if_neg (Ne.symm hw), mul_zero]
    · intro w hw
      rw [Set.Finite.coe_toFinset]
      exact left_ne_zero_of_mul hw
  rw [hL]
  by_cases hx : x ∈ Set.range i
  · obtain ⟨y, rfl⟩ := hx
    have hfib : ν ⁻¹' {i y} = ν' ⁻¹' {y} := by
      ext w
      change (ν' ≫ i) w = i y ↔ ν' w = y
      rw [Scheme.Hom.comp_apply]
      exact i.isClosedEmbedding.injective.eq_iff
    have hi : i ⁻¹' {i y} = {y} := by
      ext y'
      exact i.isClosedEmbedding.injective.eq_iff
    rw [hfib, hi, finsum_mem_singleton]
    by_cases hy : coheight y = 1
    · exact fibreOrdFormula_absoluteNormalizationMap (i ≫ p) hVp hν hy g hg
    · rw [Scheme.ord_eq_zero_of_coheight_neq_one hy]
      refine finsum_mem_eq_zero_of_forall_eq_zero fun w hw ↦ ?_
      have hc := coheight_apply_eq_of_isFinite (ν ≫ p) (i ≫ p) hp' hVp ν' hν
        (topologicalKrullDim_absoluteNormalization_eq p hp hn i hV).1 w
      rw [show ν' w = y from hw] at hc
      rw [Scheme.ord_eq_zero_of_coheight_neq_one (fun h ↦ hy (hc.trans h)), zero_mul]
  · have h1 : ν ⁻¹' {x} = ∅ := by
      ext w
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro h
      exact hx ⟨ν' w, h⟩
    have h2 : i ⁻¹' {x} = ∅ := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro h
      exact hx ⟨y, h⟩
    rw [h1, h2, finsum_mem_empty, finsum_mem_empty]

end Coefficient

end Hartshorne

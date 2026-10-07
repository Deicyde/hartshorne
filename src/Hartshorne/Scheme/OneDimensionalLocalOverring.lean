/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Adjoin.FG
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# A one-dimensional local overring

The local-algebra construction used in Hartshorne II, Exercise 4.11(a).
-/

namespace Hartshorne

open IsLocalRing

universe u

noncomputable section

/-- A one-dimensional Noetherian local domain dominating `A` inside its fraction field `K`. -/
structure OneDimensionalLocalOverring
    (A K : Type u) [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] where
  B : Type u
  [commRing : CommRing B]
  [domain : IsDomain B]
  [noetherian : IsNoetherianRing B]
  [localRing : IsLocalRing B]
  [algebraAB : Algebra A B]
  [algebraBK : Algebra B K]
  [tower : IsScalarTower A B K]
  [fractionRing : IsFractionRing B K]
  [dominates : IsLocalHom (algebraMap A B)]
  dimension : ringKrullDim B = 1

attribute [instance] OneDimensionalLocalOverring.commRing
  OneDimensionalLocalOverring.domain OneDimensionalLocalOverring.noetherian
  OneDimensionalLocalOverring.localRing OneDimensionalLocalOverring.algebraAB
  OneDimensionalLocalOverring.algebraBK OneDimensionalLocalOverring.tower
  OneDimensionalLocalOverring.fractionRing OneDimensionalLocalOverring.dominates

private lemma exists_pivot
    {A V : Type*} [CommRing A] [CommRing V] [IsDomain V] [ValuationRing V]
    (f : A →+* V) (hf : Function.Injective f) (s : Finset A)
    (hs : ∃ x ∈ s, x ≠ 0) :
    ∃ x ∈ s, x ≠ 0 ∧ ∀ y ∈ s, f x ∣ f y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert a s ha ih =>
      by_cases hs0 : ∃ x ∈ s, x ≠ 0
      · obtain ⟨x, hxs, hx0, hx⟩ := ih hs0
        rcases ValuationRing.dvd_total (f a) (f x) with hax | hxa
        · have ha0 : a ≠ 0 := by
            intro e
            subst e
            simp only [map_zero, zero_dvd_iff] at hax
            exact hx0 (hf (by simpa using hax))
          refine ⟨a, Finset.mem_insert_self a s, ha0, ?_⟩
          intro y hy
          rw [Finset.mem_insert] at hy
          rcases hy with rfl | hy
          · exact dvd_rfl
          · exact hax.trans (hx y hy)
        · refine ⟨x, Finset.mem_insert_of_mem hxs, hx0, ?_⟩
          intro y hy
          rw [Finset.mem_insert] at hy
          rcases hy with rfl | hy
          · exact hxa
          · exact hx y hy
      · have ha0 : a ≠ 0 := by
          intro e
          subst e
          apply hs0
          simpa using hs
        refine ⟨a, Finset.mem_insert_self a s, ha0, ?_⟩
        intro y hy
        rw [Finset.mem_insert] at hy
        rcases hy with rfl | hy
        · exact dvd_rfl
        · have : y = 0 := not_ne_iff.mp fun hy0 ↦ hs0 ⟨y, hy, hy0⟩
          subst y
          simp

private theorem exists_blowupChart
    (A K : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsLocalRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    (hm : maximalIdeal A ≠ ⊥) :
    ∃ (s : Finset A) (x : A) (A' : Subalgebra A K),
      Ideal.span (s : Set A) = maximalIdeal A ∧ x ∈ s ∧ x ≠ 0 ∧
      A'.FG ∧ ¬ IsUnit (algebraMap A A' x) ∧
      ∀ y ∈ s, algebraMap A A' y ∈ Ideal.span {algebraMap A A' x} := by
  classical
  obtain ⟨x₀, hx₀m, hx₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  obtain ⟨s₀, hs₀fin, hs₀span⟩ :=
    Submodule.fg_def.mp (maximalIdeal A).fg_of_isNoetherianRing
  let sSet : Set A := insert x₀ s₀
  have hsSetfin : sSet.Finite := hs₀fin.insert x₀
  let s : Finset A := hsSetfin.toFinset
  have hscoe : (s : Set A) = sSet := Set.Finite.coe_toFinset hsSetfin
  have hs₀span' : Ideal.span s₀ = maximalIdeal A := by
    ext a
    change a ∈ Submodule.span A s₀ ↔ a ∈ maximalIdeal A
    rw [hs₀span]
  have hsspan : Ideal.span (s : Set A) = maximalIdeal A := by
    rw [hscoe, show sSet = {x₀} ∪ s₀ by ext; simp [sSet], Ideal.span_union,
      hs₀span', sup_eq_right]
    exact (maximalIdeal A).span_singleton_le_iff_mem.mpr hx₀m
  obtain ⟨V, hAV, hlocal⟩ :=
    IsLocalRing.exists_factor_valuationRing (algebraMap A K)
  let f : A →+* V := (algebraMap A K).codRestrict V.toSubring hAV
  have hf : Function.Injective f := by
    intro a b hab
    apply IsFractionRing.injective A K
    exact congr_arg Subtype.val hab
  have hsnonzero : ∃ x ∈ s, x ≠ 0 := by
    refine ⟨x₀, ?_, hx₀⟩
    change x₀ ∈ (s : Set A)
    rw [hscoe]
    exact Set.mem_insert x₀ s₀
  obtain ⟨x, hxs, hx, hxdiv⟩ := exists_pivot f hf s hsnonzero
  let ratios : Finset K := s.image fun y ↦ algebraMap A K y / algebraMap A K x
  let A' : Subalgebra A K := Algebra.adjoin A (ratios : Set K)
  have hA'fg : A'.FG := by
    dsimp only [A']
    exact Subalgebra.fg_adjoin_finset ratios
  let V' : Subalgebra A K :=
    { V.toSubring with
      algebraMap_mem' := hAV }
  have hA'V : A' ≤ V' := by
    apply Algebra.adjoin_le
    intro z hz
    rw [Finset.mem_coe] at hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨c, hc⟩ := hxdiv y hy
    have hxK : algebraMap A K x ≠ 0 := by
      simpa using (IsFractionRing.injective A K).ne hx
    have heq : algebraMap A K y / algebraMap A K x = (c : K) := by
      rw [div_eq_iff hxK]
      simpa [f, mul_comm] using congr_arg Subtype.val hc
    rw [heq]
    exact c.2
  have hxm : x ∈ maximalIdeal A := by
    rw [← hsspan]
    exact Ideal.subset_span (by simpa using hxs)
  have hxnonunit : ¬ IsUnit (algebraMap A A' x) := by
    intro hxu
    let j : A' →+* V :=
      { toFun := fun z ↦ ⟨z.1, hA'V z.2⟩
        map_one' := rfl
        map_mul' := fun _ _ ↦ rfl
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl }
    have hxu' : IsUnit (j (algebraMap A A' x)) := hxu.map j
    have hfxm : f x ∈ maximalIdeal V :=
      map_nonunit f x hxm
    have hj : j (algebraMap A A' x) = f x := by
      apply Subtype.ext
      rfl
    rw [hj] at hxu'
    exact hfxm hxu'
  have hyspan : ∀ y ∈ s,
      algebraMap A A' y ∈ Ideal.span {algebraMap A A' x} := by
    intro y hy
    let r : A' := ⟨algebraMap A K y / algebraMap A K x,
      Algebra.subset_adjoin (R := A) (by
        rw [Finset.mem_coe]
        exact Finset.mem_image.mpr ⟨y, hy, rfl⟩)⟩
    rw [Ideal.mem_span_singleton]
    refine ⟨r, ?_⟩
    apply Subtype.ext
    dsimp only [r]
    change algebraMap A K y =
      algebraMap A K x * (algebraMap A K y / algebraMap A K x)
    rw [mul_comm]
    exact (div_mul_cancel₀ (algebraMap A K y) (by
      simpa using (IsFractionRing.injective A K).ne hx)).symm
  exact ⟨s, x, A', hsspan, hxs, hx, hA'fg, hxnonunit, hyspan⟩

/-- **One-dimensional local overring.** A nonfield Noetherian local domain admits a
one-dimensional Noetherian local overring in the same fraction field which dominates it. -/
theorem exists_oneDimensionalLocalOverring
    (A K : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsLocalRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    (hm : maximalIdeal A ≠ ⊥) :
    Nonempty (OneDimensionalLocalOverring A K) := by
  classical
  obtain ⟨s, x, A', hsspan, hxs, hx, hA'fg, hxnonunit, hyspan⟩ :=
    exists_blowupChart A K hm
  let _ : IsNoetherianRing A' := isNoetherianRing_of_fg hA'fg
  let I : Ideal A' := Ideal.span {algebraMap A A' x}
  have hI : I ≠ ⊤ := by
    exact Ideal.span_singleton_ne_top hxnonunit
  obtain ⟨p, hp⟩ := I.nonempty_minimalPrimes hI
  let _ : p.IsPrime := hp.isPrime
  have hcontraction : p.comap (algebraMap A A') = maximalIdeal A := by
    apply le_antisymm
    · apply le_maximalIdeal
      rw [ne_eq, Ideal.eq_top_iff_one, Ideal.mem_comap]
      simpa [Ideal.eq_top_iff_one] using hp.isPrime.ne_top
    · rw [← hsspan, Ideal.span_le]
      intro y hy
      change algebraMap A A' y ∈ p
      exact hp.le (hyspan y hy)
  have hS : p.primeCompl ≤ nonZeroDivisors A' := by
    intro a ha
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro ha0
    apply ha
    simp [ha0]
  let B : Subalgebra A' K := Localization.subalgebra.ofField K p.primeCompl hS
  let _ : IsLocalization p.primeCompl B := by
    dsimp only [B]
    infer_instance
  let _ : Algebra A B :=
    ((algebraMap A' B).comp (algebraMap A A')).toAlgebra
  let _ : IsScalarTower A A' B := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower A B K := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsLocalRing B := IsLocalization.AtPrime.isLocalRing B p
  let _ : IsNoetherianRing B :=
    IsLocalization.isNoetherianRing p.primeCompl B inferInstance
  have hdom : IsLocalHom (algebraMap A B) := by
    apply ((IsLocalRing.local_hom_TFAE (algebraMap A B)).out 4 0).mp
    change (maximalIdeal B).comap
      ((algebraMap A' B).comp (algebraMap A A')) = maximalIdeal A
    rw [← Ideal.comap_comap]
    have hmax := IsLocalization.AtPrime.under_maximalIdeal B p
    change (maximalIdeal B).comap (algebraMap A' B) = p at hmax
    rw [hmax, hcontraction]
  let _ : IsLocalHom (algebraMap A B) := hdom
  have hpne : p ≠ ⊥ := by
    intro hpbot
    have hpx : algebraMap A A' x ∈ p :=
      hp.le (Ideal.mem_span_singleton_self (algebraMap A A' x))
    rw [hpbot, Ideal.mem_bot] at hpx
    apply hx
    apply IsFractionRing.injective A K
    have hpx' := congr_arg (fun z : A' ↦ (z : K)) hpx
    change algebraMap A K x = 0 at hpx'
    simpa using hpx'
  have hpheight : p.height = 1 := by
    apply le_antisymm
    · exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes I p hp
    · rw [Order.one_le_iff_ne_zero]
      intro hpzero
      exact hpne (Ideal.height_eq_zero_iff_eq_bot.mp hpzero)
  have hdim : ringKrullDim B = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p B, hpheight]
    simp
  exact ⟨{
    B := B
    dimension := hdim }⟩

end

end Hartshorne

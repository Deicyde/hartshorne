/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Curve.FrobeniusFinite
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Finiteness of purely inseparable normalizations

This file proves the purely inseparable step in the finiteness theorem for
normalizations of affine domains.  In positive characteristic, a uniform
Frobenius exponent for a finite purely inseparable field extension is combined
with finiteness over the Frobenius image.  The characteristic-zero case is
handled separately: a purely inseparable finite extension is then trivial.
-/

namespace Hartshorne

noncomputable section

universe u v w x

/-- A finite-dimensional purely inseparable extension has a single Frobenius
exponent that sends every element into the base field. -/
theorem exists_uniform_pow_mem_of_finiteDimensional
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (q : ℕ) [ExpChar K q]
    [FiniteDimensional K L] [IsPurelyInseparable K L] :
    ∃ e : ℕ, ∀ x : L, x ^ q ^ e ∈ (algebraMap K L).range :=
  ⟨IsPurelyInseparable.exponent K L,
    IsPurelyInseparable.exponent_def' K q⟩

section Normalization

variable (k : Type u) (A : Type v) (K : Type w) (L : Type x)
  [Field k] [IsAlgClosed k]
  [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
  [IsIntegrallyClosed A]
  [Field K] [Algebra A K] [IsFractionRing A K]
  [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  [FiniteDimensional K L] [IsPurelyInseparable K L]

include K

omit [IsAlgClosed k] [Algebra.FiniteType k A] [FiniteDimensional K L] in
/-- In characteristic zero, a finite purely inseparable field extension is
trivial, and normality identifies its integral closure with `A`. -/
theorem algebraMap_integralClosure_surjective_of_charZero [CharZero k] :
    Function.Surjective (algebraMap A (integralClosure A L)) := by
  let _ : CharZero A :=
    charZero_of_injective_ringHom (algebraMap k A).injective
  let _ : CharZero K :=
    charZero_of_injective_ringHom (IsFractionRing.injective A K)
  intro b
  obtain ⟨x, hx⟩ :=
    IsPurelyInseparable.surjective_algebraMap_of_isSeparable K L (b : L)
  have hxIntegral : IsIntegral A x := by
    apply (isIntegral_algHom_iff
      (IsScalarTower.toAlgHom A K L) (algebraMap K L).injective).mp
    change IsIntegral A (algebraMap K L x)
    rw [hx]
    exact b.property
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hxIntegral
  refine ⟨a, Subtype.ext ?_⟩
  change algebraMap A L a = (b : L)
  rw [IsScalarTower.algebraMap_apply A K L, ha, hx]

/-- In positive characteristic, the integral closure in a finite purely
inseparable extension is finite.  The proof uses the explicit extension
exponent and finiteness over the corresponding Frobenius image. -/
theorem moduleFinite_integralClosure_of_isPurelyInseparable_of_charP
    (p : ℕ) [Fact p.Prime] [CharP k p] :
    Module.Finite A (integralClosure A L) := by
  let _ : ExpChar k p := ExpChar.prime Fact.out
  let _ : ExpChar A p :=
    expChar_of_injective_algebraMap (algebraMap k A).injective p
  let _ : ExpChar K p :=
    expChar_of_injective_algebraMap (IsFractionRing.injective A K) p
  let _ : ExpChar L p :=
    expChar_of_injective_algebraMap (algebraMap K L).injective p
  let e := IsPurelyInseparable.exponent K L
  let B := integralClosure A L
  let fLK : L →+* K :=
    IsPurelyInseparable.iterateFrobenius K L p (le_refl e)
  let fBK : B →+* K := fLK.comp B.val.toRingHom
  have hfBK_mem (b : B) : fBK b ∈ (algebraMap A K).range := by
    apply IsIntegrallyClosed.algebraMap_eq_of_integral
    apply (isIntegral_algHom_iff
      (IsScalarTower.toAlgHom A K L) (algebraMap K L).injective).mp
    change IsIntegral A (algebraMap K L (fLK (b : L)))
    rw [IsPurelyInseparable.algebraMap_iterateFrobenius K p (le_refl e)]
    exact b.property.pow _
  let AK := (algebraMap A K).range
  let aToAK : A →+* AK := (algebraMap A K).rangeRestrict
  have haToAK_bij : Function.Bijective aToAK := by
    refine ⟨?_, RingHom.rangeRestrict_surjective _⟩
    intro x y h
    apply IsFractionRing.injective A K
    exact congrArg Subtype.val h
  let equivAK : A ≃+* AK := RingEquiv.ofBijective aToAK haToAK_bij
  let fBAK : B →+* AK := fBK.codRestrict AK hfBK_mem
  let g : B →+* A := equivAK.symm.toRingHom.comp fBAK
  have hg_spec (b : B) : algebraMap A K (g b) = fBK b := by
    have h := equivAK.apply_symm_apply (fBAK b)
    exact congrArg Subtype.val h
  have hg_algebraMap (a : A) :
      g (algebraMap A B a) = frobeniusPowerHom k A p e a := by
    apply IsFractionRing.injective A K
    rw [hg_spec, frobeniusPowerHom_apply]
    change fLK (algebraMap A L a) = algebraMap A K (a ^ p ^ e)
    rw [IsScalarTower.algebraMap_apply A K L,
      IsPurelyInseparable.iterateFrobenius_algebraMap, map_pow]
  have hfBK_inj : Function.Injective fBK := by
    intro x y hxy
    apply Subtype.ext
    apply iterateFrobenius_inj L p e
    change (x : L) ^ p ^ e = (y : L) ^ p ^ e
    rw [← IsPurelyInseparable.algebraMap_iterateFrobenius K p (le_refl e),
      ← IsPurelyInseparable.algebraMap_iterateFrobenius K p (le_refl e)]
    exact congrArg (algebraMap K L) hxy
  have hg_inj : Function.Injective g := by
    intro x y hxy
    apply hfBK_inj
    rw [← hg_spec, ← hg_spec, hxy]
  let P := frobeniusPowerSubalgebra k A p e
  let sigma : A →+* P :=
    (frobeniusPowerHom k A p e).codRestrict P fun a =>
      (mem_frobeniusPowerSubalgebra_iff k A p e _).2
        ⟨a, (frobeniusPowerHom_apply k A p e a).symm⟩
  have hsigma_surj : Function.Surjective sigma := by
    intro y
    obtain ⟨x, hx⟩ :=
      (mem_frobeniusPowerSubalgebra_iff k A p e y).1 y.property
    refine ⟨x, Subtype.ext ?_⟩
    exact (frobeniusPowerHom_apply k A p e x).trans hx
  have hsigma_inj : Function.Injective sigma := by
    intro x y hxy
    apply iterateFrobenius_inj A p e
    change x ^ p ^ e = y ^ p ^ e
    simpa [sigma, frobeniusPowerHom_apply] using congrArg Subtype.val hxy
  let _ : RingHomSurjective sigma := ⟨hsigma_surj⟩
  let _ : IsNoetherianRing A :=
    Algebra.FiniteType.isNoetherianRing k A
  let _ : IsNoetherianRing P :=
    isNoetherianRing_of_ringEquiv A
      (RingEquiv.ofBijective sigma ⟨hsigma_inj, hsigma_surj⟩)
  let _ : Module.Finite P A :=
    moduleFinite_frobeniusPowerSubalgebra k A p e
  let C : Subalgebra P A :=
    { __ := g.range
      algebraMap_mem' := fun r => by
        obtain ⟨x, hx⟩ :=
          (mem_frobeniusPowerSubalgebra_iff k A p e r).1 r.property
        refine ⟨algebraMap A B x, ?_⟩
        change g (algebraMap A B x) = (r : A)
        rw [hg_algebraMap, frobeniusPowerHom_apply]
        exact hx }
  let phi : B →ₛₗ[sigma] C :=
    { toFun := fun b => ⟨g b, ⟨b, rfl⟩⟩
      map_add' := fun x y => by
        apply Subtype.ext
        exact g.map_add x y
      map_smul' := fun a b => by
        apply Subtype.ext
        simp only [Algebra.smul_def]
        change g (algebraMap A B a * b) = (sigma a : A) * g b
        rw [g.map_mul, hg_algebraMap]
        rfl }
  have hphi_bij : Function.Bijective phi := by
    constructor
    · intro x y hxy
      apply hg_inj
      exact congrArg Subtype.val hxy
    · intro z
      obtain ⟨b, hb⟩ := z.property
      exact ⟨b, Subtype.ext hb⟩
  let _ : IsNoetherian P A := inferInstance
  let _ : IsNoetherian P C :=
    isNoetherian_of_submodule_of_noetherian P A C.toSubmodule inferInstance
  let _ : Module.Finite P C := inferInstance
  exact (LinearMap.finite_iff_of_bijective phi hphi_bij).2 inferInstance

include k

/-- The integral closure of a finite-type normal domain in a finite purely
inseparable extension of its fraction field is module-finite. -/
theorem moduleFinite_integralClosure_of_isPurelyInseparable :
    Module.Finite A (integralClosure A L) := by
  let ⟨p, _⟩ := ExpChar.exists k
  rcases ‹ExpChar k p› with _ | ⟨hp⟩
  · rw [← RingHom.finite_algebraMap]
    exact RingHom.Finite.of_surjective _
      (algebraMap_integralClosure_surjective_of_charZero k A K L)
  · let _ : Fact p.Prime := ⟨hp⟩
    exact moduleFinite_integralClosure_of_isPurelyInseparable_of_charP
      k A K L p

/-- An explicit uniform Frobenius exponent together with a finite family that
spans the integral closure.  In characteristic zero the exponential
characteristic is `1`, so the exponent statement records the triviality of the
purely inseparable extension. -/
theorem exists_uniformExponent_and_fin_spanningFamily_integralClosure
    (q : ℕ) [ExpChar K q] :
    ∃ (e n : ℕ) (b : Fin n → integralClosure A L),
      (∀ x : L, x ^ q ^ e ∈ (algebraMap K L).range) ∧
        Submodule.span A (Set.range b) = ⊤ := by
  let _ : Module.Finite A (integralClosure A L) :=
    moduleFinite_integralClosure_of_isPurelyInseparable k A K L
  obtain ⟨n, b, hb⟩ :=
    Module.Finite.exists_fin (R := A) (M := integralClosure A L)
  exact ⟨IsPurelyInseparable.exponent K L, n, b,
    IsPurelyInseparable.exponent_def' K q, hb⟩

/-- Positive-characteristic form of the explicit exponent-and-spanning-family
result, with the characteristic inherited from the algebraically closed base
field. -/
theorem exists_frobeniusExponent_and_fin_spanningFamily_integralClosure_of_charP
    (p : ℕ) [Fact p.Prime] [CharP k p] :
    ∃ (e n : ℕ) (b : Fin n → integralClosure A L),
      (∀ x : L, x ^ p ^ e ∈ (algebraMap K L).range) ∧
        Submodule.span A (Set.range b) = ⊤ := by
  let _ : ExpChar k p := ExpChar.prime Fact.out
  let _ : ExpChar A p :=
    expChar_of_injective_algebraMap (algebraMap k A).injective p
  let _ : ExpChar K p :=
    expChar_of_injective_algebraMap (IsFractionRing.injective A K) p
  exact exists_uniformExponent_and_fin_spanningFamily_integralClosure
    k A K L p

end Normalization

end

end Hartshorne

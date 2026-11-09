/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.OneDimensionalLocalOverring
import Hartshorne.Curve.KrullAkizuki
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.LocalRing.LocalSubring
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# A dominating DVR in a finitely generated extension

Hartshorne, *Algebraic Geometry*, II, Exercise 4.11(a), in a repaired form
excluding only the false edge case (`A` a field and `L/K` algebraic).

Let `(A, 𝔪)` be a Noetherian local domain with fraction field `K`, and let `L/K`
be a finitely generated field extension, and suppose that `𝔪 ≠ 0` or `L` is not
algebraic over `K`. Then a nonfield discrete valuation ring of `L` with fraction
field `L` dominates the image of `A`.

## Proof

Everything happens inside `L`. Write `L = Frac(A)(S)` with `S` finite and argue
by induction on the size of `S`.

* If some `s ∈ S` is transcendental over `Frac(A)`, replace `A` by the
  localization of `A[s]` at the extension of `𝔪`; this is again a Noetherian
  local domain with nonzero maximal ideal, it dominates `A`, and it contains `s`,
  so `S \ {s}` generates `L` over its fraction field
  (`exists_transcendental_step`).
* Otherwise `L` is finite over `Frac(A)`. Take a one-dimensional Noetherian
  local overring `B` of `A` dominating it; the integral closure `C` of `B` in `L`
  is Noetherian of dimension at most one by Krull--Akizuki, hence Dedekind.
  Lying over gives a prime `Q` of `C` above the maximal ideal of `B`, and `C_Q`
  is the required DVR (`hasDominatingDVR_of_finiteDimensional`).

If `𝔪 = 0` and `t ∈ L` is transcendental over `K`, the localization of `K[t]` at
`(t)` has nonzero maximal ideal (`exists_localSubring_of_transcendental`); the
case above applies to it, and domination of the field `A` is just containment.

## Main results

* `Hartshorne.exists_dominating_dvr_of_fg_of_ne_bot_or_transcendental`: the exercise, assuming
  `𝔪 ≠ 0` or that `L` is not algebraic over `K`.
* `Hartshorne.exists_dominating_dvr_of_fg`: its special case `𝔪 ≠ 0`.
* `Hartshorne.hasDominatingDVR_of_closure_eq_top`: its form for subrings of `L`.
-/

namespace Hartshorne

open IsLocalRing

noncomputable section

universe u

variable {L : Type u} [Field L]

/-- A subring `A` of a field `L` is dominated by a nonfield discrete valuation
ring of `L` with fraction field `L`. -/
def HasDominatingDVR (A : Subring L) : Prop :=
  ∃ R : Subring L, IsDiscreteValuationRing R ∧ IsFractionRing R L ∧
    ∃ h : A ≤ R, IsLocalHom (Subring.inclusion h)

/-- The fraction field of a subring of `L`, as a subfield of `L`. -/
abbrev subringFractionField (A : Subring L) : Subfield L :=
  Subfield.closure (A : Set L)

theorem le_subringFractionField (A : Subring L) :
    A ≤ (subringFractionField A).toSubring :=
  fun _ hx => Subfield.subset_closure hx

instance (A : Subring L) : Algebra A (subringFractionField A) :=
  (Subring.inclusion (le_subringFractionField A)).toAlgebra

instance (A : Subring L) : IsScalarTower A (subringFractionField A) L :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance (A : Subring L) : IsFractionRing A (subringFractionField A) := by
  have : FaithfulSMul A (subringFractionField A) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr fun x y h => by
      apply Subtype.ext
      exact congrArg (fun z : subringFractionField A => (z : L)) h
  refine IsFractionRing.of_field A _ fun z => ?_
  obtain ⟨y, hy, w, hw, hz⟩ := Subfield.mem_closure_iff.mp z.2
  rw [Subring.closure_eq] at hy hw
  refine ⟨⟨y, hy⟩, ⟨w, hw⟩, ?_⟩
  apply Subtype.ext
  simp only [Subfield.coe_div]
  exact hz.symm

/-- **The finite case.** A Noetherian local subring with nonzero maximal ideal,
whose fraction field has `L` as a finite extension, is dominated by a DVR of
`L`. -/
theorem hasDominatingDVR_of_finiteDimensional (A : Subring L) [IsLocalRing A]
    [IsNoetherianRing A] (hm : maximalIdeal A ≠ ⊥)
    [FiniteDimensional (subringFractionField A) L] : HasDominatingDVR A := by
  classical
  set K := subringFractionField A
  obtain ⟨B₀⟩ := exists_oneDimensionalLocalOverring A K hm
  let B := B₀.B
  let : Algebra B L := ((algebraMap K L).comp (algebraMap B K)).toAlgebra
  have : IsScalarTower B K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Ring.KrullDimLE 1 B := Ring.krullDimLE_iff.mpr (by rw [B₀.dimension]; rfl)
  have hBinj : Function.Injective (algebraMap B L) := by
    rw [IsScalarTower.algebraMap_eq B K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective B K)
  let C := integralClosure B L
  have : NoZeroSMulDivisors C L := by
    constructor
    intro c x hcx
    rw [Algebra.smul_def] at hcx
    rcases mul_eq_zero.mp hcx with hc | hx
    · exact Or.inl (Subtype.ext hc)
    · exact Or.inr hx
  have hKA := krull_akizuki B K L C
  have : IsNoetherianRing C := hKA.1
  have : Ring.DimensionLEOne C := hKA.2.2
  have : IsIntegrallyClosed C := integralClosure.isIntegrallyClosedOfFiniteExtension K
  have : IsFractionRing C L := integralClosure.isFractionRing_of_finite_extension K L
  have : IsDedekindDomain C := {}
  have hCinj : Function.Injective (algebraMap B C) := by
    intro x y hxy
    apply hBinj
    rw [IsScalarTower.algebraMap_apply B C L, hxy, ← IsScalarTower.algebraMap_apply]
  obtain ⟨Q, -, hQprime, hQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
    (S := C) (maximalIdeal B) ⊥ (by
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_bot, ← map_zero (algebraMap B C)] at hx
      rw [hCinj hx]
      exact zero_mem _)
  have hBnf : maximalIdeal B ≠ ⊥ := by
    intro h
    have hf : IsField B := (isField_iff_maximalIdeal_eq).mpr h
    have := B₀.dimension
    rw [ringKrullDim_eq_zero_of_isField hf] at this
    exact zero_ne_one this
  have hQne : Q ≠ ⊥ := by
    rintro rfl
    apply hBnf
    rw [← hQ]
    ext x
    rw [Ideal.mem_comap, Ideal.mem_bot, Ideal.mem_bot, ← map_zero (algebraMap B C)]
    exact hCinj.eq_iff
  have hS : Q.primeCompl ≤ nonZeroDivisors C := Q.primeCompl_le_nonZeroDivisors
  let R' := Localization.subalgebra.ofField L Q.primeCompl hS
  have : IsLocalization.AtPrime R' Q :=
    Localization.subalgebra.isLocalization_ofField L Q.primeCompl hS
  have : IsLocalRing R' := IsLocalization.AtPrime.isLocalRing R' Q
  have hdvr : IsDiscreteValuationRing R' :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain C hQne R'
  refine ⟨R'.toSubring, hdvr, inferInstanceAs (IsFractionRing R' L), ?_⟩
  have hval : ∀ x : A,
      ((algebraMap C R' (algebraMap B C (algebraMap A B x)) : R') : L) = x := by
    intro x
    change algebraMap B L (algebraMap A B x) = x
    rw [IsScalarTower.algebraMap_apply B K L, ← IsScalarTower.algebraMap_apply A B K]
    rfl
  have hle : A ≤ R'.toSubring := fun a ha => by
    have h := SetLike.coe_mem (algebraMap C R' (algebraMap B C (algebraMap A B ⟨a, ha⟩)))
    rw [hval ⟨a, ha⟩] at h
    exact h
  refine ⟨hle, ⟨fun x hx => ?_⟩⟩
  have heq : (Subring.inclusion hle x : L) =
      ((algebraMap C R' (algebraMap B C (algebraMap A B x)) : R') : L) := (hval x).symm
  have hx' : IsUnit (algebraMap C R' (algebraMap B C (algebraMap A B x))) := by
    have : Subring.inclusion hle x = algebraMap C R' (algebraMap B C (algebraMap A B x)) :=
      Subtype.ext heq
    rw [← this]
    exact hx
  by_contra hxu
  have hb : algebraMap A B x ∈ maximalIdeal B := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    exact fun hu => hxu (isUnit_of_map_unit _ _ hu)
  have hc : algebraMap B C (algebraMap A B x) ∈ Q := by
    rw [← Ideal.mem_comap, hQ]
    exact hb
  have hr := (IsLocalization.AtPrime.to_map_mem_maximal_iff R' Q _).mpr hc
  exact (mem_maximalIdeal _).mp hr hx'

/-- **The transcendental step.** Adjoining an element `s` transcendental over a
Noetherian local subring `A` and localizing at the extension of the maximal
ideal gives a Noetherian local subring with nonzero maximal ideal, containing
`s` and dominating `A`. -/
theorem exists_transcendental_step (A : Subring L) [IsLocalRing A] [IsNoetherianRing A]
    (hm : maximalIdeal A ≠ ⊥) (s : L) (hs : Transcendental A s) :
    ∃ A' : LocalSubring L, IsNoetherianRing A'.toSubring ∧
      maximalIdeal A'.toSubring ≠ ⊥ ∧ s ∈ A'.toSubring ∧
      ∃ h : A ≤ A'.toSubring, IsLocalHom (Subring.inclusion h) := by
  classical
  let T : Subalgebra A L := Algebra.adjoin A {s}
  let e : Polynomial A ≃+* T.toSubring := (Polynomial.algEquivOfTranscendental A s hs).toRingEquiv
  let P : Ideal T.toSubring := Ideal.map e (Ideal.map Polynomial.C (maximalIdeal A))
  have : P.IsPrime := Ideal.map_isPrime_of_equiv e
  have hT : IsNoetherianRing T.toSubring := isNoetherianRing_of_ringEquiv _ e
  let A' := LocalSubring.ofPrime T.toSubring P
  have hA'noeth : IsNoetherianRing A'.toSubring :=
    IsLocalization.isNoetherianRing P.primeCompl A'.toSubring hT
  have hAT : A ≤ T.toSubring := fun a ha =>
    Subalgebra.algebraMap_mem T (⟨a, ha⟩ : A)
  have hle : A ≤ A'.toSubring := hAT.trans (LocalSubring.le_ofPrime T.toSubring P)
  have hmax : ∀ x ∈ maximalIdeal A, Subring.inclusion hle x ∈ maximalIdeal A'.toSubring := by
    intro x hx
    have hxP : (⟨x, hAT x.2⟩ : T.toSubring) ∈ P := by
      have h1 : Polynomial.C x ∈ Ideal.map Polynomial.C (maximalIdeal A) :=
        Ideal.mem_map_of_mem _ hx
      have h2 := Ideal.mem_map_of_mem e h1
      convert h2 using 1
      apply Subtype.ext
      simp [e]
      rfl
    have := (IsLocalization.AtPrime.to_map_mem_maximal_iff A'.toSubring P _).mpr hxP
    convert this using 1
    apply Subtype.ext
    rfl
  refine ⟨A', hA'noeth, ?_, ?_, hle, ⟨fun x hx => ?_⟩⟩
  · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
    intro hbot
    have h := hmax x hx
    rw [hbot, Ideal.mem_bot] at h
    have h2 : ((Subring.inclusion hle x : A'.toSubring) : L) = 0 :=
      congrArg Subtype.val h
    exact hx0 (Subtype.ext h2)
  · exact LocalSubring.le_ofPrime T.toSubring P (Algebra.self_mem_adjoin_singleton A s)
  · by_contra hxu
    have hxm : x ∈ maximalIdeal A := by
      rw [mem_maximalIdeal, mem_nonunits_iff]
      exact hxu
    exact (mem_maximalIdeal _).mp (hmax x hxm) hx

/-- **A transcendental element over a field.** Localizing `K[t]` at `(t)`, for `t ∈ L`
transcendental over a field `K`, gives a Noetherian local subring of `L` with nonzero maximal
ideal containing the image of `K`. -/
theorem exists_localSubring_of_transcendental (K : Type*) [Field K] [Algebra K L]
    (t : L) (ht : Transcendental K t) :
    ∃ A' : LocalSubring L, IsNoetherianRing A'.toSubring ∧
      maximalIdeal A'.toSubring ≠ ⊥ ∧ ∀ k, algebraMap K L k ∈ A'.toSubring := by
  classical
  let T : Subalgebra K L := Algebra.adjoin K {t}
  let e : Polynomial K ≃+* T.toSubring :=
    (Polynomial.algEquivOfTranscendental K t ht).toRingEquiv
  have : (Ideal.span {(Polynomial.X : Polynomial K)}).IsPrime :=
    (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr Polynomial.prime_X
  let P : Ideal T.toSubring := Ideal.map e (Ideal.span {Polynomial.X})
  have : P.IsPrime := Ideal.map_isPrime_of_equiv e
  have hT : IsNoetherianRing T.toSubring := isNoetherianRing_of_ringEquiv _ e
  let A' := LocalSubring.ofPrime T.toSubring P
  have hA'noeth : IsNoetherianRing A'.toSubring :=
    IsLocalization.isNoetherianRing P.primeCompl A'.toSubring hT
  have hTA' : T.toSubring ≤ A'.toSubring := LocalSubring.le_ofPrime T.toSubring P
  refine ⟨A', hA'noeth, ?_, fun k => hTA' (Subalgebra.algebraMap_mem T k)⟩
  let t' : T.toSubring := ⟨t, Algebra.self_mem_adjoin_singleton K t⟩
  have ht'P : t' ∈ P := by
    have h := Ideal.mem_map_of_mem e
      (Ideal.mem_span_singleton_self (Polynomial.X : Polynomial K))
    convert h using 1
    exact (Polynomial.algEquivOfTranscendental_apply_X K t ht).symm
  have hmem := (IsLocalization.AtPrime.to_map_mem_maximal_iff A'.toSubring P t').mpr ht'P
  intro hbot
  rw [hbot, Ideal.mem_bot] at hmem
  have h0 : t = 0 := congrArg Subtype.val hmem
  exact ht (h0 ▸ isAlgebraic_zero)

/-- Domination is transitive. -/
theorem HasDominatingDVR.of_le {A A' : Subring L} (h : A ≤ A')
    [IsLocalHom (Subring.inclusion h)] (hA' : HasDominatingDVR A') : HasDominatingDVR A := by
  obtain ⟨R, hR, hRf, h', hloc⟩ := hA'
  refine ⟨R, hR, hRf, h.trans h', ?_⟩
  have : Subring.inclusion (h.trans h') = (Subring.inclusion h').comp (Subring.inclusion h) := by
    ext
    rfl
  rw [this]
  infer_instance

/-- If `L` is generated over the fraction field of `A` by finitely many
algebraic elements, then it is a finite extension of it. -/
theorem finiteDimensional_of_isAlgebraic (A : Subring L) (S : Finset L)
    (hS : Subfield.closure ((A : Set L) ∪ S) = ⊤)
    (halg : ∀ s ∈ S, IsAlgebraic (subringFractionField A) s) :
    FiniteDimensional (subringFractionField A) L := by
  set K := subringFractionField A
  have hfin : FiniteDimensional K (IntermediateField.adjoin K (S : Set L)) :=
    IntermediateField.finiteDimensional_adjoin fun x hx => (halg x hx).isIntegral
  have htop : IntermediateField.adjoin K (S : Set L) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hle : Subfield.closure ((A : Set L) ∪ S) ≤
        (IntermediateField.adjoin K (S : Set L)).toSubfield := by
      rw [Subfield.closure_le]
      rintro y (hy | hy)
      · exact IntermediateField.algebraMap_mem _ (⟨y, Subfield.subset_closure hy⟩ : K)
      · exact IntermediateField.subset_adjoin K _ hy
    exact hle (hS ▸ Subfield.mem_top x)
  rw [htop] at hfin
  exact (IntermediateField.topEquiv (F := K) (E := L)).toLinearEquiv.finiteDimensional

/-- The subring form of the theorem, by induction on the number of field
generators of `L` over the fraction field of `A`. -/
theorem hasDominatingDVR_of_closure_eq_top (n : ℕ) :
    ∀ (A : Subring L) [IsLocalRing A] [IsNoetherianRing A], maximalIdeal A ≠ ⊥ →
      ∀ S : Finset L, S.card = n → Subfield.closure ((A : Set L) ∪ S) = ⊤ →
        HasDominatingDVR A := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A _ _ hm S hcard hS
  by_cases halg : ∀ s ∈ S, IsAlgebraic (subringFractionField A) s
  · have := finiteDimensional_of_isAlgebraic A S hS halg
    exact hasDominatingDVR_of_finiteDimensional A hm
  · obtain ⟨s, hsS, hs⟩ : ∃ s ∈ S, ¬ IsAlgebraic (subringFractionField A) s := by
      by_contra hcon
      exact halg fun s hs => by
        by_contra h
        exact hcon ⟨s, hs, h⟩
    have hsA : Transcendental A s :=
      Transcendental.restrictScalars (IsFractionRing.injective A (subringFractionField A)) hs
    obtain ⟨A', hnoeth, hm', hsA', hle, hloc⟩ := exists_transcendental_step A hm s hsA
    have := hnoeth
    refine HasDominatingDVR.of_le hle ?_
    refine ih (S.erase s).card ?_ A'.toSubring hm' (S.erase s) rfl ?_
    · rw [Finset.card_erase_of_mem hsS, ← hcard]
      exact Nat.sub_lt (Finset.card_pos.mpr ⟨s, hsS⟩) one_pos
    · rw [eq_top_iff, ← hS, Subfield.closure_le]
      rintro y (hy | hy)
      · exact Subfield.subset_closure (Or.inl (hle hy))
      · by_cases hys : y = s
        · subst hys
          exact Subfield.subset_closure (Or.inl hsA')
        · exact Subfield.subset_closure (Or.inr (Finset.mem_erase.mpr ⟨hys, hy⟩))

/-- **Hartshorne II, Exercise 4.11(a)** (repaired). Let `(A, 𝔪)` be a Noetherian
local domain with `𝔪 ≠ 0`, with fraction field `K`, and let `L/K` be a finitely
generated field extension. Then there is a discrete valuation ring `R ⊆ L`, not
a field, with fraction field `L`, which dominates the image of `A` in `L`: the
image of `A` lies in `R` and the induced map `A → R` is local.

The domain hypothesis is the source's; it also follows from `IsFractionRing A K`,
so the proof does not use it separately. -/
theorem exists_dominating_dvr_of_fg (A K : Type*) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsLocalRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    (hm : maximalIdeal A ≠ ⊥) (hfg : (⊤ : IntermediateField K L).FG) :
    ∃ R : Subring L, IsDiscreteValuationRing R ∧ IsFractionRing R L ∧ ¬ IsField R ∧
      ∃ h : ∀ a, algebraMap A L a ∈ R, IsLocalHom ((algebraMap A L).codRestrict R h) := by
  classical
  let f := algebraMap A L
  have hinj : Function.Injective f := by
    rw [show f = (algebraMap K L).comp (algebraMap A K) from IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  let A₀ := LocalSubring.range f
  have hmem : ∀ a, f a ∈ A₀.toSubring := fun a => by
    rw [LocalSubring.range_toSubring]
    exact ⟨a, rfl⟩
  let g : A →+* A₀.toSubring := f.codRestrict _ hmem
  have hgsurj : Function.Surjective g := by
    rintro ⟨y, hy⟩
    rw [LocalSubring.range_toSubring] at hy
    obtain ⟨a, rfl⟩ := hy
    exact ⟨a, rfl⟩
  have hginj : Function.Injective g := fun a b hab => hinj (congrArg Subtype.val hab)
  let e : A ≃+* A₀.toSubring := RingEquiv.ofBijective g ⟨hginj, hgsurj⟩
  have : IsNoetherianRing A₀.toSubring := isNoetherianRing_of_ringEquiv A e
  have : IsLocalHom g := IsLocalHom.of_surjective g hgsurj
  have hm₀ : maximalIdeal A₀.toSubring ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
    intro hbot
    have hgx : g x ∈ maximalIdeal A₀.toSubring := by
      rw [mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact (mem_maximalIdeal _).mp hx (isUnit_of_map_unit g x hu)
    rw [hbot, Ideal.mem_bot] at hgx
    exact hx0 (hginj (hgx.trans (map_zero g).symm))
  obtain ⟨S, hS⟩ := hfg
  have hclosure : Subfield.closure ((A₀.toSubring : Set L) ∪ S) = ⊤ := by
    let F : IntermediateField K L :=
      (Subfield.closure ((A₀.toSubring : Set L) ∪ S)).toIntermediateField fun k => by
        obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective A k
        rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
        exact div_mem (Subfield.subset_closure (Or.inl (hmem a)))
          (Subfield.subset_closure (Or.inl (hmem b)))
    have hle : IntermediateField.adjoin K (S : Set L) ≤ F :=
      IntermediateField.adjoin_le_iff.mpr fun y hy => Subfield.subset_closure (Or.inr hy)
    rw [eq_top_iff]
    intro y _
    have hy : y ∈ IntermediateField.adjoin K (S : Set L) := by
      rw [hS]
      exact IntermediateField.mem_top
    exact hle hy
  obtain ⟨R, hR, hRf, hle, hloc⟩ :=
    hasDominatingDVR_of_closure_eq_top S.card A₀.toSubring hm₀ S rfl hclosure
  refine ⟨R, hR, hRf, IsDiscreteValuationRing.not_isField R, fun a => hle (hmem a), ?_⟩
  have : f.codRestrict R (fun a => hle (hmem a)) = (Subring.inclusion hle).comp g := by
    ext
    rfl
  rw [this]
  infer_instance


/-- **Hartshorne II, Exercise 4.11(a)** (repaired, general form). Let `(A, 𝔪)` be a
Noetherian local domain with fraction field `K`, and let `L/K` be a finitely generated field
extension, and suppose that `𝔪 ≠ 0` or `L` is not algebraic over `K`. Then there is a discrete
valuation ring `R ⊆ L`, not a field, with fraction field `L`, which dominates the image of `A`
in `L`: the image of `A` lies in `R` and the induced map `A → R` is local.

Without the added hypothesis the literal statement fails exactly when `A` is a field and
`L/K` is algebraic, for instance when `L = K`. The case `𝔪 ≠ 0` is
`exists_dominating_dvr_of_fg`; when `𝔪 = 0`, the localization of `K[t]` at `(t)`, for `t`
transcendental over `K`, takes the place of `A`. The domain hypothesis is the source's; it
also follows from `IsFractionRing A K`. -/
theorem exists_dominating_dvr_of_fg_of_ne_bot_or_transcendental (A K : Type*) [CommRing A]
    [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] [Field K] [Algebra A K]
    [IsFractionRing A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    (h : maximalIdeal A ≠ ⊥ ∨ ¬ Algebra.IsAlgebraic K L)
    (hfg : (⊤ : IntermediateField K L).FG) :
    ∃ R : Subring L, IsDiscreteValuationRing R ∧ IsFractionRing R L ∧ ¬ IsField R ∧
      ∃ h : ∀ a, algebraMap A L a ∈ R, IsLocalHom ((algebraMap A L).codRestrict R h) := by
  classical
  by_cases hm : maximalIdeal A ≠ ⊥
  · exact exists_dominating_dvr_of_fg A K hm hfg
  have halg : ¬ Algebra.IsAlgebraic K L := h.resolve_left hm
  rw [not_not] at hm
  obtain ⟨t, ht⟩ : ∃ t : L, Transcendental K t := by
    by_contra hcon
    exact halg ⟨fun x => by
      by_contra hx
      exact hcon ⟨x, hx⟩⟩
  obtain ⟨A', hnoeth, hm', hK⟩ := exists_localSubring_of_transcendental K t ht
  have := hnoeth
  obtain ⟨S, hS⟩ := hfg
  have hclosure : Subfield.closure ((A'.toSubring : Set L) ∪ S) = ⊤ := by
    let F : IntermediateField K L :=
      (Subfield.closure ((A'.toSubring : Set L) ∪ S)).toIntermediateField fun k =>
        Subfield.subset_closure (Or.inl (hK k))
    have hle : IntermediateField.adjoin K (S : Set L) ≤ F :=
      IntermediateField.adjoin_le_iff.mpr fun y hy => Subfield.subset_closure (Or.inr hy)
    rw [eq_top_iff]
    intro y _
    have hy : y ∈ IntermediateField.adjoin K (S : Set L) := by
      rw [hS]
      exact IntermediateField.mem_top
    exact hle hy
  obtain ⟨R, hR, hRf, hle, -⟩ :=
    hasDominatingDVR_of_closure_eq_top S.card A'.toSubring hm' S rfl hclosure
  have hmem : ∀ a, algebraMap A L a ∈ R := fun a => by
    rw [IsScalarTower.algebraMap_apply A K L]
    exact hle (hK _)
  refine ⟨R, hR, hRf, IsDiscreteValuationRing.not_isField R, hmem, ⟨fun a ha => ?_⟩⟩
  by_contra hau
  have ha0 : a = 0 := by
    have hma : a ∈ maximalIdeal A := by
      rw [mem_maximalIdeal, mem_nonunits_iff]
      exact hau
    rwa [hm, Ideal.mem_bot] at hma
  subst ha0
  rw [map_zero] at ha
  exact not_isUnit_zero ha

end

end Hartshorne

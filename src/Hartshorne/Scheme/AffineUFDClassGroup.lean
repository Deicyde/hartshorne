/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.HeightOneLocalizationIntersection
import Hartshorne.Scheme.Normal
import Hartshorne.Scheme.WeilClassGroup
import Mathlib.RingTheory.Ideal.UFD
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed

/-!
# The affine UFD class-group criterion

Hartshorne, *Algebraic Geometry*, II.6, Proposition 6.2 (pp. 131--132).

A Noetherian domain `A` is a unique factorization domain if and only if
`Spec A` is normal and its Weil divisor class group is trivial.

The Weil divisor class group is only defined for schemes satisfying
Hartshorne's condition `(*)`. A normal Noetherian integral separated scheme
satisfies `(*)`, so the right-hand side of the criterion records that
`Spec A` satisfies `(*)` together with the triviality of the class group.

The proof compares the order of vanishing at a codimension-one point
`p ∈ Spec A` with the discrete valuation of the local ring `A_p`: an element
of `A` has order zero exactly when it lies outside `p`, an element of the
function field with nonnegative order lies in `A_p`, and a generator of a
principal height-one prime has order one. In the reverse direction the
height-one intersection theorem turns the rational function whose divisor is
a given prime divisor into an element of `A` generating the prime ideal.
-/

noncomputable section

open AlgebraicGeometry IsLocalRing Order

namespace Hartshorne

universe u

section DVRLocalization

variable {A R K : Type*} [CommRing A] [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R] [Field K] [Algebra A R] [Algebra A K] [Algebra R K]
  [IsScalarTower A R K] [IsFractionRing R K]
  (p : Ideal A) [p.IsPrime] [IsLocalization.AtPrime R p]

include p in
/-- If a discrete valuation ring `R` is the localization of `A` at `p`, then an
element of `A` has trivial order in `R` exactly when it lies outside `p`. -/
theorem ordFrac_algebraMap_eq_one_iff_notMem_of_isLocalizationAtPrime (a : A) :
    Ring.ordFrac R (algebraMap A K a) = 1 ↔ a ∉ p := by
  rw [IsScalarTower.algebraMap_apply A R K,
    ← Ring.isUnit_iff_ordFrac_one_of_isDiscreteValuationRing,
    IsLocalization.AtPrime.isUnit_to_map_iff R p a]
  rfl

include p in
/-- If a discrete valuation ring `R` is the localization of `A` at `p`, then
every nonzero element of `A` has nonnegative order in `R`. -/
theorem one_le_ordFrac_algebraMap_of_isLocalizationAtPrime [IsDomain A] {a : A} (ha : a ≠ 0) :
    1 ≤ Ring.ordFrac R (algebraMap A K a) := by
  rw [IsScalarTower.algebraMap_apply A R K]
  apply Ring.ordFrac_ge_one_of_ne_zero
  intro h
  apply ha
  apply IsLocalization.injective R p.primeCompl_le_nonZeroDivisors
  rw [h, map_zero]

include p in
/-- If a discrete valuation ring `R` is the localization of `A` at `p` and
`p = (π)`, then `π` has order one in `R`. -/
theorem ordFrac_algebraMap_eq_exp_one_of_span_eq {π : A}
    (hπ : Ideal.span {π} = p) :
    Ring.ordFrac R (algebraMap A K π) = WithZero.exp 1 := by
  rw [IsScalarTower.algebraMap_apply A R K]
  apply Ring.ordFrac_irreducible
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer,
    ← IsLocalization.AtPrime.map_eq_maximalIdeal p R, ← hπ, Ideal.map_span,
    Set.image_singleton]

include p in
/-- If a discrete valuation ring `R` is the localization of `A` at `p`, then an
element of the fraction field with nonnegative order lies in the localization
`A_p`, viewed inside the fraction field. -/
theorem mem_ofField_of_one_le_ordFrac [IsDomain A] [IsFractionRing A K] {f : K} (hf : f ≠ 0)
    (h : 1 ≤ Ring.ordFrac R f) :
    f ∈ Localization.subalgebra.ofField K p.primeCompl p.primeCompl_le_nonZeroDivisors := by
  rw [Ring.ordFrac_eq_valuation_inv] at h
  have hv : (IsDiscreteValuationRing.maximalIdeal R).valuation K f ≠ 0 := by simpa using hf
  have hle : (IsDiscreteValuationRing.maximalIdeal R).valuation K f ≤ 1 :=
    (one_le_inv₀ (zero_lt_iff.mpr hv)).mp h
  obtain ⟨r, rfl⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hle
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl r
  have hs : algebraMap A K s ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (p.primeCompl_le_nonZeroDivisors s.2)
  have hspec := congrArg (algebraMap R K) (IsLocalization.mk'_spec R a s)
  rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at hspec
  refine ⟨a, s, s.2, ?_⟩
  rw [← hspec, mul_inv_cancel_right₀ hs]

end DVRLocalization

/-- The structure map from a ring to a stalk of its spectrum, as an algebra. -/
abbrev specStalkAlgebra (R : CommRingCat.{u}) (x : Spec R) :
    Algebra R ((Spec R).presheaf.stalk x) :=
  StructureSheaf.stalkAlgebra R x

attribute [local instance] specStalkAlgebra

/-- The prime ideal of a point of `Spec R` is prime. -/
theorem specPoint_asIdeal_isPrime (R : CommRingCat.{u}) (x : Spec R) : x.asIdeal.IsPrime :=
  PrimeSpectrum.isPrime (R := R) x

attribute [local instance] specPoint_asIdeal_isPrime

/-- The stalk of `Spec R` at a point is the localization of `R` at the
corresponding prime ideal. -/
theorem specStalk_isLocalizationAtPrime (R : CommRingCat.{u}) (x : Spec R) :
    IsLocalization.AtPrime ((Spec R).presheaf.stalk x) x.asIdeal :=
  StructureSheaf.IsLocalization.to_stalk R x

attribute [local instance] specStalk_isLocalizationAtPrime

/-- For a domain `R`, the maps `R → 𝒪_{Spec R, x} → K(Spec R)` compose to the
canonical map from `R` to the function field. -/
theorem specStalk_functionField_isScalarTower (R : CommRingCat.{u}) [IsDomain R]
    (x : Spec R) :
    IsScalarTower R ((Spec R).presheaf.stalk x) (Spec R).functionField := by
  apply IsScalarTower.of_algebraMap_eq'
  simp_rw [RingHom.algebraMap_toAlgebra]
  exact congrArg CommRingCat.Hom.hom (StructureSheaf.toStalk_stalkSpecializes _).symm

attribute [local instance] specStalk_functionField_isScalarTower

section SpecOrder

variable {R : CommRingCat.{u}} [IsDomain R]

/-- On `Spec R` for a domain `R` satisfying condition `(*)`, a nonzero element
of `R` has order zero at a codimension-one point exactly when it lies outside
the corresponding prime ideal. -/
theorem spec_ord_algebraMap_eq_zero_iff (hX : (Spec R).SatisfiesConditionStar)
    {x : Spec R} (hx : coheight x = 1) {a : R} (ha : a ≠ 0) :
    let _ : IsNoetherian (Spec R) := hX.isNoetherian
    (Spec R).ord (algebraMap R (Spec R).functionField a) x = 0 ↔ a ∉ x.asIdeal := by
  dsimp only
  let _ : IsNoetherian (Spec R) := hX.isNoetherian
  let _ : IsDiscreteValuationRing ((Spec R).presheaf.stalk x) :=
    (Spec R).codimensionOneStalk_isDiscreteValuationRing hX hx
  have ha' : algebraMap R (Spec R).functionField a ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero ha)
  rw [Scheme.ord_eq_iff hx ha', ofAdd_zero, WithZero.coe_one,
    ← ordFrac_algebraMap_eq_one_iff_notMem_of_isLocalizationAtPrime
      (R := (Spec R).presheaf.stalk x) (K := (Spec R).functionField) x.asIdeal a]
  rfl

/-- On `Spec R` for a Noetherian domain `R`, a nonzero element of `R` has
nonnegative order at every point. -/
theorem spec_ord_algebraMap_nonneg (hX : (Spec R).SatisfiesConditionStar)
    (x : Spec R) {a : R} (ha : a ≠ 0) :
    let _ : IsNoetherian (Spec R) := hX.isNoetherian
    0 ≤ (Spec R).ord (algebraMap R (Spec R).functionField a) x := by
  dsimp only
  let _ : IsNoetherian (Spec R) := hX.isNoetherian
  by_cases hx : coheight x = 1
  · let _ : IsDiscreteValuationRing ((Spec R).presheaf.stalk x) :=
      (Spec R).codimensionOneStalk_isDiscreteValuationRing hX hx
    have ha' : algebraMap R (Spec R).functionField a ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero ha)
    rw [Scheme.le_ord_iff hx ha']
    exact one_le_ordFrac_algebraMap_of_isLocalizationAtPrime
      (R := (Spec R).presheaf.stalk x) (K := (Spec R).functionField) x.asIdeal ha
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one hx]

/-- On `Spec R` for a domain `R` satisfying condition `(*)`, a nonzero element
of `R` lying in the prime ideal of a codimension-one point has positive order
there. -/
theorem spec_one_le_ord_algebraMap_of_mem (hX : (Spec R).SatisfiesConditionStar)
    {x : Spec R} (hx : coheight x = 1) {a : R} (ha : a ≠ 0) (hax : a ∈ x.asIdeal) :
    let _ : IsNoetherian (Spec R) := hX.isNoetherian
    1 ≤ (Spec R).ord (algebraMap R (Spec R).functionField a) x := by
  dsimp only
  let _ : IsNoetherian (Spec R) := hX.isNoetherian
  have h0 := spec_ord_algebraMap_nonneg hX x ha
  have h1 := (spec_ord_algebraMap_eq_zero_iff hX hx ha).not.mpr (not_not.mpr hax)
  dsimp only at h0 h1
  omega

/-- On `Spec R` for a domain `R` satisfying condition `(*)`, a generator of a
principal codimension-one prime has order one at that point. -/
theorem spec_ord_algebraMap_eq_one_of_span_eq (hX : (Spec R).SatisfiesConditionStar)
    {x : Spec R} (hx : coheight x = 1) {π : R} (hπ : Ideal.span {π} = x.asIdeal) :
    let _ : IsNoetherian (Spec R) := hX.isNoetherian
    (Spec R).ord (algebraMap R (Spec R).functionField π) x = 1 := by
  dsimp only
  let _ : IsNoetherian (Spec R) := hX.isNoetherian
  let _ : IsDiscreteValuationRing ((Spec R).presheaf.stalk x) :=
    (Spec R).codimensionOneStalk_isDiscreteValuationRing hX hx
  have hπ0 : π ≠ 0 := by
    rintro rfl
    have hbot : x.asIdeal = ⊥ := by rw [← hπ, Ideal.span_singleton_eq_bot]
    have hheight := idealHeight_eq_coheight R x
    rw [hx, hbot, Ideal.height_bot] at hheight
    exact zero_ne_one hheight
  have hπ' : algebraMap R (Spec R).functionField π ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hπ0)
  rw [Scheme.ord_eq_iff hx hπ']
  exact ordFrac_algebraMap_eq_exp_one_of_span_eq (R := (Spec R).presheaf.stalk x) (K := (Spec R).functionField) x.asIdeal hπ

/-- On `Spec R` for a domain `R` satisfying condition `(*)`, a nonzero rational
function with nonnegative order at a codimension-one point lies in the
localization of `R` at the corresponding prime. -/
theorem spec_mem_ofField_of_ord_nonneg (hX : (Spec R).SatisfiesConditionStar)
    {x : Spec R} (hx : coheight x = 1) {f : (Spec R).functionField} (hf : f ≠ 0)
    (h : let _ : IsNoetherian (Spec R) := hX.isNoetherian
      0 ≤ (Spec R).ord f x) :
    f ∈ Localization.subalgebra.ofField (Spec R).functionField x.asIdeal.primeCompl
      x.asIdeal.primeCompl_le_nonZeroDivisors := by
  let _ : IsNoetherian (Spec R) := hX.isNoetherian
  let _ : IsDiscreteValuationRing ((Spec R).presheaf.stalk x) :=
    (Spec R).codimensionOneStalk_isDiscreteValuationRing hX hx
  rw [Scheme.le_ord_iff hx hf] at h
  exact mem_ofField_of_one_le_ordFrac (R := (Spec R).presheaf.stalk x) (K := (Spec R).functionField) x.asIdeal hf h

end SpecOrder

section Normality

/-- A Noetherian integral separated normal scheme satisfies Hartshorne's
condition `(*)`: its codimension-one local rings are one-dimensional
integrally closed Noetherian local domains, hence regular. -/
theorem satisfiesConditionStar_of_isNormal {X : Scheme.{u}} [IsNoetherian X] [IsIntegral X]
    [X.IsSeparated] [IsNormal X] : X.SatisfiesConditionStar := by
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  intro x hx
  have hdim : ringKrullDim (X.presheaf.stalk x) = 1 := by
    rw [ringKrullDim_stalk_eq_coheight]
    exact WithBot.coe_eq_coe.mpr hx
  exact ((dvr_characterizations (X.presheaf.stalk x) hdim).out 1 2).mp
    (show IsIntegrallyClosed (X.presheaf.stalk x) from inferInstance)

/-- The spectrum of an integrally closed domain is a normal scheme. -/
theorem isNormal_spec_of_isIntegrallyClosed (R : CommRingCat.{u}) [IsDomain R]
    [IsIntegrallyClosed R] : IsNormal (Spec R) where
  isDomain_stalk _ := inferInstance
  isIntegrallyClosed_stalk x :=
    isIntegrallyClosed_of_isLocalization (R := R) _ x.asIdeal.primeCompl
      x.asIdeal.primeCompl_le_nonZeroDivisors

/-- A domain whose spectrum is a normal scheme is integrally closed. -/
theorem isIntegrallyClosed_of_isNormal_spec (R : CommRingCat.{u}) [IsDomain R]
    [IsNormal (Spec R)] : IsIntegrallyClosed R := by
  apply IsIntegrallyClosed.of_localization_maximal
  intro p _ _
  let x : Spec R := ⟨p, inferInstance⟩
  have : IsLocalization.AtPrime ((Spec R).presheaf.stalk x) p :=
    specStalk_isLocalizationAtPrime R x
  let e : Localization.AtPrime p ≃ₐ[R] (Spec R).presheaf.stalk x :=
    IsLocalization.algEquiv p.primeCompl _ _
  exact IsIntegrallyClosed.of_equiv e.symm.toRingEquiv

end Normality

section ClassGroup

private theorem weilDivisorAddEquivFinsupp_apply_eq_coeff {X : Scheme.{u}} [IsNoetherian X]
    (D : X.WeilDivisor) (P : X.PrimeDivisor) :
    X.weilDivisorAddEquivFinsupp D P = D.1 P.1 :=
  rfl

private theorem scheme_ord_inv {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {g : X.functionField} (hg : g ≠ 0) (x : X) : X.ord g⁻¹ x = -X.ord g x := by
  have h1 : X.ord (1 : X.functionField) x = 0 := by
    have h := X.ord_mul (x := x) (one_ne_zero (α := X.functionField)) one_ne_zero
    rw [mul_one] at h
    omega
  have h := X.ord_mul (x := x) hg (inv_ne_zero hg)
  rw [mul_inv_cancel₀ hg, h1] at h
  omega

/-- If `R` is a UFD whose spectrum satisfies condition `(*)`, then the Weil
divisor class group of `Spec R` is trivial: every prime divisor is the
divisor of a generator of the corresponding principal height-one prime. -/
theorem spec_weilClassGroup_subsingleton_of_uniqueFactorizationMonoid
    {R : CommRingCat.{u}} [IsDomain R] [UniqueFactorizationMonoid R]
    (hX : (Spec R).SatisfiesConditionStar) :
    Subsingleton ((Spec R).WeilClassGroup hX) := by
  classical
  let _ : IsNoetherian (Spec R) := hX.isNoetherian
  let e := (Spec R).weilDivisorAddEquivFinsupp
  have hprime : ∀ P : (Spec R).PrimeDivisor,
      e.symm (Finsupp.single P 1) ∈ (Spec R).principalDivisorSubgroup hX := by
    rintro ⟨x, hx⟩
    have hheight : x.asIdeal.height = 1 := by
      rw [idealHeight_eq_coheight]
      exact hx
    have : x.asIdeal.IsPrincipal :=
      UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hheight
    have hspan : Ideal.span {Submodule.IsPrincipal.generator x.asIdeal} = x.asIdeal :=
      Ideal.span_singleton_generator x.asIdeal
    have hπprime : Prime (Submodule.IsPrincipal.generator x.asIdeal) :=
      Submodule.IsPrincipal.prime_generator_of_isPrime x.asIdeal
        (Ideal.ne_bot_of_height_eq_one hheight)
    have hπ0 : algebraMap R (Spec R).functionField
        (Submodule.IsPrincipal.generator x.asIdeal) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_of_ne_zero hπprime.ne_zero)
    let f : (Spec R).functionFieldˣ := Units.mk0 _ hπ0
    have hD : e.symm (Finsupp.single ⟨x, hx⟩ 1) = (Spec R).principalDivisor hX f := by
      apply e.injective
      rw [AddEquiv.apply_symm_apply]
      ext Q
      rw [weilDivisorAddEquivFinsupp_apply_eq_coeff, Scheme.principalDivisor_apply]
      change _ = (Spec R).ord (algebraMap R (Spec R).functionField
        (Submodule.IsPrincipal.generator x.asIdeal)) Q.1
      by_cases hQ : (⟨x, hx⟩ : (Spec R).PrimeDivisor) = Q
      · subst hQ
        rw [Finsupp.single_eq_same]
        exact (spec_ord_algebraMap_eq_one_of_span_eq hX hx hspan).symm
      · rw [Finsupp.single_apply, if_neg hQ]
        have hnot : Submodule.IsPrincipal.generator x.asIdeal ∉ Q.1.asIdeal := by
          intro hmem
          apply hQ
          have hQh : Q.1.asIdeal.height = 1 := by
            rw [idealHeight_eq_coheight]
            exact Q.2
          have hQeq := Ideal.eq_span_singleton_of_height_eq_one hQh hmem hπprime
          apply Subtype.ext
          apply PrimeSpectrum.ext
          change x.asIdeal = Q.1.asIdeal
          rw [hQeq, hspan]
        exact ((spec_ord_algebraMap_eq_zero_iff hX Q.2 hπprime.ne_zero).mpr hnot).symm
    rw [hD]
    change _ ∈ ((Spec R).principalDivisorHom hX).range
    exact ⟨Additive.ofMul f, rfl⟩
  have hall : ∀ D : (Spec R).WeilDivisor, D ∈ (Spec R).principalDivisorSubgroup hX := by
    intro D
    rw [← e.symm_apply_apply D]
    induction e D using Finsupp.induction_linear with
    | zero => rw [map_zero]; exact zero_mem _
    | add F G hF hG => rw [map_add]; exact add_mem hF hG
    | single P n =>
      have hn : e.symm (Finsupp.single P n) = n • e.symm (Finsupp.single P 1) := by
        rw [← map_zsmul, Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [hn]
      exact zsmul_mem (hprime P) n
  constructor
  intro a b
  induction a using QuotientAddGroup.induction_on
  induction b using QuotientAddGroup.induction_on
  exact QuotientAddGroup.eq.mpr (hall _)

/-- If `R` is a Noetherian domain whose spectrum is normal and has trivial Weil
divisor class group, then `R` is a UFD: the divisor of a height-one prime is
principal, and its rational generator is an element of `R` generating the
prime ideal. -/
theorem uniqueFactorizationMonoid_of_spec_weilClassGroup_subsingleton
    {R : CommRingCat.{u}} [IsDomain R] [IsNoetherianRing R] [IsNormal (Spec R)]
    (hX : (Spec R).SatisfiesConditionStar) [Subsingleton ((Spec R).WeilClassGroup hX)] :
    UniqueFactorizationMonoid R := by
  classical
  have : IsIntegrallyClosed R := isIntegrallyClosed_of_isNormal_spec R
  let _ : IsNoetherian (Spec R) := hX.isNoetherian
  apply UniqueFactorizationMonoid.of_forall_isPrincipal_of_height_eq_one
  intro p hp hheight
  let x : Spec R := ⟨p, hp⟩
  have hx : coheight x = 1 := by
    rw [← idealHeight_eq_coheight]
    exact hheight
  let P : (Spec R).PrimeDivisor := ⟨x, hx⟩
  let e := (Spec R).weilDivisorAddEquivFinsupp
  obtain ⟨f, hf⟩ := ((Spec R).weilDivisorClass_eq_iff hX (e.symm (Finsupp.single P 1)) 0).mp
    (Subsingleton.elim _ _)
  rw [sub_zero] at hf
  have hcoeff : ∀ Q : (Spec R).PrimeDivisor,
      (Spec R).ord (f : (Spec R).functionField) Q.1 = if P = Q then 1 else 0 := by
    intro Q
    have hQ := congrArg (fun D ↦ e D Q) hf
    simp only [AddEquiv.apply_symm_apply] at hQ
    rw [weilDivisorAddEquivFinsupp_apply_eq_coeff, Scheme.principalDivisor_apply,
      Finsupp.single_apply] at hQ
    exact hQ.symm
  have hint : ∀ g : (Spec R).functionField, g ≠ 0 →
      (∀ Q : (Spec R).PrimeDivisor, 0 ≤ (Spec R).ord g Q.1) →
        ∃ c : R, algebraMap R (Spec R).functionField c = g := by
    intro g hg hQ
    apply exists_algebraMap_eq_of_forall_height_one (Spec R).functionField g
    intro q hq hqh
    let y : Spec R := ⟨q, hq⟩
    have hy : coheight y = 1 := by
      rw [← idealHeight_eq_coheight]
      exact hqh
    exact spec_mem_ofField_of_ord_nonneg hX hy hg (hQ ⟨y, hy⟩)
  obtain ⟨a, ha⟩ := hint f f.ne_zero fun Q ↦ by
    rw [hcoeff Q]
    split_ifs <;> norm_num
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact f.ne_zero ha.symm
  have haK : algebraMap R (Spec R).functionField a ≠ 0 := by
    rw [ha]
    exact f.ne_zero
  have hordx : (Spec R).ord (algebraMap R (Spec R).functionField a) x = 1 := by
    rw [ha]
    simpa using hcoeff P
  have hordQ : ∀ Q : (Spec R).PrimeDivisor, Q ≠ P →
      (Spec R).ord (algebraMap R (Spec R).functionField a) Q.1 = 0 := by
    intro Q hQ
    rw [ha, hcoeff Q, if_neg (Ne.symm hQ)]
  have hap : a ∈ p := by
    by_contra h
    have h0 := (spec_ord_algebraMap_eq_zero_iff hX hx ha0).mpr h
    rw [hordx] at h0
    exact one_ne_zero h0
  refine ⟨⟨a, le_antisymm ?_ ?_⟩⟩
  · intro b hb
    by_cases hb0 : b = 0
    · rw [hb0]
      exact zero_mem _
    have hbK : algebraMap R (Spec R).functionField b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hb0)
    have hgint : ∀ Q : (Spec R).PrimeDivisor, 0 ≤ (Spec R).ord
        (algebraMap R (Spec R).functionField b * (algebraMap R (Spec R).functionField a)⁻¹)
        Q.1 := by
      intro Q
      rw [Scheme.ord_mul hbK (inv_ne_zero haK), scheme_ord_inv haK]
      have hb_nonneg := spec_ord_algebraMap_nonneg hX Q.1 hb0
      dsimp only at hb_nonneg
      by_cases hQ : Q = P
      · subst hQ
        have hb_pos := spec_one_le_ord_algebraMap_of_mem hX hx hb0 hb
        dsimp only at hb_pos
        change 0 ≤ (Spec R).ord _ x + -(Spec R).ord _ x
        rw [hordx]
        omega
      · rw [hordQ Q hQ]
        omega
    obtain ⟨c, hc⟩ := hint (algebraMap R (Spec R).functionField b *
      (algebraMap R (Spec R).functionField a)⁻¹) (mul_ne_zero hbK (inv_ne_zero haK)) hgint
    rw [Submodule.mem_span_singleton]
    refine ⟨c, ?_⟩
    apply IsFractionRing.injective R (Spec R).functionField
    rw [smul_eq_mul, map_mul, hc, inv_mul_cancel_right₀ haK]
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hap

end ClassGroup

/-- **Hartshorne II.6, Proposition 6.2.** A Noetherian domain `A` is a unique
factorization domain if and only if `Spec A` is normal and its Weil divisor
class group is trivial.

The class group is defined only under Hartshorne's condition `(*)`, so the
right-hand side records that `Spec A` satisfies `(*)` (which follows from
normality) and that the class group is trivial. -/
theorem uniqueFactorizationMonoid_iff_isNormal_spec_and_weilClassGroup_subsingleton
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] :
    UniqueFactorizationMonoid A ↔
      IsNormal (Spec (CommRingCat.of A)) ∧
        ∃ hX : (Spec (CommRingCat.of A)).SatisfiesConditionStar,
          Subsingleton ((Spec (CommRingCat.of A)).WeilClassGroup hX) := by
  constructor
  · intro hA
    have hN : IsNormal (Spec (CommRingCat.of A)) :=
      isNormal_spec_of_isIntegrallyClosed (CommRingCat.of A)
    have hX : (Spec (CommRingCat.of A)).SatisfiesConditionStar :=
      satisfiesConditionStar_of_isNormal
    exact ⟨hN, hX, spec_weilClassGroup_subsingleton_of_uniqueFactorizationMonoid hX⟩
  · rintro ⟨hN, hX, hsub⟩
    exact uniqueFactorizationMonoid_of_spec_weilClassGroup_subsingleton
      (R := CommRingCat.of A) hX

end Hartshorne

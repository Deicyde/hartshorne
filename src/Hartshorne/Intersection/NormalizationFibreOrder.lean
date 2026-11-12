/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.NormalizationPushforwardOrder
import Mathlib.Data.ENat.BigOperators

/-!
# The fibre order formula for the normalization

Let `D` be a Noetherian domain whose integral closure `O` in its fraction field is a finite
`D`-module, and `Q` a prime of `D` of height one. For every nonzero rational function `g` on
`Spec D`, `∑_{𝔔 ∩ D = Q} ord_𝔔(g) [κ(𝔔) : κ(Q)] = ord_Q(g)`
(`fibreOrdFormula_specMap_integralClosure`): the fibre order formula holds for
`Spec O ⟶ Spec D` at `Q`.
-/

universe u

open AlgebraicGeometry CategoryTheory IsLocalRing Order Hartshorne.NormalizationLocalOrder

namespace Hartshorne

section SpecFibre

variable (D : CommRingCat.{u}) [IsDomain D] [IsNoetherianRing D]
  [Module.Finite D (integralClosure D (FractionRing D))]

/-- The integral closure of `D` in its fraction field, as a commutative ring. -/
private abbrev closureRing : CommRingCat.{u} := CommRingCat.of (integralClosure D (FractionRing D))

private instance isDomain_closureRing : IsDomain (closureRing D) :=
  inferInstanceAs (IsDomain (integralClosure D (FractionRing D)))

private noncomputable instance algebra_closureRing_functionField :
    Algebra (closureRing D) (Spec (closureRing D)).functionField :=
  instAlgebraCarrierFunctionFieldSpec _

private instance isFractionRing_closureRing_functionField :
    IsFractionRing (closureRing D) (Spec (closureRing D)).functionField :=
  functionField_isFractionRing_of_affine _

private instance isNoetherianRing_closureRing : IsNoetherianRing (closureRing D) := by
  have : IsNoetherian D (integralClosure D (FractionRing D)) :=
    isNoetherian_of_isNoetherianRing_of_finite D _
  exact isNoetherian_of_tower D this

/-- The inclusion of `D` into its integral closure. -/
private abbrev closureHom : D ⟶ closureRing D :=
  CommRingCat.ofHom (algebraMap D (integralClosure D (FractionRing D)))

omit [IsDomain D] [IsNoetherianRing D] [Module.Finite D (integralClosure D (FractionRing D))] in
private theorem closureHom_injective : Function.Injective (closureHom D) := by
  intro a b h
  have h' := congrArg (fun x : integralClosure D (FractionRing D) ↦ (x : FractionRing D)) h
  exact IsFractionRing.injective D (FractionRing D) h'

omit [IsNoetherianRing D] [Module.Finite D (integralClosure D (FractionRing D))] in
/-- `Spec O ⟶ Spec D` sends the generic point to the generic point. -/
theorem specMap_integralClosure_genericPoint :
    (Spec.map (closureHom D)) (genericPoint (Spec (closureRing D))) = genericPoint (Spec D) := by
  rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
  exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective _ (closureHom_injective D))

private instance isFinite_closureHom : IsFinite (Spec.map (closureHom D)) :=
  (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

variable {D}

attribute [local instance] FreeLocusAux.freeLocusStalkAlgebra
  FreeLocusAux.freeLocus_asIdeal_isPrime specStalk_functionField_isScalarTower

private theorem coheight_eq_one_iff_ringKrullDim (R : CommRingCat.{u}) (x : Spec R) :
    coheight x = 1 ↔ ringKrullDim (Localization.AtPrime x.asIdeal) = 1 := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height x.asIdeal, idealHeight_eq_coheight]
  norm_cast

private instance isPrime_closureRing_point (x : Spec (closureRing D)) : x.asIdeal.IsPrime :=
  x.isPrime

private noncomputable instance algebra_closureRing_stalk (x : Spec (closureRing D)) :
    Algebra (closureRing D) ((Spec (closureRing D)).presheaf.stalk x) :=
  FreeLocusAux.freeLocusStalkAlgebra x

private instance isScalarTower_closureRing_stalk (x : Spec (closureRing D)) :
    IsScalarTower (closureRing D) ((Spec (closureRing D)).presheaf.stalk x)
      (Spec (closureRing D)).functionField :=
  specStalk_functionField_isScalarTower _ x

omit [IsNoetherianRing D] [Module.Finite D (integralClosure D (FractionRing D))] in
private theorem genericFunctionFieldMap_closureHom (a : D) :
    (Spec.map (closureHom D)).genericFunctionFieldMap (specMap_integralClosure_genericPoint D)
      (algebraMap D (Spec D).functionField a) =
      algebraMap (closureRing D) (Spec (closureRing D)).functionField (closureHom D a) := by
  have e := (Spec.map (closureHom D)).genericFunctionFieldMap_algebraMap
    (specMap_integralClosure_genericPoint D) (genericPoint (Spec (closureRing D)))
    (algebraMap D _ a)
  rw [← IsScalarTower.algebraMap_apply] at e
  rw [e, Spec.stalkMap_algebraMap, ← IsScalarTower.algebraMap_apply]

omit [IsDomain D] [IsNoetherianRing D] [Module.Finite D (integralClosure D (FractionRing D))] in
private theorem algebraMap_closure_ne_zero {a : D} (ha : a ≠ 0) :
    algebraMap D (integralClosure D (FractionRing D)) a ≠ 0 := fun h ↦ ha <|
  IsFractionRing.injective D (FractionRing D)
    ((congrArg (fun x : integralClosure D (FractionRing D) ↦ (x : FractionRing D)) h).trans
      (by simp))

omit [IsDomain D] [IsNoetherianRing D] in
/-- The primes of the integral closure lying over `Q` form a finite set. -/
private theorem finite_primesOver_closure (Q : Spec D) :
    {𝔔 : PrimeSpectrum (integralClosure D (FractionRing D)) |
      𝔔.asIdeal.comap (algebraMap D _) = Q.asIdeal}.Finite := by
  have h := (Spec.map (closureHom D)).finite_preimage_singleton Q
  refine (h.image (fun z : Spec (closureRing D) ↦
    (z : PrimeSpectrum (integralClosure D (FractionRing D))))).subset ?_
  intro 𝔔 h𝔔
  exact ⟨𝔔, PrimeSpectrum.ext h𝔔, rfl⟩

private theorem ord_mul_residueDegree_closure (Q : Spec D) (hQ : coheight Q = 1) {a : D}
    (ha : a ≠ 0) (𝔔 : Spec (closureRing D))
    (h𝔔 : 𝔔.asIdeal.comap (algebraMap D (integralClosure D (FractionRing D))) = Q.asIdeal) :
    (Spec (closureRing D)).ord (algebraMap (closureRing D) _ (closureHom D a)) 𝔔 *
        ((Spec.map (closureHom D)).residueDegree 𝔔 : ℤ) =
      ((Ring.ord (Localization.AtPrime 𝔔.asIdeal)
        (algebraMap D (Localization.AtPrime 𝔔.asIdeal) a)).toNat * 𝔔.asIdeal.inertiaDeg D : ℕ) := by
  have hdim := ringKrullDim_localization_of_comap_eq Q.asIdeal
    ((coheight_eq_one_iff_ringKrullDim D Q).mp hQ) 𝔔 h𝔔
  have h1 : coheight 𝔔 = 1 := (coheight_eq_one_iff_ringKrullDim _ _).mpr hdim
  have hφa : closureHom D a ≠ 0 := fun h ↦
    ha (closureHom_injective D (h.trans (map_zero _).symm))
  rw [Spec.ord_algebraMap (closureRing D) h1 hφa]
  have hrd : (Spec.map (closureHom D)).residueDegree 𝔔 = 𝔔.asIdeal.inertiaDeg D :=
    Spec.residueDegree_map_eq_inertiaDeg (D := D) 𝔔
  rw [hrd, IsScalarTower.algebraMap_apply D (integralClosure D (FractionRing D))
    (Localization.AtPrime 𝔔.asIdeal) a, Nat.cast_mul]
  rfl

private theorem sum_fibre_ord_algebraMap (Q : Spec D) (hQ : coheight Q = 1) {a : D}
    (ha : a ≠ 0) :
    ∑ᶠ z ∈ (Spec.map (closureHom D)) ⁻¹' {Q},
      (Spec (closureRing D)).ord (algebraMap (closureRing D) _ (closureHom D a)) z *
        ((Spec.map (closureHom D)).residueDegree z : ℤ) =
      (Spec D).ord (algebraMap D (Spec D).functionField a) Q := by
  classical
  let O := integralClosure D (FractionRing D)
  have hQ' := (coheight_eq_one_iff_ringKrullDim D Q).mp hQ
  let s : Set (PrimeSpectrum O) := {𝔔 | 𝔔.asIdeal.comap (algebraMap D O) = Q.asIdeal}
  have hs : s.Finite := finite_primesOver_closure Q
  let f : PrimeSpectrum O → ℕ∞ := fun 𝔔 ↦
    Ring.ord (Localization.AtPrime 𝔔.asIdeal) (algebraMap D _ a) * (𝔔.asIdeal.inertiaDeg D : ℕ∞)
  have hne : ∀ 𝔔 ∈ s, f 𝔔 ≠ ⊤ := by
    intro 𝔔 h𝔔
    have hdim := ringKrullDim_localization_of_comap_eq Q.asIdeal hQ' 𝔔 h𝔔
    have : Ring.KrullDimLE 1 (Localization.AtPrime 𝔔.asIdeal) := ⟨hdim.le⟩
    have : IsNoetherianRing O := isNoetherianRing_closureRing D
    have : IsNoetherianRing (Localization.AtPrime 𝔔.asIdeal) :=
      IsLocalization.isNoetherianRing 𝔔.asIdeal.primeCompl _ this
    have : IsDomain (Localization.AtPrime 𝔔.asIdeal) :=
      IsLocalization.isDomain_localization 𝔔.asIdeal.primeCompl_le_nonZeroDivisors
    have hx : algebraMap D (Localization.AtPrime 𝔔.asIdeal) a ∈ nonZeroDivisors _ := by
      rw [IsScalarTower.algebraMap_apply D O (Localization.AtPrime 𝔔.asIdeal)]
      exact map_mem_nonZeroDivisors _ (IsLocalization.injective (Localization.AtPrime 𝔔.asIdeal)
        𝔔.asIdeal.primeCompl_le_nonZeroDivisors)
        (mem_nonZeroDivisors_of_ne_zero (algebraMap_closure_ne_zero ha))
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp
      (@Ring.ord_ne_top (Localization.AtPrime 𝔔.asIdeal) _ _ ‹_› _ hx)
    change Ring.ord _ _ * _ ≠ ⊤
    rw [← hm, ← ENat.natCast_mul]
    exact ENat.natCast_ne_top _
  have hL : ∑ᶠ z ∈ (Spec.map (closureHom D)) ⁻¹' {Q},
      (Spec (closureRing D)).ord (algebraMap (closureRing D) _ (closureHom D a)) z *
        ((Spec.map (closureHom D)).residueDegree z : ℤ) = ∑ᶠ 𝔔 ∈ s, ((f 𝔔).toNat : ℤ) := by
    symm
    refine finsum_mem_eq_of_bijOn (fun 𝔔 : PrimeSpectrum O ↦ (𝔔 : Spec (closureRing D)))
      ⟨fun 𝔔 h𝔔 ↦ PrimeSpectrum.ext h𝔔, fun _ _ _ _ h ↦ h,
        fun z hz ↦ ⟨z, congrArg PrimeSpectrum.asIdeal hz, rfl⟩⟩ ?_
    intro 𝔔 h𝔔
    rw [ord_mul_residueDegree_closure Q hQ ha 𝔔 h𝔔]
    simp only [f, ENat.toNat_mul, ENat.toNat_natCast]
    rfl
  rw [hL, Spec.ord_algebraMap D hQ ha, Ring.ord,
    length_quotient_eq_finsum_primesOver Q.asIdeal hQ' ha]
  change _ = (((∑ᶠ 𝔔 ∈ s, f 𝔔).toNat : ℕ) : ℤ)
  rw [finsum_mem_eq_finite_toFinset_sum _ hs, finsum_mem_eq_finite_toFinset_sum _ hs,
    ENat.toNat_sum (fun 𝔔 h𝔔 ↦ hne 𝔔 (hs.mem_toFinset.mp h𝔔)), Nat.cast_sum]

/-- **The fibre order formula for the normalization of an affine scheme.** Let `D` be a
Noetherian domain whose integral closure `O` in its fraction field is a finite `D`-module, and `Q`
a point of codimension one of `Spec D`. Then for every nonzero rational function `g` on `Spec D`,
`∑_{𝔔 ↦ Q} ord_𝔔(g) [κ(𝔔) : κ(Q)] = ord_Q(g)`, the sum running over the points of `Spec O` over
`Q`. -/
theorem fibreOrdFormula_specMap_integralClosure (Q : Spec D) (hQ : coheight Q = 1) :
    FibreOrdFormula (Spec.map (R := D) (CommRingCat.ofHom
      (algebraMap D (integralClosure D (FractionRing D)))))
      (specMap_integralClosure_genericPoint D) Q := by
  classical
  intro g hg
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective D g
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hg (by rw [map_zero, zero_div])
  have hfa : algebraMap D (Spec D).functionField a ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero ha0)
  have hfb : algebraMap D (Spec D).functionField b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  set ν := Spec.map (closureHom D)
  have hinj := (ν.genericFunctionFieldMap (specMap_integralClosure_genericPoint D)).hom.injective
  have hfin : (ν ⁻¹' {Q}).Finite := ν.finite_preimage_singleton Q
  change ∑ᶠ z ∈ ν ⁻¹' {Q}, _ = _
  rw [map_div₀, Scheme.ord_div hfa hfb, ← sum_fibre_ord_algebraMap Q hQ ha0,
    ← sum_fibre_ord_algebraMap Q hQ hb0, genericFunctionFieldMap_closureHom,
    genericFunctionFieldMap_closureHom, finsum_mem_eq_finite_toFinset_sum _ hfin,
    finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  rw [Scheme.ord_div, sub_mul]
  · exact (map_ne_zero_iff _ (IsFractionRing.injective (closureRing D) _)).mpr
      fun h ↦ ha0 (closureHom_injective D (h.trans (map_zero _).symm))
  · exact (map_ne_zero_iff _ (IsFractionRing.injective (closureRing D) _)).mpr
      fun h ↦ hb0 (closureHom_injective D (h.trans (map_zero _).symm))

end SpecFibre

end Hartshorne

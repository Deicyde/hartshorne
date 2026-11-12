/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.NormalizationPushforwardOrder
import Mathlib.Data.ENat.BigOperators
import Hartshorne.Scheme.AbsoluteNormalizationFinite

/-!
# The fibre order formula for the normalization

Let `D` be a Noetherian domain whose integral closure `O` in its fraction field is a finite
`D`-module, and `Q` a prime of `D` of height one. For every nonzero rational function `g` on
`Spec D`, `∑_{𝔔 ∩ D = Q} ord_𝔔(g) [κ(𝔔) : κ(Q)] = ord_Q(g)`
(`fibreOrdFormula_specMap_integralClosure`): the fibre order formula holds for
`Spec O ⟶ Spec D` at `Q`. The inputs are the length formula for orders through the
normalization and the identification of orders and residue degrees on `Spec`.

For an integral scheme `V` of finite type over a field, the normalization `ν : Ṽ ⟶ V` is covered
by affine charts of this shape. Hence the fibre order formula holds for `ν` at every point of
codimension one (`fibreOrdFormula_absoluteNormalizationMap`), and `ν` induces an isomorphism of
function fields (`genericFunctionFieldMap_absoluteNormalizationMap_bijective`).
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

omit [IsNoetherianRing D] [Module.Finite D (integralClosure D (FractionRing D))] in
private theorem birational_closureHom (a : integralClosure D (FractionRing D)) :
    ∃ d₁ d₂ : D, d₂ ≠ 0 ∧ algebraMap D (integralClosure D (FractionRing D)) d₂ * a =
      algebraMap D (integralClosure D (FractionRing D)) d₁ := by
  obtain ⟨d₁, d₂, hd₂, h⟩ := IsFractionRing.div_surjective D (a : FractionRing D)
  have hd₂' : algebraMap D (FractionRing D) d₂ ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd₂
  refine ⟨d₁, d₂, nonZeroDivisors.ne_zero hd₂, Subtype.ext ?_⟩
  change algebraMap D (FractionRing D) d₂ * (a : FractionRing D) = algebraMap D (FractionRing D) d₁
  rw [← h, mul_div_cancel₀ _ hd₂']

/-- An affine chart of the normalization: around every point of `V` there is an open affine
`Spec R ⟶ V` whose preimage in the normalization is `Spec O`, `O` the integral closure of `R`
(a finite `R`-module). -/
private theorem exists_chart_absoluteNormalization {k : Type u} [Field k] {V : Scheme.{u}}
    [IsIntegral V] [IsLocallyNoetherian V] (s : V ⟶ Spec (.of k)) (hs : FiniteType s) (y : V) :
    ∃ (R : CommRingCat.{u}) (_ : IsDomain R) (_ : IsNoetherianRing R)
      (_ : Module.Finite R (integralClosure R (FractionRing R))) (b : Spec R ⟶ V)
      (_ : IsOpenImmersion b) (a : Spec (closureRing R) ⟶ absoluteNormalization V)
      (_ : IsOpenImmersion a), a ≫ absoluteNormalizationMap V = Spec.map (closureHom R) ≫ b ∧
      y ∈ Set.range b ∧ absoluteNormalizationMap V ⁻¹' Set.range b ⊆ Set.range a := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, -⟩ :=
    V.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  replace hW : IsAffineOpen W := hW
  have : Nonempty W := ⟨⟨y, hyW⟩⟩
  let R : CommRingCat.{u} := Γ(V, W)
  have : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  -- the normalization of `Spec R` is `Spec O`, `O` the integral closure of `R`
  let O := integralClosure R (FractionRing R)
  let j : R →+* O := algebraMap R O
  have hj : Function.Injective j := closureHom_injective R
  have : IsIntegrallyClosed O :=
    integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing R)
  obtain ⟨e, he, heν⟩ := exists_isIso_absoluteNormalization_spec (D := R) (O := O) j hj
    (fun a ↦ integralClosure.isIntegral a) (fun a ↦ birational_closureHom (D := R) a)
  have : IsOpenImmersion hW.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec hW
  have hfinR : IsFinite (absoluteNormalizationMap (Spec R)) := by
    have : QuasiCompact (hW.fromSpec ≫ s) := inferInstance
    have : LocallyOfFiniteType s := hs.1
    have : LocallyOfFiniteType hW.fromSpec := locallyOfFiniteType_of_isOpenImmersion _
    have : LocallyOfFiniteType (hW.fromSpec ≫ s) := inferInstance
    exact isFinite_absoluteNormalizationMap_of_finiteType_field k (Spec R) (hW.fromSpec ≫ s)
      ⟨inferInstance, inferInstance⟩
  have : Module.Finite R O := by
    have h : IsFinite (Spec.map (CommRingCat.ofHom j)) := by
      rw [← heν]
      infer_instance
    exact RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff _).mp h)
  -- the normalization of `W`, and its identification with `Spec O`
  have : IsIntegral (W : Scheme) := isIntegral_of_isOpenImmersion (Scheme.Opens.ι W)
  obtain ⟨h, hh, hhν, hrange⟩ := exists_isOpenImmersion_absoluteNormalization W
  obtain ⟨et, het, hetν⟩ := exists_isIso_absoluteNormalization hW.isoSpec.inv
  refine ⟨R, inferInstance, inferInstance, inferInstance, hW.fromSpec, inferInstance,
    e ≫ et ≫ h, inferInstance, ?_, by rw [hW.range_fromSpec]; exact hyW, ?_⟩
  · have heν' : e ≫ absoluteNormalizationMap (Spec R) =
        Spec.map (R := R) (CommRingCat.ofHom (algebraMap R O)) := heν
    simp only [Category.assoc, hhν]
    rw [reassoc_of% hetν, ← IsAffineOpen.isoSpec_inv_ι, reassoc_of% heν']
  · intro z hz
    have hz' : z ∈ Set.range h := by
      rw [hrange, ← hW.range_fromSpec]
      exact hz
    obtain ⟨w, rfl⟩ := hz'
    obtain ⟨w', rfl⟩ := (ConcreteCategory.bijective_of_isIso (e ≫ et).base).2 w
    exact ⟨w', rfl⟩

/-- **The fibre order formula for the normalization.** Let `V` be an integral scheme of finite
type over a field `k` whose normalization `ν : Ṽ ⟶ V` is locally Noetherian. At every point `y`
of codimension one of `V` and for every nonzero rational function `g` on `V`,
`∑_{ν(z) = y} ord_z(g) [κ(z) : κ(y)] = ord_y(g)`. -/
theorem fibreOrdFormula_absoluteNormalizationMap {k : Type u} [Field k] {V : Scheme.{u}}
    [IsIntegral V] [IsLocallyNoetherian V] [IsLocallyNoetherian (absoluteNormalization V)]
    (s : V ⟶ Spec (.of k)) (hs : FiniteType s)
    (hν : absoluteNormalizationMap V (genericPoint (absoluteNormalization V)) = genericPoint V)
    {y : V} (hy : coheight y = 1) : FibreOrdFormula (absoluteNormalizationMap V) hν y := by
  obtain ⟨R, _, _, _, b, _, a, _, hsq, ⟨Q, hQy⟩, hfib⟩ := exists_chart_absoluteNormalization s hs y
  have hQ : coheight Q = 1 := (coheight_eq_of_isOpenImmersion b).symm.trans (hQy ▸ hy)
  have hfib' : absoluteNormalizationMap V ⁻¹' {b Q} ⊆ Set.range a := fun z hz ↦
    hfib ⟨Q, (show absoluteNormalizationMap V z = b Q from hz).symm⟩
  have key := FibreOrdFormula.of_isOpenImmersion a b hsq hν
    (specMap_integralClosure_genericPoint R) hfib'
    (fibreOrdFormula_specMap_integralClosure (D := R) Q hQ)
  rwa [hQy] at key

/-- The normalization of an integral scheme of finite type over a field induces an isomorphism
of function fields: the pullback `K(V) → K(Ṽ)` is bijective. -/
theorem genericFunctionFieldMap_absoluteNormalizationMap_bijective {k : Type u} [Field k]
    {V : Scheme.{u}} [IsIntegral V] [IsLocallyNoetherian V] (s : V ⟶ Spec (.of k))
    (hs : FiniteType s)
    (hν : absoluteNormalizationMap V (genericPoint (absoluteNormalization V)) = genericPoint V) :
    Function.Bijective ((absoluteNormalizationMap V).genericFunctionFieldMap hν) := by
  refine ⟨((absoluteNormalizationMap V).genericFunctionFieldMap hν).hom.injective, ?_⟩
  obtain ⟨R, _, _, _, b, _, a, _, hsq, -, -⟩ := exists_chart_absoluteNormalization s hs
    (genericPoint V)
  let ν := absoluteNormalizationMap V
  let ν' := Spec.map (closureHom R)
  have ha := genericPoint_eq_of_isOpenImmersion a
  have hb := genericPoint_eq_of_isOpenImmersion b
  have hν' := specMap_integralClosure_genericPoint R
  have hab : (a ≫ ν).base (genericPoint (Spec (closureRing R))) = genericPoint V := by
    rw [Scheme.Hom.comp_base, TopCat.comp_app, ha, hν]
  have hcomp : ∀ g, ν'.genericFunctionFieldMap hν' (b.genericFunctionFieldMap hb g) =
      a.genericFunctionFieldMap ha (ν.genericFunctionFieldMap hν g) := by
    intro g
    have h1 := Scheme.Hom.genericFunctionFieldMap_comp a ν ha hν hab
    have h2 := Scheme.Hom.genericFunctionFieldMap_comp ν' b hν' hb (by rw [← hsq]; exact hab)
    rw [Scheme.Hom.genericFunctionFieldMap_congr hsq hab (by rw [← hsq]; exact hab), h2] at h1
    exact (ConcreteCategory.congr_hom h1 g).trans rfl
  -- `K(Spec R) → K(Spec O)` is surjective
  have hsurj : Function.Surjective (ν'.genericFunctionFieldMap hν') := by
    intro G
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (closureRing R) G
    obtain ⟨d₁, d₂, hd₂, h₁⟩ := birational_closureHom (D := R) x
    obtain ⟨e₁, e₂, he₂, h₂⟩ := birational_closureHom (D := R) y
    refine ⟨algebraMap R (Spec R).functionField (d₁ * e₂) /
      algebraMap R (Spec R).functionField (d₂ * e₁), ?_⟩
    have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
    have hinj := IsFractionRing.injective (closureRing R) (Spec (closureRing R)).functionField
    have he₁ : e₁ ≠ 0 := by
      rintro rfl
      rw [map_zero] at h₂
      exact hy0 ((mul_eq_zero.mp h₂).resolve_left
        fun h ↦ he₂ (closureHom_injective R (h.trans (map_zero _).symm)))
    have hden : algebraMap (closureRing R) (Spec (closureRing R)).functionField
        (closureHom R (d₂ * e₁)) ≠ 0 :=
      (map_ne_zero_iff _ hinj).mpr fun h ↦
        mul_ne_zero hd₂ he₁ (closureHom_injective R (h.trans (map_zero _).symm))
    rw [map_div₀, genericFunctionFieldMap_closureHom, genericFunctionFieldMap_closureHom,
      div_eq_div_iff hden ((map_ne_zero_iff _ hinj).mpr hy0), ← map_mul, ← map_mul]
    congr 1
    change algebraMap R _ (d₁ * e₂) * y = x * algebraMap R _ (d₂ * e₁)
    rw [map_mul, map_mul, ← h₁, ← h₂]
    ring
  intro G
  have haG := (ConcreteCategory.bijective_of_isIso (functionFieldIsoOfIsOpenImmersion a).hom)
  have hbG := (ConcreteCategory.bijective_of_isIso (functionFieldIsoOfIsOpenImmersion b).hom)
  obtain ⟨u, hu⟩ := hsurj (a.genericFunctionFieldMap ha G)
  obtain ⟨g, rfl⟩ := hbG.2 u
  refine ⟨g, haG.1 ?_⟩
  exact (hcomp g).symm.trans hu

end SpecFibre

end Hartshorne

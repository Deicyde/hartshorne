/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.GradedLocalizationLength
import Hartshorne.Intersection.GradedMultiplicity
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.OrderOfVanishing
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# Orders of quotients of forms along an integral subscheme of `Proj`

Let `A` be an `ℕ`-graded domain and `i : V ⟶ Proj A` a closed immersion of an integral
scheme, with generic point mapping to the homogeneous prime `𝔭`. For forms `F, G` of the same
degree with `G ∉ 𝔭`, `F / G` is a rational function on `V` (`functionFieldQuot`): the image of
`F / G ∈ A₍𝔭₎ = 𝒪_{Proj A, 𝔭}` in `𝒪_{V, ξ} = K(V)`. These rational functions multiply like
fractions (`functionFieldQuot_mul`, `functionFieldQuot_eq_of_mul_eq`).

Let `y ∈ V` be a codimension-one point mapping to the homogeneous prime `𝔮`, let `L ∈ A₁ ∖ 𝔮` and
let `F ∉ 𝔭` be a form of degree `e`. Then the order of `F / Lᵉ` at `y` is the length of
`(A / (𝔭 + F))_𝔮` over `A_𝔮` (`ord_functionFieldQuot_pow`). Indeed `𝒪_{V,y}` is the quotient of
`A₍𝔮₎ = 𝒪_{Proj A, 𝔮}` by the ideal of fractions with numerator in `𝔭`, the order is the length
of `A₍𝔮₎ / (𝔭₍𝔮₎ + F / Lᵉ)`, and lengths do not change under `A₍𝔮₎ → A_𝔮`
(`Hartshorne.GradedLocalizationLength.length_quotient_map_atPrime`), where the ideal generated is
`(𝔭 + F) A_𝔮`.
-/

universe u

open AlgebraicGeometry CategoryTheory HomogeneousLocalization IsLocalRing Order

namespace Hartshorne.ProjectiveSubvarietyOrder

section Algebra

/-- For a surjective homomorphism `ψ : R → B` and `r ∈ R`,
`ℓ_B(B / ψ(r)) = ℓ_R(R / (ker ψ + r))`. -/
theorem length_quotient_span_map_of_surjective {R B : Type*} [CommRing R] [CommRing B]
    (ψ : R →+* B) (hψ : Function.Surjective ψ) (r : R) :
    Module.length B (B ⧸ Ideal.span {ψ r}) =
      Module.length R (R ⧸ (RingHom.ker ψ ⊔ Ideal.span {r})) := by
  let _ : Algebra R B := ψ.toAlgebra
  rw [← Module.length_eq_of_surjective (S := R) (R := B) (M := B ⧸ Ideal.span {ψ r}) hψ]
  let g : R →ₐ[R] B ⧸ Ideal.span {ψ r} :=
    (Ideal.Quotient.mkₐ R (Ideal.span {ψ r})).comp (Algebra.ofId R B)
  have hg : Function.Surjective g :=
    (Ideal.Quotient.mkₐ_surjective R _).comp hψ
  have hker : RingHom.ker g = RingHom.ker ψ ⊔ Ideal.span {r} := by
    have h1 : RingHom.ker g = Ideal.comap ψ (Ideal.span {ψ r}) := by
      ext x
      change (Ideal.Quotient.mk _ (ψ x) = 0) ↔ _
      rw [Ideal.Quotient.eq_zero_iff_mem]
      rfl
    rw [h1, ← Set.image_singleton, ← Ideal.map_span, Ideal.comap_map_of_surjective _ hψ, sup_comm]
    rfl
  rw [← (Ideal.quotientKerAlgEquivOfSurjective hg).toLinearEquiv.length_eq]
  exact congrArg (fun I : Ideal R ↦ Module.length R (R ⧸ I)) hker

end Algebra

variable {A : Type u} [CommRing A] {R : Type*} [CommRing R] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

/-- `F / G` in the local ring of `Proj A` at `x`, for forms `F, G` of the same degree with
`G ∉ x`. -/
noncomputable def stalkQuot (x : Proj 𝒜) {d : ℕ} {F G : A} (hF : F ∈ 𝒜 d) (hG : G ∈ 𝒜 d)
    (hGx : G ∉ x.asHomogeneousIdeal) : (Proj 𝒜).presheaf.stalk x :=
  (Proj.stalkIso 𝒜 x).inv (HomogeneousLocalization.mk ⟨d, ⟨F, hF⟩, ⟨G, hG⟩, hGx⟩)

theorem stalkIso_hom_stalkQuot (x : Proj 𝒜) {d : ℕ} {F G : A} (hF : F ∈ 𝒜 d) (hG : G ∈ 𝒜 d)
    (hGx : G ∉ x.asHomogeneousIdeal) :
    (Proj.stalkIso 𝒜 x).hom (stalkQuot 𝒜 x hF hG hGx) =
      HomogeneousLocalization.mk ⟨d, ⟨F, hF⟩, ⟨G, hG⟩, hGx⟩ := by
  rw [stalkQuot, ← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]

/-- A generization in `Proj A` has a smaller homogeneous prime. -/
theorem asHomogeneousIdeal_le_of_specializes {x x' : Proj 𝒜} (h : x' ⤳ x) :
    x'.asHomogeneousIdeal ≤ x.asHomogeneousIdeal :=
  (ProjectiveSpectrum.le_iff_mem_closure (𝒜 := 𝒜) x' x).mpr
    (specializes_iff_mem_closure.mp h)

/-- `F / G` at `x` generizes to `F / G` at `x'`. -/
theorem stalkSpecializes_stalkQuot {x x' : Proj 𝒜} (h : x' ⤳ x) {d : ℕ} {F G : A}
    (hF : F ∈ 𝒜 d) (hG : G ∈ 𝒜 d) (hGx : G ∉ x.asHomogeneousIdeal) :
    (Proj 𝒜).presheaf.stalkSpecializes h (stalkQuot 𝒜 x hF hG hGx) =
      stalkQuot 𝒜 x' hF hG (fun hG' ↦ hGx (asHomogeneousIdeal_le_of_specializes 𝒜 h hG')) := by
  change (Proj 𝒜).presheaf.stalkSpecializes h ((Proj.stalkIso' 𝒜 x).symm _) =
    (Proj.stalkIso' 𝒜 x').symm _
  exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ h _

variable {𝒜}

/-- `F / G` as a rational function on an integral scheme `V` with a morphism `i : V ⟶ Proj A`,
for forms `F, G` of the same degree with `G` not in the prime of the image of the generic
point. -/
noncomputable def functionFieldQuot {V : Scheme.{u}} [IsIntegral V] (i : V ⟶ Proj 𝒜) {d : ℕ}
    {F G : A} (hF : F ∈ 𝒜 d) (hG : G ∈ 𝒜 d)
    (hGv : G ∉ (i (genericPoint V)).asHomogeneousIdeal) : V.functionField :=
  i.stalkMap (genericPoint V) (stalkQuot 𝒜 _ hF hG hGv)

theorem algebraMap_stalkMap_stalkQuot {V : Scheme.{u}} [IsIntegral V] (i : V ⟶ Proj 𝒜) (y : V)
    {d : ℕ} {F G : A} (hF : F ∈ 𝒜 d) (hG : G ∈ 𝒜 d) (hGy : G ∉ (i y).asHomogeneousIdeal)
    (hGv : G ∉ (i (genericPoint V)).asHomogeneousIdeal) :
    algebraMap (V.presheaf.stalk y) V.functionField (i.stalkMap y (stalkQuot 𝒜 _ hF hG hGy)) =
      functionFieldQuot i hF hG hGv := by
  have hξ : genericPoint V ⤳ y := (genericPoint_spec V).specializes trivial
  change V.presheaf.stalkSpecializes hξ _ = _
  rw [← Scheme.Hom.stalkSpecializes_stalkMap_apply, stalkSpecializes_stalkQuot]
  rfl

theorem stalkQuot_mul (x : Proj 𝒜) {d d' : ℕ} {F G F' G' : A} (hF : F ∈ 𝒜 d) (hG : G ∈ 𝒜 d)
    (hGx : G ∉ x.asHomogeneousIdeal) (hF' : F' ∈ 𝒜 d') (hG' : G' ∈ 𝒜 d')
    (hG'x : G' ∉ x.asHomogeneousIdeal) :
    stalkQuot 𝒜 x hF hG hGx * stalkQuot 𝒜 x hF' hG' hG'x =
      stalkQuot 𝒜 x (SetLike.mul_mem_graded hF hF') (SetLike.mul_mem_graded hG hG')
        (fun h ↦ (x.isPrime.mem_or_mem h).elim hGx hG'x) := by
  rw [stalkQuot, stalkQuot, stalkQuot, ← map_mul]
  rfl

theorem stalkQuot_eq_of_mul_eq (x : Proj 𝒜) {d d' : ℕ} {F G F' G' : A} (hF : F ∈ 𝒜 d)
    (hG : G ∈ 𝒜 d) (hGx : G ∉ x.asHomogeneousIdeal) (hF' : F' ∈ 𝒜 d') (hG' : G' ∈ 𝒜 d')
    (hG'x : G' ∉ x.asHomogeneousIdeal) (h : F * G' = F' * G) :
    stalkQuot 𝒜 x hF hG hGx = stalkQuot 𝒜 x hF' hG' hG'x := by
  rw [stalkQuot, stalkQuot]
  congr 1
  apply HomogeneousLocalization.val_injective
  simp only [val_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp only [OneMemClass.coe_one, one_mul]; rw [mul_comm G' F, h, mul_comm]⟩

theorem functionFieldQuot_mul {V : Scheme.{u}} [IsIntegral V] (i : V ⟶ Proj 𝒜) {d d' : ℕ}
    {F G F' G' : A} (hF : F ∈ 𝒜 d) (hG : G ∈ 𝒜 d)
    (hGv : G ∉ (i (genericPoint V)).asHomogeneousIdeal) (hF' : F' ∈ 𝒜 d') (hG' : G' ∈ 𝒜 d')
    (hG'v : G' ∉ (i (genericPoint V)).asHomogeneousIdeal) :
    functionFieldQuot i hF hG hGv * functionFieldQuot i hF' hG' hG'v =
      functionFieldQuot i (SetLike.mul_mem_graded hF hF') (SetLike.mul_mem_graded hG hG')
        (fun h ↦ ((i (genericPoint V)).isPrime.mem_or_mem h).elim hGv hG'v) := by
  rw [functionFieldQuot, functionFieldQuot, functionFieldQuot, ← map_mul, stalkQuot_mul]

theorem functionFieldQuot_eq_of_mul_eq {V : Scheme.{u}} [IsIntegral V] (i : V ⟶ Proj 𝒜)
    {d d' : ℕ} {F G F' G' : A} (hF : F ∈ 𝒜 d) (hG : G ∈ 𝒜 d)
    (hGv : G ∉ (i (genericPoint V)).asHomogeneousIdeal) (hF' : F' ∈ 𝒜 d') (hG' : G' ∈ 𝒜 d')
    (hG'v : G' ∉ (i (genericPoint V)).asHomogeneousIdeal) (h : F * G' = F' * G) :
    functionFieldQuot i hF hG hGv = functionFieldQuot i hF' hG' hG'v := by
  rw [functionFieldQuot, functionFieldQuot, stalkQuot_eq_of_mul_eq _ hF hG hGv hF' hG' hG'v h]

section Order

open GradedLocalizationLength

/-- A fraction `a / s` in the homogeneous localization at `𝔭` is a unit exactly when `a ∉ 𝔭`. -/
theorem isUnit_mk_iff (𝔭 : Ideal A) [𝔭.IsPrime]
    (f : HomogeneousLocalization.NumDenSameDeg 𝒜 𝔭.primeCompl) :
    IsUnit (HomogeneousLocalization.mk f : HomogeneousLocalization.AtPrime 𝒜 𝔭) ↔
      (f.num : A) ∉ 𝔭 := by
  rw [← isUnit_iff_isUnit_val, val_mk, Localization.mk_eq_mk']
  have h := IsLocalization.mk'_spec (Localization.AtPrime 𝔭) (f.num : A) ⟨f.den, f.den_mem⟩
  have hs : IsUnit (algebraMap A (Localization.AtPrime 𝔭) f.den) :=
    IsLocalization.map_units _ (⟨f.den, f.den_mem⟩ : 𝔭.primeCompl)
  refine (and_iff_left hs).symm.trans ?_
  rw [← IsUnit.mul_iff, h]
  exact IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime 𝔭) 𝔭 (f.num : A)

variable {V : Scheme.{u}} [IsIntegral V] (i : V ⟶ Proj 𝒜) [IsClosedImmersion i]

/-- The kernel of `𝒪_{Proj A, i(y)} → 𝒪_{V, y}`: a fraction `a / s` maps to zero exactly when
`a` lies in the prime `𝔭` of the image of the generic point of `V`. -/
theorem stalkMap_stalkQuot_eq_zero_iff (y : V) {d : ℕ} {a s : A} (ha : a ∈ 𝒜 d)
    (hs : s ∈ 𝒜 d) (hsy : s ∉ (i y).asHomogeneousIdeal) :
    i.stalkMap y (stalkQuot 𝒜 _ ha hs hsy) = 0 ↔ a ∈ (i (genericPoint V)).asHomogeneousIdeal := by
  have hsv : s ∉ (i (genericPoint V)).asHomogeneousIdeal := fun h ↦ hsy
    (asHomogeneousIdeal_le_of_specializes 𝒜
      (i.base.hom.map_specializes ((genericPoint_spec V).specializes trivial)) h)
  have hinj := IsFractionRing.injective (V.presheaf.stalk y) V.functionField
  rw [← hinj.eq_iff, map_zero, algebraMap_stalkMap_stalkQuot i y ha hs hsy hsv, functionFieldQuot,
    ← RingHom.mem_ker, IsLocalRing.ker_eq_maximalIdeal _ (i.stalkMap_surjective _),
    mem_maximalIdeal, mem_nonunits_iff, not_iff_comm]
  have := (i (genericPoint V)).isPrime
  refine (isUnit_mk_iff (i (genericPoint V)).asHomogeneousIdeal.toIdeal
    ⟨d, ⟨a, ha⟩, ⟨s, hs⟩, hsv⟩).symm.trans ?_
  rw [← stalkIso_hom_stalkQuot]
  have : IsLocalHom (Proj.stalkIso 𝒜 (i (genericPoint V))).hom.hom := isLocalHom_of_isIso _
  exact isUnit_map_iff _ _

omit [IsClosedImmersion i] in
/-- `Lᵉ ∉ 𝔭` when `L ∉ 𝔮` for a point `y` of `V`. -/
theorem pow_notMem_genericPoint {y : V} {L : A} (hLy : L ∉ (i y).asHomogeneousIdeal) (e : ℕ) :
    L ^ e ∉ (i (genericPoint V)).asHomogeneousIdeal := fun h ↦ hLy
  (asHomogeneousIdeal_le_of_specializes 𝒜
    (i.base.hom.map_specializes ((genericPoint_spec V).specializes trivial))
    ((i (genericPoint V)).isPrime.mem_of_pow_mem e h))

/-- The localization at `𝔮` of `A / I` is `A_𝔮 / I A_𝔮`. -/
noncomputable def localizedQuotientEquivMap (𝔮 : Ideal A) [𝔮.IsPrime] (I : Ideal A) :
    LocalizedModule 𝔮.primeCompl (A ⧸ I) ≃ₗ[Localization.AtPrime 𝔮]
      (Localization.AtPrime 𝔮 ⧸ I.map (algebraMap A (Localization.AtPrime 𝔮))) :=
  (localizedQuotientEquiv 𝔮.primeCompl I).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (by
      change Submodule.localized' (Localization.AtPrime 𝔮)
        𝔮.primeCompl (Algebra.linearMap A (Localization.AtPrime 𝔮)) I = _
      rw [Ideal.localized'_eq_map])

/-- **Orders of `F / Lᵉ` along an integral subscheme of `Proj` are graded multiplicities.** Let
`A` be an `ℕ`-graded domain, `i : V ⟶ Proj A` a closed immersion of a locally Noetherian
integral scheme whose generic point maps to the homogeneous prime `𝔭`, and `y ∈ V` a point of
codimension one mapping to the homogeneous prime `𝔮`. Let `L ∈ A₁ ∖ 𝔮` and let `F ∉ 𝔭` be a form
of degree `e`. Then the order of the rational function `F / Lᵉ` at `y` is
`ℓ_{A_𝔮}((A / (𝔭 + F))_𝔮)`. -/
theorem ord_functionFieldQuot_pow [IsDomain A] [IsLocallyNoetherian V] {y : V}
    (hy : coheight y = 1) {L : A} (hL : L ∈ 𝒜 1) (hLy : L ∉ (i y).asHomogeneousIdeal) {e : ℕ}
    {F : A} (hF : F ∈ 𝒜 e) (hFv : F ∉ (i (genericPoint V)).asHomogeneousIdeal)
    (hLe : L ^ e ∈ 𝒜 e) :
    V.ord (functionFieldQuot i hF hLe (pow_notMem_genericPoint i hLy e)) y =
      ((gradedMultiplicity A
        (A ⧸ ((i (genericPoint V)).asHomogeneousIdeal.toIdeal ⊔ Ideal.span {F}))
        ⟨(i y).asHomogeneousIdeal.toIdeal, (i y).isPrime⟩).toNat : ℤ) := by
  classical
  set x := i y with hx
  set v := i (genericPoint V) with hv
  set 𝔮 := x.asHomogeneousIdeal.toIdeal with h𝔮
  set 𝔭 := v.asHomogeneousIdeal.toIdeal with h𝔭
  have : 𝔮.IsPrime := x.isPrime
  have hLx : L ∉ 𝔮 := hLy
  have hLex : L ^ e ∉ x.asHomogeneousIdeal := fun h ↦ hLy (x.isPrime.mem_of_pow_mem e h)
  -- the surjection `ψ : A₍𝔮₎ → 𝒪_{V,y}`
  let ψ : HomogeneousLocalization.AtPrime 𝒜 𝔮 →+* V.presheaf.stalk y :=
    (i.stalkMap y).hom.comp (Proj.stalkIso 𝒜 x).inv.hom
  have hψ : Function.Surjective ψ :=
    (i.stalkMap_surjective y).comp (ConcreteCategory.bijective_of_isIso (Proj.stalkIso 𝒜 x).inv).2
  have hker : ∀ f : HomogeneousLocalization.NumDenSameDeg 𝒜 𝔮.primeCompl,
      ψ (HomogeneousLocalization.mk f) = 0 ↔ (f.num : A) ∈ 𝔭 := fun f ↦
    stalkMap_stalkQuot_eq_zero_iff i y f.num.2 f.den.2 f.den_mem
  let a0 := overPow 𝒜 𝔮 hL hLx hF
  have hψa0 : ψ a0 = i.stalkMap y (stalkQuot 𝒜 x hF hLe hLex) := rfl
  have halg : algebraMap _ V.functionField (ψ a0) =
      functionFieldQuot i hF hLe (pow_notMem_genericPoint i hLy e) := by
    rw [hψa0]
    exact algebraMap_stalkMap_stalkQuot i y hF hLe hLex _
  have hne : ψ a0 ≠ 0 := fun h ↦ hFv ((hker _).mp h)
  -- the order is the length of `𝒪_{V,y} / (F / Lᵉ)`
  have : Ring.KrullDimLE 1 (V.presheaf.stalk y) := krullDimLE_of_coheight_le hy.le
  have hnz : ψ a0 ∈ nonZeroDivisors _ := mem_nonZeroDivisors_of_ne_zero hne
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (Ring.ord_ne_top hnz)
  have hord : V.ord (functionFieldQuot i hF hLe (pow_notMem_genericPoint i hLy e)) y = m := by
    rw [← halg, Scheme.ord_eq_iff hy (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hnz)]
    unfold Scheme.ordHom
    rw [Ring.ordFrac_eq_ord _ hne]
    simp [Ring.ordMonoidWithZeroHom, ← hm, hne]
  -- the ideal generated in `A_𝔮`
  have hmap : (RingHom.ker ψ ⊔ Ideal.span {a0}).map (algebraMap _ (Localization.AtPrime 𝔮)) =
      (𝔭 ⊔ Ideal.span {F}).map (algebraMap A (Localization.AtPrime 𝔮)) := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      refine sup_le ?_ ?_
      · intro z hz
        obtain ⟨f, rfl⟩ := HomogeneousLocalization.mk_surjective z
        have hf𝔭 : (f.num : A) ∈ 𝔭 := (hker f).mp hz
        rw [Ideal.mem_comap, HomogeneousLocalization.algebraMap_apply, val_mk,
          Localization.mk_eq_mk', IsLocalization.mk'_eq_mul_mk'_one]
        exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (Ideal.mem_sup_left hf𝔭))
      · rw [Ideal.span_le]
        rintro _ rfl
        rw [SetLike.mem_coe, Ideal.mem_comap, HomogeneousLocalization.algebraMap_apply,
          show a0 = HomogeneousLocalization.mk ⟨e, ⟨F, hF⟩, ⟨L ^ e, hLe⟩, hLex⟩ from rfl, val_mk, Localization.mk_eq_mk', IsLocalization.mk'_eq_mul_mk'_one]
        exact Ideal.mul_mem_right _ _
          (Ideal.mem_map_of_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self F)))
    · rw [Ideal.map_le_iff_le_comap]
      refine sup_le ?_ ?_
      · intro p hp
        rw [Ideal.mem_comap, ← DirectSum.sum_support_decompose 𝒜 p, map_sum]
        refine sum_mem fun d _ ↦ ?_
        have hpd : (DirectSum.decompose 𝒜 p d : A) ∈ 𝔭 := v.asHomogeneousIdeal.isHomogeneous d hp
        rw [← overPow_val_mul_pow 𝒜 𝔮 hL hLx (DirectSum.decompose 𝒜 p d).2]
        refine Ideal.mul_mem_right _ _ (show algebraMap _ (Localization.AtPrime 𝔮)
          (overPow 𝒜 𝔮 hL hLx (DirectSum.decompose 𝒜 p d).2) ∈ _ from
            Ideal.mem_map_of_mem _ (Ideal.mem_sup_left ?_))
        rw [RingHom.mem_ker]
        exact (hker _).mpr hpd
      · rw [Ideal.span_le]
        rintro _ rfl
        rw [SetLike.mem_coe, Ideal.mem_comap, ← overPow_val_mul_pow 𝒜 𝔮 hL hLx hF]
        exact Ideal.mul_mem_right _ _ (show algebraMap _ (Localization.AtPrime 𝔮) a0 ∈ _ from
          Ideal.mem_map_of_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
  have hlen : Ring.ord (V.presheaf.stalk y) (ψ a0) =
      gradedMultiplicity A (A ⧸ (𝔭 ⊔ Ideal.span {F})) ⟨𝔮, x.isPrime⟩ := by
    rw [Ring.ord, length_quotient_span_map_of_surjective ψ hψ a0,
      ← length_quotient_map_atPrime 𝒜 𝔮 x.asHomogeneousIdeal.isHomogeneous hL hLx, hmap]
    exact (localizedQuotientEquivMap 𝔮 (𝔭 ⊔ Ideal.span {F})).length_eq.symm
  rw [hord, ← hlen, ← hm, ENat.toNat_natCast]

end Order

end Hartshorne.ProjectiveSubvarietyOrder

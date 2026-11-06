/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ProjectiveSpaceChart
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Morphisms into `Proj` from coordinate data

Hartshorne, *Algebraic Geometry*, II.7 (morphisms to projective space), in the elementary
form used to build explicit morphisms such as the Segre embedding (Exercise II.4.9).

For a graded ring `A`, a ring `B` and a ring map `F : A → B` sending a homogeneous element `f`
of positive degree to a unit, `projChartMap F f` is the morphism `Spec B → Proj A` obtained from the
induced map `A_(f) → B` and the chart `Spec A_(f) ≅ D₊(f)`. We prove:

* `projChartMap_eq`: the result does not depend on which inverted homogeneous element is used;
* `projChartMap_eq_of_scale`: rescaling each degree `n` component by `u ^ n` does not change it;
* `SpecMap_projChartMap`: naturality in `B`;
* `projChartMap_preimage_basicOpen`: the preimage of `D₊(g)` is the basic open of `F g`;
* `ι_comp_eq_toSpecΓ_SpecMap` and `eq_awayLift_chartPolyMap`: every morphism into `Proj`,
  restricted to an open set mapping into a coordinate chart of projective space, is of this
  form;
* `glueOpens`: gluing morphisms along an open cover described by opens;
* `appLE_chartRatio_cocycle`: the cocycle identity `xₘ/xₖ = (xᵢ/xₖ)(xₘ/xᵢ)` for coordinate
  ratios pulled back along a morphism into projective space.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomogeneousLocalization

namespace Hartshorne

section AwayLift

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] {𝒜 : ℕ → σ}
  [GradedRing 𝒜] {B : Type*} [CommRing B]

/-- The ring map `A_(f) → B` induced by a ring map `F : A → B` with `F f` a unit. -/
def awayLift (F : A →+* B) (f : A) (hf : IsUnit (F f)) : Away 𝒜 f →+* B :=
  (IsLocalization.Away.lift (S := Localization.Away f) f hf).comp (algebraMap (Away 𝒜 f) (Localization.Away f))

theorem awayLift_mk (F : A →+* B) {f : A} (hf : IsUnit (F f)) {d : ℕ} (hd : f ∈ 𝒜 d)
    (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • d)) :
    awayLift (𝒜 := 𝒜) F f hf (Away.mk 𝒜 hd n a ha) * F f ^ n = F a := by
  simp only [awayLift, RingHom.coe_comp, Function.comp_apply,
    HomogeneousLocalization.algebraMap_apply, Away.val_mk, Localization.mk_eq_mk']
  have h := congrArg (IsLocalization.Away.lift (S := Localization.Away f) f hf)
    (IsLocalization.mk'_spec (Localization.Away f) a
      (⟨f ^ n, n, rfl⟩ : Submonoid.powers f))
  rw [map_mul] at h
  simp only [IsLocalization.Away.lift, IsLocalization.lift_eq] at h ⊢
  rw [map_pow] at h
  exact h

theorem awayLift_mk_eq (F : A →+* B) {f : A} (hf : IsUnit (F f)) {d : ℕ} (hd : f ∈ 𝒜 d)
    (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • d)) :
    awayLift (𝒜 := 𝒜) F f hf (Away.mk 𝒜 hd n a ha) = F a * ((hf.unit⁻¹ : Bˣ) : B) ^ n := by
  rw [← awayLift_mk F hf hd n a ha, mul_assoc, ← mul_pow]
  simp

/-- Ring maps out of `A_(f)` agree once they agree on the fractions `a / f ^ n`. -/
theorem away_ringHom_ext {f : A} {d : ℕ} (hd : f ∈ 𝒜 d) {φ ψ : Away 𝒜 f →+* B}
    (h : ∀ n a ha, φ (Away.mk 𝒜 hd n a ha) = ψ (Away.mk 𝒜 hd n a ha)) : φ = ψ := by
  ext z
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hd z
  exact h n a ha

/-- Characterization of `awayLift` by its values on fractions. -/
theorem eq_awayLift (F : A →+* B) {f : A} (hf : IsUnit (F f)) {d : ℕ} (hd : f ∈ 𝒜 d)
    (φ : Away 𝒜 f →+* B)
    (h : ∀ n a ha, φ (Away.mk 𝒜 hd n a ha) * F f ^ n = F a) :
    φ = awayLift F f hf := by
  apply away_ringHom_ext hd
  intro n a ha
  apply (hf.pow n).mul_left_injective
  simp only
  rw [h, awayLift_mk]

theorem awayLift_comp_awayMap (F : A →+* B) {f g x : A} {d e : ℕ} (hd : f ∈ 𝒜 d)
    (hg : g ∈ 𝒜 e) (hx : x = f * g) (hf : IsUnit (F f)) (hxu : IsUnit (F x)) :
    (awayLift (𝒜 := 𝒜) F x hxu).comp (awayMap 𝒜 hg hx) = awayLift F f hf := by
  subst hx
  apply eq_awayLift F hf hd
  intro n a ha
  have hgu : IsUnit (F g) := by
    rw [map_mul] at hxu
    exact isUnit_of_mul_isUnit_right hxu
  rw [RingHom.comp_apply, awayMap_mk]
  apply (hgu.pow n).mul_left_injective
  simp only
  rw [mul_assoc, ← mul_pow, ← map_mul, awayLift_mk, map_mul, map_pow]

theorem awayLift_eq_of_scale (F F' : A →+* B) {f : A} {d : ℕ} (hd : f ∈ 𝒜 d) (u : B)
    (hscale : ∀ n a, a ∈ 𝒜 n → F' a = u ^ n * F a)
    (hf : IsUnit (F f)) (hf' : IsUnit (F' f)) :
    awayLift (𝒜 := 𝒜) F' f hf' = awayLift F f hf := by
  symm
  apply eq_awayLift F' hf' hd
  intro n a ha
  rw [hscale _ _ ha, hscale _ _ hd, ← awayLift_mk F hf hd n a ha, mul_pow, ← pow_mul,
    smul_eq_mul, mul_comm n d]
  ring

theorem awayLift_naturality (F : A →+* B) {C : Type*} [CommRing C] (β : B →+* C) {f : A}
    {d : ℕ} (hd : f ∈ 𝒜 d) (hf : IsUnit (F f)) (hf' : IsUnit ((β.comp F) f)) :
    β.comp (awayLift (𝒜 := 𝒜) F f hf) = awayLift (β.comp F) f hf' := by
  apply eq_awayLift _ hf' hd
  intro n a ha
  simp only [RingHom.comp_apply]
  rw [← map_pow, ← map_mul, awayLift_mk]

end AwayLift


section ChartMap

universe u

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] {𝒜 : ℕ → σ}
  [GradedRing 𝒜]

/-- The morphism `Spec B → Proj 𝒜` determined by a ring map `F : A → B` sending the
homogeneous element `f` of positive degree to a unit: it is `Spec` of the induced map
`A_(f) → B` followed by the chart `Spec A_(f) ≅ D₊(f) ⊆ Proj 𝒜`. -/
def projChartMap {B : CommRingCat.{u}} (F : A →+* B) {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m)
    (hm : 0 < m) (hf : IsUnit (F f)) : Spec B ⟶ Proj 𝒜 :=
  Spec.map (CommRingCat.ofHom (awayLift (𝒜 := 𝒜) F f hf)) ≫ Proj.awayι 𝒜 f f_deg hm

theorem awayι_congr_deg {f : A} {m m' : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m)
    (f_deg' : f ∈ 𝒜 m') (hm' : 0 < m') (h : m = m') :
    Proj.awayι 𝒜 f f_deg hm = Proj.awayι 𝒜 f f_deg' hm' := by
  subst h
  rfl

/-- The chart morphism does not depend on the chosen coordinate inverted by `F`. -/
theorem projChartMap_eq {B : CommRingCat.{u}} (F : A →+* B) {f g : A} {m n : ℕ}
    (f_deg : f ∈ 𝒜 m) (hm : 0 < m) (hf : IsUnit (F f))
    (g_deg : g ∈ 𝒜 n) (hn : 0 < n) (hg : IsUnit (F g)) :
    projChartMap F f_deg hm hf = projChartMap F g_deg hn hg := by
  have hfg : IsUnit (F (f * g)) := by rw [map_mul]; exact hf.mul hg
  have h1 : projChartMap F f_deg hm hf =
      Spec.map (CommRingCat.ofHom (awayLift (𝒜 := 𝒜) F (f * g) hfg)) ≫
        Proj.awayι 𝒜 (f * g) (SetLike.mul_mem_graded f_deg g_deg) (by omega) := by
    rw [projChartMap, ← awayLift_comp_awayMap F f_deg g_deg rfl hf hfg, CommRingCat.ofHom_comp,
      Spec.map_comp, Category.assoc, Proj.SpecMap_awayMap_awayι]
  have h2 : projChartMap F g_deg hn hg =
      Spec.map (CommRingCat.ofHom (awayLift (𝒜 := 𝒜) F (f * g) hfg)) ≫
        Proj.awayι 𝒜 (f * g) (SetLike.mul_mem_graded f_deg g_deg) (by omega) := by
    rw [projChartMap, ← awayLift_comp_awayMap F g_deg f_deg (mul_comm f g) hg hfg,
      CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, Proj.SpecMap_awayMap_awayι,
      awayι_congr_deg _ _ _ _ (Nat.add_comm n m)]
  rw [h1, h2]

/-- Rescaling all homogeneous elements of degree `n` by `u ^ n` does not change the chart
morphism. -/
theorem projChartMap_eq_of_scale {B : CommRingCat.{u}} (F F' : A →+* B) (u : B)
    (hscale : ∀ n a, a ∈ 𝒜 n → F' a = u ^ n * F a) {f : A} {m : ℕ}
    (f_deg : f ∈ 𝒜 m) (hm : 0 < m) (hf : IsUnit (F f)) (hf' : IsUnit (F' f)) :
    projChartMap F' f_deg hm hf' = projChartMap F f_deg hm hf := by
  rw [projChartMap, projChartMap, awayLift_eq_of_scale F F' f_deg u hscale hf hf']

/-- Naturality of the chart morphism in the ring. -/
theorem SpecMap_projChartMap {B C : CommRingCat.{u}} (F : A →+* B) (β : B ⟶ C) {f : A} {m : ℕ}
    (f_deg : f ∈ 𝒜 m) (hm : 0 < m) (hf : IsUnit (F f)) (hf' : IsUnit ((β.hom.comp F) f)) :
    Spec.map β ≫ projChartMap F f_deg hm hf = projChartMap (β.hom.comp F) f_deg hm hf' := by
  rw [projChartMap, projChartMap, ← Category.assoc, ← Spec.map_comp,
    ← awayLift_naturality F β.hom f_deg hf hf']
  rfl

/-- The preimage of a standard open under a chart morphism. -/
theorem projChartMap_preimage_basicOpen {B : CommRingCat.{u}} (F : A →+* B) {f g : A} {m n : ℕ}
    (f_deg : f ∈ 𝒜 m) (hm : 0 < m) (hf : IsUnit (F f)) (g_deg : g ∈ 𝒜 n) (hn : 0 < n) :
    projChartMap F f_deg hm hf ⁻¹ᵁ Proj.basicOpen 𝒜 g = PrimeSpectrum.basicOpen (F g) := by
  rw [projChartMap, Scheme.Hom.comp_preimage, Proj.awayι_preimage_basicOpen 𝒜 f_deg hm g_deg hn]
  have : Spec.map (CommRingCat.ofHom (awayLift (𝒜 := 𝒜) F f hf)) ⁻¹ᵁ
      PrimeSpectrum.basicOpen (Away.isLocalizationElem f_deg g_deg) =
      PrimeSpectrum.basicOpen (awayLift (𝒜 := 𝒜) F f hf
        (Away.isLocalizationElem f_deg g_deg)) :=
    PrimeSpectrum.comap_basicOpen _ _
  rw [this, Away.isLocalizationElem, awayLift_mk_eq]
  have key : PrimeSpectrum.basicOpen (F (g ^ m) * ((hf.unit⁻¹ : (↑B : Type u)ˣ) : B) ^ n) =
      PrimeSpectrum.basicOpen (F g) := by
    have hu : IsUnit (((hf.unit⁻¹ : (↑B : Type u)ˣ) : B) ^ n) := (Units.isUnit _).pow n
    have htop : PrimeSpectrum.basicOpen (((hf.unit⁻¹ : (↑B : Type u)ˣ) : B) ^ n) = ⊤ := by
      refine top_unique fun x _ => ?_
      exact fun h => x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
    rw [PrimeSpectrum.basicOpen_mul, map_pow, PrimeSpectrum.basicOpen_pow _ _ hm, htop,
      inf_top_eq]
  exact key

end ChartMap

section Glue

universe u

/-- Glue morphisms defined on the members of an open cover, given that they agree on
pairwise intersections. -/
def glueOpens {X Y : Scheme.{u}} {ι : Type*} (U : ι → X.Opens) (hU : TopologicalSpace.IsOpenCover U)
    (g : ∀ i, (U i).toScheme ⟶ Y)
    (hg : ∀ i j, X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ g i =
      X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ g j) : X ⟶ Y :=
  (X.openCoverOfIsOpenCover U hU).glueMorphisms g (fun i j => by
    have h := isPullback_opens_inf (U i) (U j)
    change pullback.fst (U i).ι (U j).ι ≫ g i = pullback.snd (U i).ι (U j).ι ≫ g j
    rw [← h.isoPullback_inv_fst, ← h.isoPullback_inv_snd, Category.assoc, Category.assoc]
    congr 1
    exact hg i j)

@[reassoc (attr := simp)]
theorem ι_glueOpens {X Y : Scheme.{u}} {ι : Type*} (U : ι → X.Opens) (hU : TopologicalSpace.IsOpenCover U)
    (g : ∀ i, (U i).toScheme ⟶ Y)
    (hg : ∀ i j, X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ g i =
      X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ g j) (i : ι) :
    (U i).ι ≫ glueOpens U hU g hg = g i :=
  (X.openCoverOfIsOpenCover U hU).ι_glueMorphisms g _ i

end Glue

section ChartRepresentation

universe u

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] {𝒜 : ℕ → σ}
  [GradedRing 𝒜]

/-- A morphism into `Proj`, restricted to an open set mapping into a standard chart, is `Spec`
of the induced ring map on sections followed by the chart. -/
theorem ι_comp_eq_toSpecΓ_SpecMap {Y : Scheme.{u}} (φ : Y ⟶ Proj 𝒜) (U : Y.Opens) {f : A}
    {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) (h : U ≤ φ ⁻¹ᵁ Proj.basicOpen 𝒜 f) :
    U.ι ≫ φ = U.toSpecΓ ≫
      Spec.map (Proj.awayToSection 𝒜 f ≫ φ.appLE (Proj.basicOpen 𝒜 f) U h) ≫
        Proj.awayι 𝒜 f f_deg hm := by
  have hι : (Proj.basicOpen 𝒜 f).ι = Proj.basicOpenToSpec 𝒜 f ≫ Proj.awayι 𝒜 f f_deg hm := by
    rw [← Proj.basicOpenIsoSpec_inv_ι 𝒜 f f_deg hm, ← Category.assoc,
      ← Proj.basicOpenIsoSpec_hom 𝒜 f f_deg hm, Iso.hom_inv_id, Category.id_comp]
  rw [← Scheme.Hom.resLE_comp_ι φ h, hι, Proj.basicOpenToSpec, Spec.map_comp]
  simp only [Category.assoc]
  rw [← Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc]

end ChartRepresentation

section PolynomialCharts

universe u

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] {κ : Type} [DecidableEq κ]

omit [DecidableEq κ] in
theorem chartRatio_self (c : κ) : chartRatio R c c = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [chartRatio_val, HomogeneousLocalization.val_one]
  convert Localization.mk_self
    (⟨X c ^ 1, 1, rfl⟩ : Submonoid.powers (X c : MvPolynomial κ R)) using 2
  simp

variable {R}

/-- Ring maps out of a coordinate chart ring agree once they agree on constants and on the
coordinate ratios. -/
theorem chart_ringHom_ext {B : Type*} [CommRing B] (c0 : κ)
    {φ ψ : HomogeneousLocalization.Away (homogeneousSubmodule κ R) (X c0) →+* B}
    (hC : ∀ r, φ (chartConst R c0 r) = ψ (chartConst R c0 r))
    (hX : ∀ j, φ (chartRatio R c0 j) = ψ (chartRatio R c0 j)) : φ = ψ := by
  have h : φ.comp (chartOfPoly R c0) = ψ.comp (chartOfPoly R c0) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [chartOfPoly, hC]
    · intro j
      simp [chartOfPoly, hX]
  ext z
  have hz : chartOfPoly R c0 (chartToPoly R c0 z) = z :=
    congrArg (fun F => F z) (chartOfPoly_comp_chartToPoly R c0)
  rw [← hz]
  exact congrArg (fun F => F (chartToPoly R c0 z)) h

/-- The coordinate-ratio description of a ring map out of a chart ring. -/
def chartPolyMap {B : Type*} [CommRing B] (c0 : κ)
    (φ : HomogeneousLocalization.Away (homogeneousSubmodule κ R) (X c0) →+* B) :
    MvPolynomial κ R →+* B :=
  eval₂Hom (φ.comp (chartConst R c0)) fun c => φ (chartRatio R c0 c)

omit [DecidableEq κ] in
theorem chartPolyMap_X_self {B : Type*} [CommRing B] (c0 : κ)
    (φ : HomogeneousLocalization.Away (homogeneousSubmodule κ R) (X c0) →+* B) :
    chartPolyMap c0 φ (X c0) = 1 := by
  simp [chartPolyMap, chartRatio_self]

omit [DecidableEq κ] in
theorem isUnit_chartPolyMap_X_self {B : Type*} [CommRing B] (c0 : κ)
    (φ : HomogeneousLocalization.Away (homogeneousSubmodule κ R) (X c0) →+* B) :
    IsUnit (chartPolyMap c0 φ (X c0)) := by
  rw [chartPolyMap_X_self]
  exact isUnit_one

/-- Every ring map out of a chart ring is the localization of its coordinate-ratio
description. -/
theorem eq_awayLift_chartPolyMap {B : Type*} [CommRing B] (c0 : κ)
    (φ : HomogeneousLocalization.Away (homogeneousSubmodule κ R) (X c0) →+* B) :
    φ = awayLift (chartPolyMap c0 φ) (X c0) (isUnit_chartPolyMap_X_self c0 φ) := by
  apply chart_ringHom_ext c0
  · intro r
    simp only [awayLift, RingHom.coe_comp, Function.comp_apply,
      HomogeneousLocalization.algebraMap_apply, chartConst_val, IsLocalization.Away.lift,
      IsLocalization.lift_eq]
    simp [chartPolyMap]
  · intro j
    have h := awayLift_mk (𝒜 := homogeneousSubmodule κ R) (chartPolyMap c0 φ)
      (isUnit_chartPolyMap_X_self c0 φ) (X_mem_homogeneousSubmodule_one R c0) 1 (X j)
      (by simpa using X_mem_homogeneousSubmodule_one R j)
    rw [chartPolyMap_X_self, one_pow, mul_one] at h
    change _ = awayLift _ _ _ (HomogeneousLocalization.Away.mk _ _ _ _ _)
    rw [h]
    simp [chartPolyMap]

end PolynomialCharts

section Restrictions

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

open MvPolynomial

/-- `projChartMap` only depends on the ring map, not on the proof that it inverts the chosen
element. -/
theorem projChartMap_congr {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    {𝒜 : ℕ → σ} [GradedRing 𝒜] {B : CommRingCat.{u}} {F G : A →+* B} (h : F = G) {f : A}
    {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) (hF : IsUnit (F f)) (hG : IsUnit (G f)) :
    projChartMap F f_deg hm hF = projChartMap G f_deg hm hG := by
  subst h
  rfl

/-- A chart ring map sending `x_c` to `1` sends `x_d / x_c` to the image of `x_d`. -/
theorem awayLift_chartRatio {R : Type u} [CommRing R] {κ : Type} {B : Type*} [CommRing B]
    (F : MvPolynomial κ R →+* B) (c d : κ) (hF : F (X c) = 1) (hu : IsUnit (F (X c))) :
    awayLift (𝒜 := homogeneousSubmodule κ R) F (X c) hu (chartRatio R c d) = F (X d) := by
  have h := awayLift_mk (𝒜 := homogeneousSubmodule κ R) F hu
    (X_mem_homogeneousSubmodule_one R c) 1 (X d)
    (by simpa using X_mem_homogeneousSubmodule_one R d)
  rw [hF, one_pow, mul_one] at h
  exact h

/-- Two open sets agreeing on every member of an open cover are equal. -/
theorem opens_eq_of_cover {X : Scheme.{u}} {ι : Type*} (U : ι → X.Opens)
    (hU : TopologicalSpace.IsOpenCover U) {O O' : X.Opens}
    (h : ∀ c, (U c).ι ⁻¹ᵁ O = (U c).ι ⁻¹ᵁ O') : O = O' := by
  ext x
  have hx : x ∈ ⨆ c, U c := by
    rw [hU.iSup_eq_top]
    trivial
  obtain ⟨c, hc⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  have := congrArg (fun V : (U c).toScheme.Opens => (⟨x, hc⟩ : (U c).toScheme) ∈ V) (h c)
  change (x ∈ O) = (x ∈ O') at this
  exact Iff.of_eq this

/-- Ring maps `R → Γ(X, U)` are determined by the induced morphisms `U → Spec R`. -/
theorem toSpecΓ_SpecMap_injective {X : Scheme.{u}} (U : X.Opens) {R : CommRingCat.{u}}
    {φ φ' : R ⟶ Γ(X, U)} (h : U.toSpecΓ ≫ Spec.map φ = U.toSpecΓ ≫ Spec.map φ') : φ = φ' := by
  have h' := congrArg (fun f => f.appTop ≫ U.topIso.hom) h
  simp only [Scheme.Hom.comp_appTop, Category.assoc, Scheme.Opens.toSpecΓ_appTop,
    Iso.inv_hom_id, Category.comp_id, Scheme.ΓSpecIso_naturality] at h'
  rwa [cancel_epi] at h'

section Restrict

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] {𝒜 : ℕ → σ}
  [GradedRing 𝒜]

/-- Restricting a pulled-back chart section to a smaller open set inside the preimage of
`D₊(fg)` is computed by the localization map `A_(f) → A_(fg)`. -/
theorem appLE_awayToSection_restrict {Y : Scheme.{u}} (φ : Y ⟶ Proj 𝒜) {f g x : A} {e : ℕ}
    (g_deg : g ∈ 𝒜 e) (hx : x = f * g) {U V : Y.Opens} (hVU : V ≤ U)
    (hU : U ≤ φ ⁻¹ᵁ Proj.basicOpen 𝒜 f)
    (hV : V ≤ φ ⁻¹ᵁ Proj.basicOpen 𝒜 x) (y : Away 𝒜 f) :
    Y.presheaf.map (homOfLE hVU).op
        (φ.appLE (Proj.basicOpen 𝒜 f) U hU (Proj.awayToSection 𝒜 f y)) =
      φ.appLE (Proj.basicOpen 𝒜 x) V hV
        (Proj.awayToSection 𝒜 x (awayMap 𝒜 g_deg hx y)) := by
  have h : Proj.awayToSection 𝒜 f ≫ φ.appLE (Proj.basicOpen 𝒜 f) U hU ≫
      Y.presheaf.map (homOfLE hVU).op =
      CommRingCat.ofHom (awayMap 𝒜 g_deg hx) ≫ Proj.awayToSection 𝒜 x ≫
        φ.appLE (Proj.basicOpen 𝒜 x) V hV := by
    rw [Proj.awayMap_awayToSection_assoc, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  exact congrArg (fun ψ => ψ.hom y) h

end Restrict

section Algebra

variable (R : Type u) [CommRing R] {κ : Type}

/-- The cocycle identity `x_m/x_k = (x_i/x_k)(x_m/x_i)` in the chart ring of `D₊(xᵢxₖ)`. -/
theorem awayMap_chartRatio_mul (i k m : κ) :
    awayMap (homogeneousSubmodule κ R) (X_mem_homogeneousSubmodule_one R i)
        (mul_comm (X i) (X k)) (chartRatio R k m) =
      awayMap (homogeneousSubmodule κ R) (X_mem_homogeneousSubmodule_one R i)
          (mul_comm (X i) (X k)) (chartRatio R k i) *
        awayMap (homogeneousSubmodule κ R) (X_mem_homogeneousSubmodule_one R k) rfl
          (chartRatio R i m) := by
  apply HomogeneousLocalization.val_injective
  simp only [chartRatio, awayMap_mk, HomogeneousLocalization.val_mul, Away.val_mk,
    Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp; ring⟩

end Algebra

section Cocycle

variable {R : Type u} [CommRing R] {κ : Type}

/-- The cocycle identity for pulled-back coordinate ratios on an overlap of charts. -/
theorem appLE_chartRatio_cocycle {Y : Scheme.{u}}
    (φ : Y ⟶ Proj (homogeneousSubmodule κ R)) {i k : κ} {U U' V : Y.Opens}
    (hVU : V ≤ U) (hVU' : V ≤ U')
    (hU : U ≤ φ ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule κ R) (X i))
    (hU' : U' ≤ φ ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule κ R) (X k)) (m : κ) :
    Y.presheaf.map (homOfLE hVU').op
        (φ.appLE _ U' hU' (Proj.awayToSection _ (X k) (chartRatio R k m))) =
      Y.presheaf.map (homOfLE hVU').op
          (φ.appLE _ U' hU' (Proj.awayToSection _ (X k) (chartRatio R k i))) *
        Y.presheaf.map (homOfLE hVU).op
          (φ.appLE _ U hU (Proj.awayToSection _ (X i) (chartRatio R i m))) := by
  have hV : V ≤ φ ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule κ R) (X i * X k) := by
    rw [Proj.basicOpen_mul]
    exact le_inf (hVU.trans hU) (hVU'.trans hU')
  rw [appLE_awayToSection_restrict φ (X_mem_homogeneousSubmodule_one R i)
      (mul_comm (X i) (X k)) hVU' hU' hV,
    appLE_awayToSection_restrict φ (X_mem_homogeneousSubmodule_one R i)
      (mul_comm (X i) (X k)) hVU' hU' hV,
    appLE_awayToSection_restrict φ (X_mem_homogeneousSubmodule_one R k) rfl hVU hU hV,
    awayMap_chartRatio_mul, map_mul, map_mul]

end Cocycle

end Restrictions

end Hartshorne

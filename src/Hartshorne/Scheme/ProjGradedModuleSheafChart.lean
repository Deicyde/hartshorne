/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ProjGradedModuleSheaf
import Hartshorne.Projective.HomogeneousLocalizedModuleAway
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Hartshorne.Scheme.ProjPartialMap

/-!
# The sheaf of a graded module on a standard chart of Proj

Hartshorne, *Algebraic Geometry*, II.5, Proposition 5.11(b) (p. 117).

Let `S` be an `ℕ`-graded ring, `M` a `ℤ`-graded `S`-module and `f ∈ S_d` with `d > 0`. Under the
chart `Spec S_(f) ≅ D₊(f) ⊆ Proj S`, the restriction of `M~` to `D₊(f)` is the sheaf associated
to the `S_(f)`-module `M_(f)`.

## Main results

* `Hartshorne.ProjGradedModuleSheaf.awayι_mem_asIdeal_iff`: the point of `Proj S` corresponding
  to a prime `𝔮` of `S_(f)` is `{a | a / f^n ∈ 𝔮}` on homogeneous elements.
* `Hartshorne.ProjGradedModuleSheaf.awayι_appIso_inv_apply`: a function `r ∈ S_(f)`, viewed as a
  section of `𝒪_{Proj S}` through the chart, takes the value `r` in `S_(𝔭)` at every point `𝔭`.
-/

universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Hartshorne

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace HomogeneousLocalization

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

namespace ProjGradedModuleSheaf

section Chart

variable {f : A} {d : ℕ} (f_deg : f ∈ 𝒜 d) (hd : 0 < d)

@[deprecated basicOpenToSpec_toLRSHom (since := "2026-11-09")]
alias forget_basicOpenToSpec := basicOpenToSpec_toLRSHom

/-- **The point correspondence of the chart.** For a prime `𝔮` of `S_(f)` with image `𝔭` in
`Proj S`, a fraction `a / f^n` lies in `𝔮` exactly when `a ∈ 𝔭`. -/
theorem awayι_mem_asIdeal_iff (y : Spec (.of (Away 𝒜 f))) (z : NumDenSameDeg 𝒜 (.powers f)) :
    HomogeneousLocalization.mk z ∈ y.asIdeal ↔
      (z.num : A) ∈ ((Proj.awayι 𝒜 f f_deg hd).base y).asHomogeneousIdeal := by
  set x' := (Proj.basicOpenIsoSpec 𝒜 f f_deg hd).inv.base y
  have hy : (ProjectiveSpectrum.Proj.toSpec 𝒜 f).base x' = y := by
    rw [← basicOpenToSpec_toLRSHom]
    change (Proj.basicOpenIsoSpec 𝒜 f f_deg hd).hom.base x' = y
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl
  have h2 : (Proj.awayι 𝒜 f f_deg hd).base y = x'.1 := rfl
  rw [h2, ← ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply 𝒜 x' z, hy]

theorem awayι_image_top_le : (Proj.awayι 𝒜 f f_deg hd) ''ᵁ ⊤ ≤ Proj.basicOpen 𝒜 f := by
  rw [Scheme.Hom.image_top_eq_opensRange, Proj.opensRange_awayι]

theorem awayι_mem_basicOpen {x : Proj 𝒜} {U : (Spec (.of (Away 𝒜 f))).Opens}
    (hx : x ∈ (Proj.awayι 𝒜 f f_deg hd) ''ᵁ U) : f ∉ x.asHomogeneousIdeal :=
  awayι_image_top_le 𝒜 f_deg hd (Scheme.Hom.image_mono _ le_top hx)

theorem awayι_base_mem_basicOpen (y : Spec (.of (Away 𝒜 f))) :
    f ∉ ((Proj.awayι 𝒜 f f_deg hd).base y).asHomogeneousIdeal :=
  awayι_mem_basicOpen 𝒜 f_deg hd (U := ⊤) ⟨y, trivial, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- Through the chart, the global function `r ∈ S_(f)` on `Spec S_(f)` is the section
`awayToSection r` of `𝒪_{Proj S}` over `D₊(f)`. -/
theorem awayι_appIso_inv_top (r : Away 𝒜 f) :
    ((Proj.awayι 𝒜 f f_deg hd).appIso ⊤).inv ((Scheme.ΓSpecIso _).inv r) =
      (Proj 𝒜).presheaf.map (homOfLE (awayι_image_top_le 𝒜 f_deg hd)).op
        (Proj.awayToSection 𝒜 f r) := by
  set ι := Proj.awayι 𝒜 f f_deg hd
  set φ := Proj.basicOpenToSpec 𝒜 f
  have hφ : IsIso φ := inferInstanceAs (IsIso (Proj.basicOpenIsoSpec 𝒜 f f_deg hd).hom)
  have hφι : φ ≫ ι = (Proj.basicOpen 𝒜 f).ι := by
    simp only [φ, ι, ← Proj.basicOpenIsoSpec_inv_ι, ← Proj.basicOpenIsoSpec_hom 𝒜 f f_deg hd,
      Iso.hom_inv_id_assoc]
  suffices key : (ι.appIso ⊤).hom ((Proj 𝒜).presheaf.map
      (homOfLE (awayι_image_top_le 𝒜 f_deg hd)).op (Proj.awayToSection 𝒜 f r)) =
      (Scheme.ΓSpecIso _).inv r by
    rw [← key, Iso.hom_inv_id_apply]
  have E : (Proj 𝒜).presheaf.map (homOfLE (awayι_image_top_le 𝒜 f_deg hd)).op ≫
      (ι.appIso ⊤).hom ≫ φ.appTop = (Proj.basicOpen 𝒜 f).topIso.inv := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE,
      Scheme.Hom.appLE_comp_appLE]
    have hc : ∀ (g : (Proj.basicOpen 𝒜 f).toScheme ⟶ Proj 𝒜)
        (hg : g = (Proj.basicOpen 𝒜 f).ι) V e,
        g.appLE (ι ''ᵁ ⊤) V e = (Proj.basicOpen 𝒜 f).ι.appLE (ι ''ᵁ ⊤) V (hg ▸ e) := by
      rintro _ rfl _ _; rfl
    erw [hc _ hφι]
    simp only [Scheme.Hom.appLE, Scheme.Opens.ι_app, Scheme.Opens.topIso_inv]
    rfl
  apply (ConcreteCategory.bijective_of_isIso φ.appTop).1
  have h1 := Proj.basicOpenToSpec_app_top 𝒜 f
  have h2 := ConcreteCategory.congr_hom E (Proj.awayToSection 𝒜 f r)
  simp only [CommRingCat.comp_apply] at h2
  rw [h2, Scheme.Hom.appTop, h1]
  simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Values of functions through the chart.** For an open `U ⊆ Spec S_(f)` and `r ∈ S_(f)`, the
section of `𝒪_{Proj S}` over the image of `U` corresponding to `r|_U` takes the value `r ∈ S_(𝔭)`
at each point `𝔭`. -/
theorem awayι_appIso_inv_apply (U : (Spec (.of (Away 𝒜 f))).Opens) (r : Away 𝒜 f) (x : Proj 𝒜)
    (hx : x ∈ (Proj.awayι 𝒜 f f_deg hd) ''ᵁ U) :
    (show (ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.obj
        (op ((Proj.awayι 𝒜 f f_deg hd) ''ᵁ U)) from
      ((Proj.awayι 𝒜 f f_deg hd).appIso U).inv
        ((Spec (.of (Away 𝒜 f))).presheaf.map U.leTop.op ((Scheme.ΓSpecIso _).inv r))).1
        ⟨x, hx⟩ =
      mapId 𝒜 (Submonoid.powers_le.mpr (show f ∈ x.asHomogeneousIdeal.toIdeal.primeCompl from
        awayι_mem_basicOpen 𝒜 f_deg hd hx)) r := by
  have := Scheme.Hom.appIso_inv_naturality (Proj.awayι 𝒜 f f_deg hd) U.leTop.op
  have h := ConcreteCategory.congr_hom this ((Scheme.ΓSpecIso _).inv r)
  simp only [CommRingCat.comp_apply] at h
  erw [h, awayι_appIso_inv_top]
  rfl

end Chart

section Module

variable {M σM : Type u} [AddCommGroup M] [Module A M] [SetLike σM M] [AddSubgroupClass σM M]
  (ℳ : ℤ → σM) [SetLike.GradedSMul 𝒜 ℳ]
  {f : A} {d : ℕ} (f_deg : f ∈ 𝒜 d) (hd : 0 < d)

local notation3 "Mat " x =>
  HomogeneousLocalizedModule 𝒜 ℳ
    (HomogeneousIdeal.toIdeal (ProjectiveSpectrum.asHomogeneousIdeal x)).primeCompl

/-- The restriction of `M~` to the chart `Spec S_(f) ≅ D₊(f)`. -/
abbrev chartModule : (Spec (.of (Away 𝒜 f))).Modules :=
  (projGradedModuleSheaf 𝒜 ℳ).restrict (Proj.awayι 𝒜 f f_deg hd)

/-- The sections of the restriction of `M~` to the chart over `U`, as an `S_(f)`-module. -/
abbrev chartSections (U : (Spec (.of (Away 𝒜 f))).Opens) :
    ModuleCat (CommRingCat.of (Away 𝒜 f)) :=
  (modulesSpecToSheaf.obj (chartModule 𝒜 ℳ f_deg hd)).presheaf.obj (op U)

variable {𝒜 ℳ f_deg hd} in
/-- The value of a section of the restriction of `M~` to the chart at a point of `Proj S`. -/
def chartEval {U : (Spec (.of (Away 𝒜 f))).Opens} (s : chartSections 𝒜 ℳ f_deg hd U) (x : Proj 𝒜)
    (hx : x ∈ (Proj.awayι 𝒜 f f_deg hd) ''ᵁ U) : Mat x :=
  (show (sheafInType 𝒜 ℳ).1.obj (op ((Proj.awayι 𝒜 f f_deg hd) ''ᵁ U)) from s).1 ⟨x, hx⟩

variable {𝒜 ℳ f_deg hd} in
theorem chartSections_ext {U : (Spec (.of (Away 𝒜 f))).Opens}
    {s t : chartSections 𝒜 ℳ f_deg hd U} (h : ∀ x hx, chartEval s x hx = chartEval t x hx) :
    s = t :=
  Subtype.ext (funext fun x => h x.1 x.2)

theorem powers_le_of_mem {U : (Spec (.of (Away 𝒜 f))).Opens} {x : Proj 𝒜}
    (hx : x ∈ (Proj.awayι 𝒜 f f_deg hd) ''ᵁ U) :
    Submonoid.powers f ≤ x.asHomogeneousIdeal.toIdeal.primeCompl :=
  Submonoid.powers_le.mpr (show f ∈ x.asHomogeneousIdeal.toIdeal.primeCompl from
    awayι_mem_basicOpen 𝒜 f_deg hd hx)

set_option backward.isDefEq.respectTransparency false in
variable {𝒜 ℳ f_deg hd} in
/-- `S_(f)` acts on the sections of the restriction of `M~` to the chart pointwise, through
`S_(f) → S_(𝔭)`. -/
theorem chartEval_smul {U : (Spec (.of (Away 𝒜 f))).Opens} (r : Away 𝒜 f)
    (s : chartSections 𝒜 ℳ f_deg hd U) (x : Proj 𝒜) (hx : x ∈ (Proj.awayι 𝒜 f f_deg hd) ''ᵁ U) :
    chartEval (r • s) x hx = mapId 𝒜 (powers_le_of_mem 𝒜 f_deg hd hx) r • chartEval s x hx := by
  rw [← awayι_appIso_inv_apply 𝒜 f_deg hd U r x hx]
  rfl

/-- The section `x ↦ m` of `M~` over the chart, for `m ∈ M_(f)`. -/
def toChartSection (m : HomogeneousLocalizedModule 𝒜 ℳ (Submonoid.powers f)) :
    chartSections 𝒜 ℳ f_deg hd ⊤ :=
  (⟨fun x => HomogeneousLocalizedModule.mapOfLE 𝒜 ℳ (powers_le_of_mem 𝒜 f_deg hd x.2) m,
    fun x => by
      obtain ⟨n, m', hm', s, hs, ⟨k, hk⟩, rfl⟩ := HomogeneousLocalizedModule.mk_surjective m
      refine ⟨_, x.2, 𝟙 _, n, m', hm', s, hs, fun y => ?_, fun y => ?_⟩
      · rw [← hk]
        exact fun hmem => awayι_mem_basicOpen 𝒜 f_deg hd y.2
          (Ideal.IsPrime.mem_of_pow_mem inferInstance k hmem)
      · exact HomogeneousLocalizedModule.mapOfLE_mk _ _ _ _ _ _ _⟩ :
    (sheafInType 𝒜 ℳ).1.obj (op ((Proj.awayι 𝒜 f f_deg hd) ''ᵁ ⊤)))

@[simp]
theorem chartEval_toChartSection (m : HomogeneousLocalizedModule 𝒜 ℳ (Submonoid.powers f))
    (x : Proj 𝒜) (hx : x ∈ (Proj.awayι 𝒜 f f_deg hd) ''ᵁ ⊤) :
    chartEval (toChartSection 𝒜 ℳ f_deg hd m) x hx =
      HomogeneousLocalizedModule.mapOfLE 𝒜 ℳ (powers_le_of_mem 𝒜 f_deg hd hx) m :=
  rfl

/-- The `S_(f)`-linear map `M_(f) → Γ(Spec S_(f), M~|_{D₊(f)})`, `m ↦ (x ↦ m)`. -/
def toChartΓLinear : HomogeneousLocalizedModule 𝒜 ℳ (Submonoid.powers f) →ₗ[Away 𝒜 f]
    chartSections 𝒜 ℳ f_deg hd ⊤ where
  toFun := toChartSection 𝒜 ℳ f_deg hd
  map_add' m m' := chartSections_ext fun x hx => by
    change _ = chartEval (toChartSection 𝒜 ℳ f_deg hd m) x hx +
      chartEval (toChartSection 𝒜 ℳ f_deg hd m') x hx
    simp only [chartEval_toChartSection, map_add]
  map_smul' c m := chartSections_ext fun x hx => by
    rw [RingHom.id_apply, chartEval_smul, chartEval_toChartSection,
      chartEval_toChartSection, HomogeneousLocalizedModule.mapOfLE_smul]

/-- `toChartΓLinear` as a morphism of `S_(f)`-modules. -/
def toChartΓ : ModuleCat.of (Away 𝒜 f) (HomogeneousLocalizedModule 𝒜 ℳ (Submonoid.powers f)) ⟶
    chartSections 𝒜 ℳ f_deg hd ⊤ :=
  ModuleCat.ofHom (Y := chartSections 𝒜 ℳ f_deg hd ⊤) (toChartΓLinear 𝒜 ℳ f_deg hd)

@[simp]
theorem toChartΓ_apply (m : HomogeneousLocalizedModule 𝒜 ℳ (Submonoid.powers f)) :
    toChartΓ 𝒜 ℳ f_deg hd m = toChartSection 𝒜 ℳ f_deg hd m :=
  rfl

variable {𝒜 ℳ f_deg hd} in
theorem mem_image_of_mem {U : (Spec (.of (Away 𝒜 f))).Opens} {y : Spec (.of (Away 𝒜 f))}
    (hy : y ∈ U) : (Proj.awayι 𝒜 f f_deg hd).base y ∈ (Proj.awayι 𝒜 f f_deg hd) ''ᵁ U :=
  ⟨y, hy, rfl⟩

/-- Evaluation on the stalks of the restriction of `M~` to the chart: the stalk at `y` maps to
`M_(𝔭)`, where `𝔭` is the image of `y` in `Proj S`. -/
def chartStalkEval (y : Spec (.of (Away 𝒜 f))) :
    (chartModule 𝒜 ℳ f_deg hd).presheaf.stalk y ⟶
      AddCommGrpCat.of (Mat ((Proj.awayι 𝒜 f f_deg hd).base y)) :=
  (Scheme.Modules.restrictStalkNatIso (Proj.awayι 𝒜 f f_deg hd) y).hom.app
    (projGradedModuleSheaf 𝒜 ℳ) ≫ stalkToFiber 𝒜 ℳ _

theorem chartStalkEval_germ (y : Spec (.of (Away 𝒜 f))) (U : (Spec (.of (Away 𝒜 f))).Opens)
    (hy : y ∈ U) (s : chartSections 𝒜 ℳ f_deg hd U) :
    chartStalkEval 𝒜 ℳ f_deg hd y ((chartModule 𝒜 ℳ f_deg hd).presheaf.germ U y hy s) =
      chartEval s _ (mem_image_of_mem hy) := by
  have h := ConcreteCategory.congr_hom (Scheme.Modules.germ_restrictStalkNatIso_hom_app
    (Proj.awayι 𝒜 f f_deg hd) y (projGradedModuleSheaf 𝒜 ℳ) hy) s
  rw [ConcreteCategory.comp_apply] at h
  rw [chartStalkEval, ConcreteCategory.comp_apply, h]
  exact stalkToFiber_germ 𝒜 ℳ _ _ _ s

theorem chartStalkEval_bijective (y : Spec (.of (Away 𝒜 f))) :
    Function.Bijective (chartStalkEval 𝒜 ℳ f_deg hd y) := by
  rw [chartStalkEval]
  change Function.Bijective (fun z => stalkToFiber 𝒜 ℳ _
    ((Scheme.Modules.restrictStalkNatIso (Proj.awayι 𝒜 f f_deg hd) y).hom.app
      (projGradedModuleSheaf 𝒜 ℳ) z))
  exact Function.Bijective.comp
    ⟨stalkToFiber_injective 𝒜 ℳ _, stalkToFiber_surjective 𝒜 ℳ _⟩
    (ConcreteCategory.bijective_of_isIso _)

variable {𝒜 ℳ f_deg hd} in
theorem chartEval_res {U V : (Spec (.of (Away 𝒜 f))).Opens} (i : V ⟶ U)
    (s : chartSections 𝒜 ℳ f_deg hd U) (x : Proj 𝒜)
    (hx : x ∈ (Proj.awayι 𝒜 f f_deg hd) ''ᵁ V) :
    chartEval ((modulesSpecToSheaf.obj (chartModule 𝒜 ℳ f_deg hd)).presheaf.map i.op s) x hx =
      chartEval s x (Scheme.Hom.image_mono _ i.le hx) :=
  rfl

variable (f) in
/-- `M_(f)` as a module over the ring `S_(f)`, bundled. -/
abbrev awayModule : ModuleCat (CommRingCat.of (Away 𝒜 f)) :=
  ModuleCat.of (Away 𝒜 f) (HomogeneousLocalizedModule 𝒜 ℳ (Submonoid.powers f))

/-- The morphism `(M_(f))~ → M~|_{D₊(f)}` corresponding to `toChartΓ` under the adjunction
between `~` and global sections. -/
def fromTildeChart : tilde (awayModule 𝒜 ℳ f) ⟶ chartModule 𝒜 ℳ f_deg hd :=
  tilde.map (toChartΓ 𝒜 ℳ f_deg hd) ≫
    Scheme.Modules.fromTildeΓ (R := CommRingCat.of (Away 𝒜 f)) (chartModule 𝒜 ℳ f_deg hd)

theorem fromTildeChart_app_toOpen (U : (Spec (.of (Away 𝒜 f))).Opens)
    (m : HomogeneousLocalizedModule 𝒜 ℳ (Submonoid.powers f)) :
    (modulesSpecToSheaf.map (fromTildeChart 𝒜 ℳ f_deg hd)).1.app (op U)
        (tilde.toOpen (awayModule 𝒜 ℳ f) U m) =
      (modulesSpecToSheaf.obj (chartModule 𝒜 ℳ f_deg hd)).presheaf.map (homOfLE le_top).op
        (toChartΓ 𝒜 ℳ f_deg hd m) := by
  have h1 := ConcreteCategory.congr_hom (tilde.toOpen_map_app (toChartΓ 𝒜 ℳ f_deg hd) U) m
  have h2 := ConcreteCategory.congr_hom
    (Scheme.Modules.toOpen_fromTildeΓ_app (R := CommRingCat.of (Away 𝒜 f))
      (chartModule 𝒜 ℳ f_deg hd) U) (toChartΓ 𝒜 ℳ f_deg hd m)
  simp only [ConcreteCategory.comp_apply] at h1 h2
  rw [fromTildeChart, Functor.map_comp]
  change (modulesSpecToSheaf.map (Scheme.Modules.fromTildeΓ (R := CommRingCat.of (Away 𝒜 f))
    (chartModule 𝒜 ℳ f_deg hd))).1.app (op U) ((modulesSpecToSheaf.map
      (tilde.map (toChartΓ 𝒜 ℳ f_deg hd))).1.app (op U) (tilde.toOpen _ U m)) = _
  rw [h1, h2]

/-- Mathlib's `S_(f)`-module structure on the stalks of `(M_(f))~` (the instance is keyed on
`CommRingCat` and is not found automatically for `CommRingCat.of (Away 𝒜 f)`). -/
noncomputable instance tildeStalkModule (y : Spec (.of (Away 𝒜 f))) :
    Module (Away 𝒜 f) ((tilde (awayModule 𝒜 ℳ f)).presheaf.stalk y) :=
  tilde.instModuleCarrierCarrierStalkAbPresheaf (R := CommRingCat.of (Away 𝒜 f)) _ y

set_option backward.isDefEq.respectTransparency false in
theorem tilde_germ_smul (y : Spec (.of (Away 𝒜 f))) (U : (Spec (.of (Away 𝒜 f))).Opens)
    (hy : y ∈ U) (r : Away 𝒜 f)
    (t : (modulesSpecToSheaf.obj (tilde (awayModule 𝒜 ℳ f))).presheaf.obj (op U)) :
    (tilde (awayModule 𝒜 ℳ f)).presheaf.germ U y hy (r • t) =
      r • (tilde (awayModule 𝒜 ℳ f)).presheaf.germ U y hy t := by
  have h := PresheafOfModules.germ_smul
    (moduleStructurePresheaf (CommRingCat.of (Away 𝒜 f)) (awayModule 𝒜 ℳ f)) y U hy
    ((Spec (.of (Away 𝒜 f))).presheaf.map U.leTop.op ((Scheme.ΓSpecIso _).inv r)) t
  refine h.trans ?_
  have h2 : (structurePresheafInCommRingCat (CommRingCat.of (Away 𝒜 f))).germ U y hy
      ((Spec (.of (Away 𝒜 f))).presheaf.map U.leTop.op ((Scheme.ΓSpecIso _).inv r)) =
        StructureSheaf.toStalk _ y r :=
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  rw [h2]
  rfl

/-- The stalk map of `fromTildeChart` at `y`, followed by `chartStalkEval`. -/
def chartStalkMap (y : Spec (.of (Away 𝒜 f))) :
    (tilde (awayModule 𝒜 ℳ f)).presheaf.stalk y ⟶
      AddCommGrpCat.of (Mat ((Proj.awayι 𝒜 f f_deg hd).base y)) :=
  (TopCat.Presheaf.stalkFunctor Ab y).map
    ((Scheme.Modules.toPresheaf _).map (fromTildeChart 𝒜 ℳ f_deg hd)) ≫
      chartStalkEval 𝒜 ℳ f_deg hd y

theorem chartStalkMap_germ (y : Spec (.of (Away 𝒜 f))) (U : (Spec (.of (Away 𝒜 f))).Opens)
    (hy : y ∈ U) (t : (modulesSpecToSheaf.obj (tilde (awayModule 𝒜 ℳ f))).presheaf.obj (op U)) :
    chartStalkMap 𝒜 ℳ f_deg hd y ((tilde (awayModule 𝒜 ℳ f)).presheaf.germ U y hy t) =
      chartEval ((modulesSpecToSheaf.map (fromTildeChart 𝒜 ℳ f_deg hd)).1.app (op U) t) _
        (mem_image_of_mem hy) := by
  rw [chartStalkMap, ConcreteCategory.comp_apply]
  have h := TopCat.Presheaf.stalkFunctor_map_germ_apply U y hy
    ((Scheme.Modules.toPresheaf _).map (fromTildeChart 𝒜 ℳ f_deg hd)) t
  exact (congrArg (fun z => chartStalkEval 𝒜 ℳ f_deg hd y z) h).trans
    (chartStalkEval_germ 𝒜 ℳ f_deg hd y U hy _)

theorem chartStalkMap_toStalk (y : Spec (.of (Away 𝒜 f)))
    (m : HomogeneousLocalizedModule 𝒜 ℳ (Submonoid.powers f)) :
    chartStalkMap 𝒜 ℳ f_deg hd y (tilde.toStalk (awayModule 𝒜 ℳ f) y m) =
      HomogeneousLocalizedModule.mapOfLE 𝒜 ℳ
        (powers_le_of_mem 𝒜 f_deg hd (mem_image_of_mem (U := ⊤) (y := y) trivial)) m := by
  change chartStalkMap 𝒜 ℳ f_deg hd y ((tilde (awayModule 𝒜 ℳ f)).presheaf.germ ⊤ y trivial
    (tilde.toOpen (awayModule 𝒜 ℳ f) ⊤ m)) = _
  rw [chartStalkMap_germ, fromTildeChart_app_toOpen, chartEval_res, toChartΓ_apply,
    chartEval_toChartSection]

theorem chartStalkMap_smul (y : Spec (.of (Away 𝒜 f))) (r : Away 𝒜 f)
    (z : (tilde (awayModule 𝒜 ℳ f)).presheaf.stalk y) :
    chartStalkMap 𝒜 ℳ f_deg hd y (r • z) =
      mapId 𝒜 (powers_le_of_mem 𝒜 f_deg hd (mem_image_of_mem (U := ⊤) (y := y) trivial)) r •
        chartStalkMap 𝒜 ℳ f_deg hd y z := by
  obtain ⟨U, hy, t, rfl⟩ := (tilde (awayModule 𝒜 ℳ f)).presheaf.exists_germ_eq z
  rw [← tilde_germ_smul, chartStalkMap_germ, chartStalkMap_germ, map_smul, chartEval_smul]

variable [DirectSum.Decomposition ℳ]

/-- On stalks, `fromTildeChart` followed by evaluation is the localization map
`(M_(f))_𝔮 → M_(𝔭)`, hence bijective. -/
theorem chartStalkMap_bijective (y : Spec (.of (Away 𝒜 f))) :
    Function.Bijective (chartStalkMap 𝒜 ℳ f_deg hd y) := by
  set x := (Proj.awayι 𝒜 f f_deg hd).base y
  have hx : x ∈ (Proj.awayι 𝒜 f f_deg hd) ''ᵁ ⊤ := mem_image_of_mem (U := ⊤) (y := y) trivial
  set h := powers_le_of_mem 𝒜 f_deg hd hx
  let _ := HomogeneousLocalizedModule.moduleOfLE 𝒜 ℳ h
  have _ : IsLocalizedModule y.asIdeal.primeCompl (tilde.toStalk (awayModule 𝒜 ℳ f) y).hom :=
    tilde.instIsLocalizedModuleCarrierCarrierOfCarrierStalkAbPresheafPrimeComplAsIdealHomToStalk
      (R := CommRingCat.of (Away 𝒜 f)) _ y
  let L : (tilde (awayModule 𝒜 ℳ f)).presheaf.stalk y →ₗ[Away 𝒜 f] Mat x :=
    { toFun := chartStalkMap 𝒜 ℳ f_deg hd y
      map_add' := map_add _
      map_smul' := chartStalkMap_smul 𝒜 ℳ f_deg hd y }
  have hcomp : L ∘ₗ (tilde.toStalk (awayModule 𝒜 ℳ f) y).hom =
      HomogeneousLocalizedModule.mapOfLELinear 𝒜 ℳ h :=
    LinearMap.ext (chartStalkMap_toStalk 𝒜 ℳ f_deg hd y)
  have hQ (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • d)) :
      Away.mk 𝒜 f_deg n a ha ∈ y.asIdeal.primeCompl ↔ a ∉ x.asHomogeneousIdeal.toIdeal :=
    (awayι_mem_asIdeal_iff 𝒜 f_deg hd y _).not
  have hloc := HomogeneousLocalizedModule.isLocalizedModule_mapOfLE (ℳ := ℳ) f_deg hd
    x.asHomogeneousIdeal.toIdeal x.asHomogeneousIdeal.isHomogeneous
    (awayι_base_mem_basicOpen 𝒜 f_deg hd y) y.asIdeal.primeCompl hQ
  have : IsLocalizedModule y.asIdeal.primeCompl
      (L ∘ₗ (tilde.toStalk (awayModule 𝒜 ℳ f) y).hom) := hcomp ▸ hloc
  have hL := IsLocalizedModule.linearEquiv_of_isLocalizedModule_comp y.asIdeal.primeCompl
    (tilde.toStalk (awayModule 𝒜 ℳ f) y).hom L
  have hb := (IsLocalizedModule.linearEquiv y.asIdeal.primeCompl
    (tilde.toStalk (awayModule 𝒜 ℳ f) y).hom
    (L ∘ₗ (tilde.toStalk (awayModule 𝒜 ℳ f) y).hom)).bijective
  have hb' : Function.Bijective L := by
    rw [← hL]
    exact hb
  exact hb'

/-- **The chart isomorphism**, as an instance: `(M_(f))~ → M~|_{D₊(f)}` is an isomorphism. -/
instance isIso_fromTildeChart : IsIso (fromTildeChart 𝒜 ℳ f_deg hd) := by
  let F₁ : TopCat.Sheaf Ab (Spec (.of (Away 𝒜 f))) :=
    ⟨(Scheme.Modules.toPresheaf _).obj (tilde (awayModule 𝒜 ℳ f)),
      (tilde (awayModule 𝒜 ℳ f)).isSheaf⟩
  let G₁ : TopCat.Sheaf Ab (Spec (.of (Away 𝒜 f))) :=
    ⟨(Scheme.Modules.toPresheaf _).obj (chartModule 𝒜 ℳ f_deg hd),
      (chartModule 𝒜 ℳ f_deg hd).isSheaf⟩
  let g : F₁ ⟶ G₁ := ⟨(Scheme.Modules.toPresheaf _).map (fromTildeChart 𝒜 ℳ f_deg hd)⟩
  have hstalk (y : Spec (.of (Away 𝒜 f))) :
      IsIso ((TopCat.Presheaf.stalkFunctor Ab y).map g.1) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    have hb := chartStalkMap_bijective 𝒜 ℳ f_deg hd y
    rw [chartStalkMap] at hb
    exact (Function.Bijective.of_comp_iff' (chartStalkEval_bijective 𝒜 ℳ f_deg hd y) _).1 hb
  have : IsIso g := TopCat.Presheaf.isIso_of_stalkFunctor_map_iso g
  have : IsIso ((Scheme.Modules.toPresheaf _).map (fromTildeChart 𝒜 ℳ f_deg hd)) :=
    (TopCat.Sheaf.forget Ab (Spec (.of (Away 𝒜 f)))).map_isIso g
  exact isIso_of_reflects_iso _ (Scheme.Modules.toPresheaf _)

/-- **Hartshorne II.5.11(b), the chart isomorphism.** For `f ∈ S_d` with `d > 0`, under the
chart `Spec S_(f) ≅ D₊(f)` the restriction of `M~` is the sheaf associated to the
`S_(f)`-module `M_(f)`: `M~|_{D₊(f)} ≅ (M_(f))~`. -/
def chartIso :
    (Scheme.Modules.restrictFunctor (Proj.awayι 𝒜 f f_deg hd)).obj (projGradedModuleSheaf 𝒜 ℳ) ≅
      tilde (awayModule 𝒜 ℳ f) :=
  (asIso (fromTildeChart 𝒜 ℳ f_deg hd)).symm

end Module

end ProjGradedModuleSheaf

end Hartshorne

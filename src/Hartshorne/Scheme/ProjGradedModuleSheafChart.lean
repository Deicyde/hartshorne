/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ProjGradedModuleSheaf
import Hartshorne.Projective.HomogeneousLocalizedModuleAway
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

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

set_option backward.isDefEq.respectTransparency false in
/-- Mathlib's two descriptions of the chart map `D₊(f) → Spec S_(f)` agree as morphisms of
locally ringed spaces. -/
theorem forget_basicOpenToSpec (f : A) :
    Scheme.forgetToLocallyRingedSpace.map (Proj.basicOpenToSpec 𝒜 f) =
      ProjectiveSpectrum.Proj.toSpec 𝒜 f := by
  refine Eq.trans ?_ (ΓSpec.locallyRingedSpaceAdjunction.homEquiv_apply _ _ _).symm
  dsimp [Proj.basicOpenToSpec, Scheme.Opens.toSpecΓ]
  simp only [Category.assoc, ← Spec.map_comp]
  rfl

/-- **The point correspondence of the chart.** For a prime `𝔮` of `S_(f)` with image `𝔭` in
`Proj S`, a fraction `a / f^n` lies in `𝔮` exactly when `a ∈ 𝔭`. -/
theorem awayι_mem_asIdeal_iff (y : Spec (.of (Away 𝒜 f))) (z : NumDenSameDeg 𝒜 (.powers f)) :
    HomogeneousLocalization.mk z ∈ y.asIdeal ↔
      (z.num : A) ∈ ((Proj.awayι 𝒜 f f_deg hd).base y).asHomogeneousIdeal := by
  set x' := (Proj.basicOpenIsoSpec 𝒜 f f_deg hd).inv.base y
  have hy : (ProjectiveSpectrum.Proj.toSpec 𝒜 f).base x' = y := by
    rw [← forget_basicOpenToSpec]
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

end Module

end ProjGradedModuleSheaf

end Hartshorne

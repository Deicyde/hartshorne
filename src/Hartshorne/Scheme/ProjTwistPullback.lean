/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ProjPartialMap
import Hartshorne.Scheme.ProjTwistLocalization
import Hartshorne.Scheme.ProjTwistCompatibility
import Hartshorne.RingedSpace.FiniteLocallyFreeProjectionFormula

/-!
# Pullback of twisting sheaves along the partial Proj morphism
-/

universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Hartshorne

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace HomogeneousLocalization

namespace ProjTwistPullback

section Chart

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜]

theorem top_le_awayι_preimage {b : A} {i : ℕ} (hb : b ∈ 𝒜 i) (hi : 0 < i) :
    (⊤ : (Spec (.of (Away 𝒜 b))).Opens) ≤ Proj.awayι 𝒜 b hb hi ⁻¹ᵁ Proj.basicOpen 𝒜 b := by
  intro y _
  exact ProjGradedModuleSheaf.awayι_base_mem_basicOpen 𝒜 hb hi y

set_option backward.isDefEq.respectTransparency false in
/-- Through the chart `Spec S_(b) ⟶ Proj S`, the section `awayToSection x` of `𝒪_{Proj S}` over
`D₊(b)` pulls back to the global function `x`. -/
theorem awayι_appLE_awayToSection {b : A} {i : ℕ} (hb : b ∈ 𝒜 i) (hi : 0 < i) (x : Away 𝒜 b) :
    (Proj.awayι 𝒜 b hb hi).appLE (Proj.basicOpen 𝒜 b) ⊤ (top_le_awayι_preimage hb hi)
        (Proj.awayToSection 𝒜 b x) = (Scheme.ΓSpecIso _).inv x := by
  have h := ProjGradedModuleSheaf.awayι_appIso_inv_top 𝒜 hb hi x
  rw [← Scheme.Hom.map_appLE (Proj.awayι 𝒜 b hb hi) _
    (homOfLE (ProjGradedModuleSheaf.awayι_image_top_le 𝒜 hb hi)).op]
  erw [CommRingCat.comp_apply, ← h, ← Scheme.Hom.appIso_hom']
  · exact Iso.inv_hom_id_apply _ _
  · exact (Scheme.Hom.preimage_image_eq _ _).ge

end Chart

section PartialChart

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] (f : 𝒜 →+*ᵍ ℬ)

theorem appLE_top_top {X Y : Scheme.{u}} (g : X ⟶ Y) (e : (⊤ : X.Opens) ≤ g ⁻¹ᵁ ⊤) :
    g.appLE ⊤ ⊤ e = g.appTop := by
  rw [Scheme.Hom.appLE, Scheme.Hom.appTop]
  have : (homOfLE e).op = 𝟙 (op (⊤ : X.Opens)) := Subsingleton.elim _ _
  erw [this, X.presheaf.map_id, Category.comp_id]

theorem top_le_chart_preimage {b : A} {i : ℕ} (hb : b ∈ 𝒜 i) (hi : 0 < i) :
    (⊤ : (Proj.basicOpen ℬ (f b)).toScheme.Opens) ≤
      ((Proj ℬ).homOfLE (basicOpen_le_projPartialDomain f hi hb) ≫ projPartialMap f) ⁻¹ᵁ
        Proj.basicOpen 𝒜 b := by
  intro y _
  change projPartialMap f ((Proj ℬ).homOfLE (basicOpen_le_projPartialDomain f hi hb) y) ∈
    Proj.basicOpen 𝒜 b
  rw [Proj.mem_basicOpen, projPartialMap_apply]
  have hy : (projPartialDomain f).ι ((Proj ℬ).homOfLE (basicOpen_le_projPartialDomain f hi hb) y)
      = y.1 := by
    rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
    rfl
  change f b ∉ ((projPartialDomain f).ι _).asHomogeneousIdeal
  rw [hy]
  exact y.2

set_option backward.isDefEq.respectTransparency false in
/-- **The partial morphism on sections of a chart.** On `D₊(φ(b)) ⊆ U`, the partial morphism
sends the section `x ∈ S_(b)` of `𝒪_{Proj S}` over `D₊(b)` to the section `φ(x) ∈ T_(φ(b))`. -/
theorem projPartialMap_appLE_awayToSection {b : A} {i : ℕ} (hb : b ∈ 𝒜 i) (hi : 0 < i)
    (x : Away 𝒜 b) :
    ((Proj ℬ).homOfLE (basicOpen_le_projPartialDomain f hi hb) ≫ projPartialMap f).appLE
        (Proj.basicOpen 𝒜 b) ⊤ (top_le_chart_preimage f hb hi) (Proj.awayToSection 𝒜 b x) =
      (Proj.basicOpen ℬ (f b)).topIso.inv
        (Proj.awayToSection ℬ (f b) (Away.map f b x)) := by
  have key : ∀ (g : (Proj.basicOpen ℬ (f b)).toScheme ⟶ Proj 𝒜)
      (hg : g = (Proj.basicOpenIsoSpec ℬ (f b) (f.map_mem hb) hi).hom ≫
        Spec.map (CommRingCat.ofHom (Away.map f b)) ≫ Proj.awayι 𝒜 b hb hi) e,
      g.appLE (Proj.basicOpen 𝒜 b) ⊤ e (Proj.awayToSection 𝒜 b x) =
        (Proj.basicOpen ℬ (f b)).topIso.inv
          (Proj.awayToSection ℬ (f b) (Away.map f b x)) := by
    rintro g rfl e
    rw [← Scheme.Hom.appLE_comp_appLE _ _ _ ⊤ _ (by
      intro y _
      exact ProjGradedModuleSheaf.awayι_base_mem_basicOpen 𝒜 hb hi _) le_top]
    rw [← Scheme.Hom.appLE_comp_appLE _ _ _ ⊤ _ (top_le_awayι_preimage hb hi) le_top]
    simp only [CommRingCat.comp_apply]
    rw [awayι_appLE_awayToSection, appLE_top_top, appLE_top_top]
    have h1 : (Spec.map (CommRingCat.ofHom (Away.map f b))).appTop
        ((Scheme.ΓSpecIso _).inv x) = (Scheme.ΓSpecIso _).inv (Away.map f b x) :=
      (ConcreteCategory.congr_hom
        (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Away.map f b))) x).symm
    rw [h1, Scheme.Hom.appTop, Proj.basicOpenIsoSpec_hom, Proj.basicOpenToSpec_app_top]
    simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply]
    rfl
  exact key _ (homOfLE_projPartialMap f hb hi) _

theorem primeCompl_le_comap_projPartialMap (y : (projPartialDomain f).toScheme) :
    (projPartialMap f y).asHomogeneousIdeal.toIdeal.primeCompl ≤
      ((projPartialDomain f).ι y).asHomogeneousIdeal.toIdeal.primeCompl.comap f := by
  intro a ha h
  apply ha
  change a ∈ (projPartialMap f y).asHomogeneousIdeal
  rw [projPartialMap_apply_asHomogeneousIdeal]
  exact h

theorem exists_basicOpen_of_mem (y : (projPartialDomain f).toScheme) :
    ∃ (k : ℕ) (c : A), 0 < k ∧ c ∈ 𝒜 k ∧ f c ∉ ((projPartialDomain f).ι y).asHomogeneousIdeal := by
  have h : (projPartialDomain f).ι y ∈ ⨆ r : ProjPartialIndex 𝒜, Proj.basicOpen ℬ (f r.2.1) :=
    projPartialDomain_eq_iSup f ▸ y.2
  rw [Opens.mem_iSup] at h
  obtain ⟨⟨k, c, hk, hc⟩, hyc⟩ := h
  exact ⟨k, c, hk, hc, hyc⟩

/-- Evaluation of a section of the structure sheaf of `Proj ℬ` at a point. -/
abbrev sectionValue {V : (Proj ℬ).Opens} (t : Γ(Proj ℬ, V)) (z : Proj ℬ) (hz : z ∈ V) :
    AtPrime ℬ z.asHomogeneousIdeal.toIdeal :=
  (show (ProjectiveSpectrum.Proj.structureSheaf ℬ).1.obj (op V) from t).1 ⟨z, hz⟩

set_option backward.isDefEq.respectTransparency false in
/-- **The partial morphism on sections, pointwise.** For a section `r` of `𝒪_{Proj S}` over `V`
and `y ∈ U` with `φ⁻¹(y) ∈ V`, the section `f^♯ r` of `𝒪_U` takes at `y` the value
`φ(r(φ⁻¹ y)) ∈ T_(y)`. -/
theorem projPartialMap_app_apply (V : (Proj 𝒜).Opens) (r : Γ(Proj 𝒜, V))
    (y : (projPartialDomain f).toScheme) (hy : y ∈ projPartialMap f ⁻¹ᵁ V) :
    sectionValue (V := (projPartialDomain f).ι ''ᵁ (projPartialMap f ⁻¹ᵁ V))
        ((projPartialMap f).app V r) ((projPartialDomain f).ι y) ⟨y, hy, rfl⟩ =
      HomogeneousLocalization.map f (primeCompl_le_comap_projPartialMap f y)
        (sectionValue r (projPartialMap f y) hy) := by
  obtain ⟨W, hW, iWV, j, ⟨a, ha⟩, ⟨b, hb⟩, hbW, hr⟩ :=
    (show (ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.obj (op V) from r).2 ⟨projPartialMap f y, hy⟩
  obtain ⟨k, c, hk, hc, hyc⟩ := exists_basicOpen_of_mem f y
  have hcy : c ∉ (projPartialMap f y).asHomogeneousIdeal := by
    rw [projPartialMap_apply_asHomogeneousIdeal]
    exact hyc
  have hby : b ∉ (projPartialMap f y).asHomogeneousIdeal := hbW ⟨_, hW⟩
  have hd : b * c ∈ 𝒜 (j + k) := SetLike.GradedMul.mul_mem hb hc
  have hdk : 0 < j + k := by omega
  have hdy : projPartialMap f y ∈ Proj.basicOpen 𝒜 (b * c) := fun h =>
    ((projPartialMap f y).isPrime.mem_or_mem h).elim hby hcy
  let x : Away 𝒜 (b * c) := HomogeneousLocalization.mk
    ⟨j + k, ⟨a * c, SetLike.GradedMul.mul_mem ha hc⟩, ⟨b * c, hd⟩, ⟨1, pow_one _⟩⟩
  set W' := W ⊓ Proj.basicOpen 𝒜 (b * c)
  have hW' : projPartialMap f y ∈ W' := ⟨hW, hdy⟩
  have hW'V : W' ≤ V := inf_le_left.trans iWV.le
  have hres : (Proj 𝒜).presheaf.map (homOfLE hW'V).op r =
      (Proj 𝒜).presheaf.map (homOfLE inf_le_right : W' ⟶ Proj.basicOpen 𝒜 (b * c)).op
        (Proj.awayToSection 𝒜 (b * c) x) := by
    apply Subtype.ext
    funext z
    have e := hr ⟨z.1, z.2.1⟩
    change r.1 ⟨z.1, _⟩ = HomogeneousLocalization.mapId 𝒜 _ x
    refine e.trans (HomogeneousLocalization.val_injective _ ?_)
    rw [HomogeneousLocalization.val_mk]
    change _ = (HomogeneousLocalization.mk _).val
    rw [HomogeneousLocalization.val_mk]
    refine Localization.mk_eq_mk_iff.2 (Localization.r_iff_exists.2 ⟨1, ?_⟩)
    simp only [OneMemClass.coe_one, one_mul]
    change b * c * a = b * (a * c)
    ring
  -- reduce to the section `x` over `D₊(bc)`
  have nat1 := ConcreteCategory.congr_hom
    ((projPartialMap f).naturality (homOfLE hW'V).op) r
  have nat2 := ConcreteCategory.congr_hom
    ((projPartialMap f).naturality (homOfLE inf_le_right : W' ⟶ Proj.basicOpen 𝒜 (b * c)).op)
    (Proj.awayToSection 𝒜 (b * c) x)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at nat1 nat2
  have hyd : y ∈ projPartialMap f ⁻¹ᵁ Proj.basicOpen 𝒜 (b * c) := hdy
  have e1 : sectionValue (V := (projPartialDomain f).ι ''ᵁ (projPartialMap f ⁻¹ᵁ V))
      ((projPartialMap f).app V r) ((projPartialDomain f).ι y) ⟨y, hy, rfl⟩ =
      sectionValue (V := (projPartialDomain f).ι ''ᵁ
        (projPartialMap f ⁻¹ᵁ Proj.basicOpen 𝒜 (b * c)))
        ((projPartialMap f).app _ (Proj.awayToSection 𝒜 (b * c) x))
        ((projPartialDomain f).ι y) ⟨y, hyd, rfl⟩ := by
    have h1 := congrArg (fun t => sectionValue (V := (projPartialDomain f).ι ''ᵁ
      (projPartialMap f ⁻¹ᵁ W')) t ((projPartialDomain f).ι y) ⟨y, hW', rfl⟩) nat1
    have h2 := congrArg (fun t => sectionValue (V := (projPartialDomain f).ι ''ᵁ
      (projPartialMap f ⁻¹ᵁ W')) t ((projPartialDomain f).ι y) ⟨y, hW', rfl⟩) nat2
    simp only at h1 h2
    rw [hres] at h1
    exact h1.symm.trans h2
  rw [e1]
  have hφ : (projPartialDomain f).ι y ∈ Proj.basicOpen ℬ (f (b * c)) := by
    rw [Proj.mem_basicOpen, map_mul]
    intro h
    rcases ((projPartialDomain f).ι y).isPrime.mem_or_mem h with h | h
    · apply hby
      rw [projPartialMap_apply_asHomogeneousIdeal]
      exact h
    · exact hyc h
  have hmem : (projPartialDomain f).ι y ∈ (Proj.basicOpen ℬ (f (b * c))).ι ''ᵁ ⊤ :=
    ⟨⟨_, hφ⟩, trivial, rfl⟩
  have hc := projPartialMap_appLE_awayToSection f hd hdk x
  rw [Scheme.Hom.comp_appLE, Scheme.homOfLE_appLE] at hc
  have hc' := congrArg (fun t => sectionValue (V := (Proj.basicOpen ℬ (f (b * c))).ι ''ᵁ ⊤) t
    ((projPartialDomain f).ι y) hmem) hc
  refine hc'.trans ?_
  have hrv := hr ⟨projPartialMap f y, hW⟩
  refine Eq.trans ?_ (congrArg (HomogeneousLocalization.map f
    (primeCompl_le_comap_projPartialMap f y)) hrv).symm
  apply HomogeneousLocalization.val_injective
  change (HomogeneousLocalization.mapId ℬ _ (Away.map f (b * c) x)).val = _
  rw [HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk]
  change (HomogeneousLocalization.mapId ℬ _ (HomogeneousLocalization.map f _
    (HomogeneousLocalization.mk _))).val = _
  rw [HomogeneousLocalization.map_mk, HomogeneousLocalization.map_mk,
    HomogeneousLocalization.val_mk]
  refine Localization.mk_eq_mk_iff.2 (Localization.r_iff_exists.2 ⟨1, ?_⟩)
  simp only [OneMemClass.coe_one, one_mul]
  change f b * (RingHom.id B) (f (a * c)) = (RingHom.id B) (f (b * c)) * f a
  simp only [RingHom.id_apply, map_mul]
  ring

end PartialChart

section Psi

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] (f : 𝒜 →+*ᵍ ℬ) (n : ℤ)

open ProjTwistMap ProjGradedModuleSheaf

theorem mem_of_mem_image {W : (projPartialDomain f).toScheme.Opens} {z : Proj ℬ}
    (hz : z ∈ (projPartialDomain f).ι ''ᵁ W) : z ∈ projPartialDomain f := by
  obtain ⟨x, -, rfl⟩ := hz
  exact x.2

theorem comap_mem_of_mem_image {V : (Proj 𝒜).Opens} {z : Proj ℬ}
    (hz : z ∈ (projPartialDomain f).ι ''ᵁ (projPartialMap f ⁻¹ᵁ V)) :
    projPartialComapPoint f z (mem_of_mem_image f hz) ∈ V := by
  obtain ⟨x, hx, rfl⟩ := hz
  have h := projPartialMap_apply f x
  change projPartialMap f x ∈ V at hx
  rw [h] at hx
  exact hx

theorem primeCompl_le_comap_point (z : Proj ℬ) (hz : z ∈ projPartialDomain f) :
    (projPartialComapPoint f z hz).asHomogeneousIdeal.toIdeal.primeCompl ≤
      z.asHomogeneousIdeal.toIdeal.primeCompl.comap f :=
  fun _ ha => ha

/-- The sections of `𝒪_{Proj S}(n) ⟶ f_*(𝒪_{Proj T}(n)|_U)` over `V`: a section `s` goes to
`z ↦ φ(s(φ⁻¹ z))`, through the fiber maps. -/
def psiSections (V : (Proj 𝒜).Opens) :
    (sheafInType 𝒜 (gradedTwist 𝒜 n)).1.obj (op V) →+
      (sheafInType ℬ (gradedTwist ℬ n)).1.obj
        (op ((projPartialDomain f).ι ''ᵁ (projPartialMap f ⁻¹ᵁ V))) where
  toFun s := ⟨fun z => twistFiber f n (primeCompl_le_comap_point f z.1 (mem_of_mem_image f z.2))
      (s.1 ⟨_, comap_mem_of_mem_image f z.2⟩), by
    intro z
    obtain ⟨W, hzW, iWV, k, m, hm, t, ht, t_nin, w⟩ := s.2 ⟨_, comap_mem_of_mem_image f z.2⟩
    have hWV : projPartialMap f ⁻¹ᵁ W ≤ projPartialMap f ⁻¹ᵁ V := fun x hx => iWV.le hx
    have hz' : z.1 ∈ (projPartialDomain f).ι ''ᵁ (projPartialMap f ⁻¹ᵁ W) := by
      obtain ⟨x, hx, hxz⟩ := z.2
      refine ⟨x, ?_, hxz⟩
      change projPartialMap f x ∈ W
      rw [projPartialMap_apply]
      have e : projPartialComapPoint f ((projPartialDomain f).ι x) x.2 =
          projPartialComapPoint f z.1 (mem_of_mem_image f z.2) :=
        ProjectiveSpectrum.ext (congrArg (fun p : Proj ℬ => p.asHomogeneousIdeal.comap f) hxz)
      rw [e]
      exact hzW
    refine ⟨(projPartialDomain f).ι ''ᵁ (projPartialMap f ⁻¹ᵁ W), hz',
      homOfLE (Scheme.Hom.image_mono _ hWV), k, f m,
      map_mem_gradedTwist f hm, f t, f.map_mem ht, fun y => ?_, fun y => ?_⟩
    · exact t_nin ⟨_, comap_mem_of_mem_image f y.2⟩
    · exact (congrArg (twistFiber f n _) (w ⟨_, comap_mem_of_mem_image f y.2⟩)).trans
        (twistFiber_mk _ _ _ _ _ _ _ _ _)⟩
  map_zero' := Subtype.ext <| funext fun _ => map_zero (twistFiber f n _)
  map_add' _ _ := Subtype.ext <| funext fun _ => map_add (twistFiber f n _) _ _

theorem map_sectionValue_congr {V : (Proj 𝒜).Opens} (r : Γ(Proj 𝒜, V)) {p q : Proj 𝒜}
    (hpq : p = q) (hp : p ∈ V) (hq : q ∈ V) {Q : Submonoid B}
    (h1 : p.asHomogeneousIdeal.toIdeal.primeCompl ≤ Q.comap f)
    (h2 : q.asHomogeneousIdeal.toIdeal.primeCompl ≤ Q.comap f) :
    HomogeneousLocalization.map f h1 (sectionValue r p hp) =
      HomogeneousLocalization.map f h2 (sectionValue r q hq) := by
  subst hpq
  rfl

/-- `projPartialMap_app_apply` at a point of `Proj T`, with `φ⁻¹(z)` in place of `f(z)`. -/
theorem projPartialMap_app_apply' (V : (Proj 𝒜).Opens) (r : Γ(Proj 𝒜, V)) (z : Proj ℬ)
    (hz : z ∈ (projPartialDomain f).ι ''ᵁ (projPartialMap f ⁻¹ᵁ V)) :
    sectionValue ((projPartialMap f).app V r) z hz =
      HomogeneousLocalization.map f (primeCompl_le_comap_point f z (mem_of_mem_image f hz))
        (sectionValue r _ (comap_mem_of_mem_image f hz)) := by
  obtain ⟨x, hx, rfl⟩ := hz
  exact (projPartialMap_app_apply f V r x hx).trans
    (map_sectionValue_congr f r (projPartialMap_apply f x) _ _ _ _)

/-- The morphism of underlying abelian presheaves. -/
def psiPresheafHom :
    (projTwistingSheaf 𝒜 n).presheaf ⟶ ((Scheme.Modules.pushforward (projPartialMap f)).obj
      ((projTwistingSheaf ℬ n).restrict (projPartialDomain f).ι)).presheaf where
  app V := AddCommGrpCat.ofHom (psiSections f n V.unop)
  naturality _ _ _ := rfl

set_option backward.isDefEq.respectTransparency false in
/-- **The morphism `𝒪_{Proj S}(n) ⟶ f_*(𝒪_{Proj T}(n)|_U)`** for the partial morphism
`f : U ⟶ Proj S`: on sections it is `s ↦ (z ↦ φ(s(φ⁻¹ z)))`. -/
def psi : projTwistingSheaf 𝒜 n ⟶ (Scheme.Modules.pushforward (projPartialMap f)).obj
    ((projTwistingSheaf ℬ n).restrict (projPartialDomain f).ι) :=
  ⟨PresheafOfModules.homMk (psiPresheafHom f n) fun V r s => Subtype.ext <| funext fun z => by
    refine (twistFiber_smul f n _ _ _).trans (congrArg (· • _) ?_)
    simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
    exact (projPartialMap_app_apply' f V.unop r z.1 z.2).symm⟩

end Psi

end ProjTwistPullback

end Hartshorne

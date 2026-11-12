/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.SectionAlgebraUniformBound
import Hartshorne.Scheme.ProjectionFromPoint

/-!
# The section-algebra model as a sheaf of graded algebras

Hartshorne, *Algebraic Geometry*, II, proof of Theorem 7.17, Steps 1–3 (pp. 166–167).

Identifying the graded pieces of the model `T^{(d)}` with `f_* L^{md}` as sheaves. Let
`i : Z ⟶ ℙʳ_X` be a closed immersion of an integral scheme, `f = π ∘ i`, and `𝒪(n)|_Z` the pullback
of `𝒪(n)` along `Z ⟶ ℙʳ_X ⟶ ℙʳ_ℤ`.

* `SectionAlgebraModel.polyTwistSection`: `Γ(X, U)[x₀, …, xᵣ] → Γ(f⁻¹(U), 𝒪(n)|_Z)`,
  `∑ a_α x^α ↦ ∑ f^*(a_α) x^α` (degree-`n` monomials), defined for every open `U`; it is additive,
  `Γ(X, U)`-linear (`polyTwistSection_C_mul`) and compatible with restriction
  (`polyTwistSection_restrict`), because it is built from global sections pulled back from `ℙʳ_ℤ`.
* `SectionAlgebraModel.chartTwistSection`: for an affine open `U`, the bijection
  `Γ(f⁻¹(U), 𝒪(n)|_Z) → Γ(Proj T(U), 𝒪(n))` obtained by pulling back along the chart
  `Proj T(U) ≅ f⁻¹(U)` (`chartTwistSection_bijective`), which sends the pulled-back monomial `x^α`
  to `x^α / 1` (`chartTwistSection_monomialSection`).
* `SectionAlgebraModel.coordTwistSection`: `T(U)_n → Γ(f⁻¹(U), 𝒪(n)|_Z)`, `[p] ↦ ∑ f^*(a_α) x^α`,
  natural (`coordTwistSection_restrict`), `Γ(X, U)`-linear (`coordTwistSection_structureMap_mul`)
  and bijective whenever `s ↦ s / 1` is (`coordTwistSection_bijective`); the key identity is
  `chartTwistSection_polyTwistSection`.
* `SectionAlgebraModel.exists_sectionAlgebraModel_natural`: the model `S = T^{(d)}` with
  `Γ(f⁻¹(U), L^{md}) ≅ S(U)_m` compatible with restriction and `Γ(X, U)`-linear.
* Supporting results: `projMapTwistIso_hom_pullbackGlobalSection` (the isomorphism
  `(Proj.map φ)^* 𝒪(n) ≅ 𝒪(n)` sends the pullback of `s / 1` to `φ(s) / 1`),
  `toSpecZero_appTop_smul_twistSection` (a function pulled back from `t ∈ S₀` multiplies `s / 1`
  by `t`), `coordToZ_comp_fst`, `coordToZ_comp_app`.
-/

universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Hartshorne

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite GradedGlobalSections

namespace SectionAlgebraModel

/-! ### Pulled-back global sections -/

/-- `g = g'` identifies `g^* e` with `g'^* e`. -/
theorem pullbackCongr_hom_pullbackGlobalSection {X Y : Scheme.{u}} {g g' : X ⟶ Y} (h : g = g')
    {N : Y.Modules} (e : Γ(N, ⊤)) :
    ((Scheme.Modules.pullbackCongr h).hom.app N).app ⊤ (pullbackGlobalSection g e) =
      pullbackGlobalSection g' e := by
  subst h
  simp [Scheme.Modules.pullbackCongr]

/-- `𝟙^* N ≅ N` sends `𝟙^* e` to `e`. -/
theorem pullbackId_hom_pullbackGlobalSection {X : Scheme.{u}} {N : X.Modules} (e : Γ(N, ⊤)) :
    ((Scheme.Modules.pullbackId X).hom.app N).app ⊤ (pullbackGlobalSection (𝟙 X) e) = e := by
  have h := unit_conjugateEquiv Adjunction.id (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X))
    (Scheme.Modules.pullbackId X).hom N
  rw [Scheme.Modules.conjugateEquiv_pullbackId_hom] at h
  have h2 : ((Scheme.Modules.pullbackId X).hom.app N).app ((𝟙 X) ⁻¹ᵁ ⊤)
      (pullbackSection (𝟙 X) e) = e :=
    (ConcreteCategory.congr_hom (congrArg (fun φ => Scheme.Modules.Hom.app φ ⊤) h) e).symm
  rw [pullbackGlobalSection, hom_app_map, h2]
  exact ConcreteCategory.congr_hom (N.presheaf.map_id _) e

/-! ### Generalities on sections -/

section Sections

variable {Y : Scheme.{u}}

/-- The sections of an isomorphism of `𝒪_Y`-modules are bijective. -/
theorem bijective_app_of_iso {M N : Y.Modules} (e : M ≅ N) (V : Y.Opens) :
    Function.Bijective (e.hom.app V) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨e.inv.app V, fun x => ?_, fun y => ?_⟩
  · have := ConcreteCategory.congr_hom
      (congrArg (fun φ => Scheme.Modules.Hom.app φ V) e.hom_inv_id) x
    rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at this
    exact this.trans rfl
  · have := ConcreteCategory.congr_hom
      (congrArg (fun φ => Scheme.Modules.Hom.app φ V) e.inv_hom_id) y
    rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at this
    exact this.trans rfl

/-- Restriction between equal opens is bijective. -/
theorem bijective_map_of_eq (M : Y.Modules) {V W : Y.Opens} (h : V ≤ W) (h' : W ≤ V) :
    Function.Bijective (M.presheaf.map (homOfLE h).op) := by
  obtain rfl : V = W := le_antisymm h h'
  rw [show homOfLE h = 𝟙 V from rfl, op_id, CategoryTheory.Functor.map_id]
  exact Function.bijective_id

/-- For an open immersion `j` and `W` inside its image, `W(M) → (j^* M)(j⁻¹ W)` is bijective. -/
theorem bijective_pullbackSection_of_le {Y' : Scheme.{u}} (j : Y' ⟶ Y) [IsOpenImmersion j]
    (M : Y.Modules) {W : Y.Opens} (hW : W ≤ j.opensRange) :
    Function.Bijective (pullbackSection (N := M) j (W := W)) := by
  have h : ∀ y : Γ(M, W), pullbackSection j y =
      ((Scheme.Modules.restrictFunctorIsoPullback j).hom.app M).app (j ⁻¹ᵁ W)
        (M.presheaf.map (homOfLE (j.image_preimage_le W)).op y) := fun y =>
    (Scheme.Modules.restrictFunctorIsoPullback_hom_restrict_unit j M W y).symm
  have hle : W ≤ j ''ᵁ (j ⁻¹ᵁ W) := by
    intro x hx
    obtain ⟨y, rfl⟩ := hW hx
    exact ⟨y, hx, rfl⟩
  rw [show (pullbackSection (N := M) j (W := W)) = _ from funext h]
  exact (bijective_app_of_iso ((Scheme.Modules.restrictFunctorIsoPullback j).app M) _).comp
    (bijective_map_of_eq M _ hle)

/-- For `⊤ ≤ j⁻¹(W)`, the additive map `W(M) → (j^* M)(⊤)`, `s ↦ j^* s`. -/
def pullbackTopAddHom {Y' : Scheme.{u}} (j : Y' ⟶ Y) (M : Y.Modules) {W : Y.Opens}
    (hW : ⊤ ≤ j ⁻¹ᵁ W) : Γ(M, W) →+ Γ((Scheme.Modules.pullback j).obj M, ⊤) :=
  AddMonoidHom.mk' (fun s => ((Scheme.Modules.pullback j).obj M).presheaf.map (homOfLE hW).op
      (pullbackSection j s)) fun a b => by
    have h : pullbackSection j (a + b) = pullbackSection j a + pullbackSection j b :=
      Ringed.etaSec_add (φ := j.toRingCatSheafHom) a b
    simp only [h, map_add]

theorem pullbackTopAddHom_apply {Y' : Scheme.{u}} (j : Y' ⟶ Y) (M : Y.Modules) {W : Y.Opens}
    (hW : ⊤ ≤ j ⁻¹ᵁ W) (s : Γ(M, W)) :
    pullbackTopAddHom j M hW s =
      ((Scheme.Modules.pullback j).obj M).presheaf.map (homOfLE hW).op (pullbackSection j s) :=
  rfl

/-- `e ∘ j^*` is bijective on `W`, for an open immersion `j` with `W` inside its image. -/
theorem bijective_iso_comp_pullbackTopAddHom {Y' : Scheme.{u}} (j : Y' ⟶ Y) [IsOpenImmersion j]
    (M : Y.Modules) {W : Y.Opens} (hW : ⊤ ≤ j ⁻¹ᵁ W) (hWj : W ≤ j.opensRange) {N : Y'.Modules}
    (e : (Scheme.Modules.pullback j).obj M ≅ N) :
    Function.Bijective ((e.hom.app ⊤).hom.comp (pullbackTopAddHom j M hW)) :=
  (bijective_app_of_iso e ⊤).comp ((bijective_map_of_eq _ hW le_top).comp
    (bijective_pullbackSection_of_le j M hWj))

/-- `e ∘ j^*` is semilinear along `j^*`. -/
theorem iso_comp_pullbackTopAddHom_smul {Y' : Scheme.{u}} (j : Y' ⟶ Y) (M : Y.Modules)
    {X' : Scheme.{u}} (g : Y ⟶ X') {V : X'.Opens} (hW : ⊤ ≤ j ⁻¹ᵁ (g ⁻¹ᵁ V)) {N : Y'.Modules}
    (e : (Scheme.Modules.pullback j).obj M ≅ N) (a : Γ(X', V)) (c : Γ(Y', ⊤))
    (hW' : ⊤ ≤ (j ≫ g) ⁻¹ᵁ V) (hc : (j ≫ g).appLE V ⊤ hW' a = c) (s : Γ(M, g ⁻¹ᵁ V)) :
    (e.hom.app ⊤).hom.comp (pullbackTopAddHom j M hW) (g.app V a • s) =
      c • (e.hom.app ⊤).hom.comp (pullbackTopAddHom j M hW) s := by
  subst hc
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, pullbackTopAddHom_apply]
  rw [pullbackSection_smul, Scheme.Modules.map_smul, Scheme.Modules.Hom.app_smul,
    Scheme.Hom.comp_appLE]
  rfl

end Sections

/-! ### Pulled-back sections of twisting sheaves along `Proj.map` -/

section ProjMap

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] (φ : 𝒜 →+*ᵍ ℬ)
  (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map φ)

private def toDom : Proj ℬ ⟶ (projPartialDomain φ).toScheme :=
  (Proj ℬ).topIso.inv ≫ (Proj ℬ).homOfLE (projPartialDomain_eq_top hf).ge

private theorem toDom_ι : toDom φ hf ≫ (projPartialDomain φ).ι = 𝟙 _ := by
  simp [toDom]

private theorem toDom_ppm : toDom φ hf ≫ projPartialMap φ = Proj.map φ hf := by
  rw [projPartialMap_eq_map hf, ← Category.assoc, toDom_ι, Category.id_comp]

/-- `(Proj.map φ)^* 𝒪_{Proj S}(n) ≅ 𝒪_{Proj T}(n)` (Proposition 5.12(c), everywhere-defined case),
in a form whose effect on pulled-back sections is computed below. -/
def projMapTwistIso (hgen : Algebra.adjoin (𝒜 0) (𝒜 1 : Set A) = ⊤) (n : ℤ) :
    (Scheme.Modules.pullback (Proj.map φ hf)).obj (projTwistingSheaf 𝒜 n) ≅
      projTwistingSheaf ℬ n :=
  (Scheme.Modules.pullbackCongr (toDom_ppm φ hf).symm).app _ ≪≫
    ((Scheme.Modules.pullbackComp (toDom φ hf) (projPartialMap φ)).app _).symm ≪≫
    (Scheme.Modules.pullback (toDom φ hf)).mapIso
      (ProjTwistPullback.pullbackTwistIso φ n hgen ≪≫
        (Scheme.Modules.restrictFunctorIsoPullback (projPartialDomain φ).ι).app _) ≪≫
    (Scheme.Modules.pullbackComp (toDom φ hf) (projPartialDomain φ).ι).app _ ≪≫
    (Scheme.Modules.pullbackCongr (toDom_ι φ hf)).app _ ≪≫
    (Scheme.Modules.pullbackId _).app _

variable (hgen : Algebra.adjoin (𝒜 0) (𝒜 1 : Set A) = ⊤)

/-- The pullback along `φ`-partial map of `s / 1` is `φ(s) / 1` on the domain. -/
private theorem psiAdj_restrict_pullbackGlobalSection (d : ℕ) (s : 𝒜 d) :
    (((ProjTwistPullback.pullbackTwistIso φ d hgen).hom ≫
        (Scheme.Modules.restrictFunctorIsoPullback (projPartialDomain φ).ι).hom.app _).app ⊤)
        (pullbackGlobalSection (projPartialMap φ) (twistSection d s (op ⊤))) =
      pullbackGlobalSection (N := projTwistingSheaf ℬ d) (projPartialDomain φ).ι
        (twistSection d ⟨φ s, φ.map_mem s.2⟩ (op ⊤)) := by
  have hpsi : ((ProjTwistPullback.pullbackTwistIso φ d hgen).hom.app (projPartialMap φ ⁻¹ᵁ ⊤))
      (pullbackSection (projPartialMap φ) (twistSection d s (op ⊤))) =
      (ProjTwistPullback.psi φ d).app ⊤ (twistSection d s (op ⊤)) :=
    ProjTwistPullback.psiAdj_etaSec φ d (V := ⊤) (twistSection d s (op ⊤))
  rw [pullbackGlobalSection, pullbackGlobalSection, hom_app_map,
    Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, hpsi, pullbackSection_eq_unit,
    ← Scheme.Modules.restrictFunctorIsoPullback_hom_restrict_unit, ← hom_app_map, ← hom_app_map]
  congr 1
  refine ProjGradedModuleSheaf.section_ext (𝒜 := ℬ) (ℳ := gradedTwist ℬ d)
    (U := op ((projPartialDomain φ).ι ''ᵁ ⊤)) fun x => ?_
  change ProjTwistMap.twistFiber φ d _ (twistFraction d _ s.2) = twistFraction d _ (φ.map_mem s.2)
  ext
  rw [ProjTwistMap.val_twistFiber, twistFraction_val, twistFraction_val, ProjTwistMap.locMap_mk]
  congr 1
  exact Subtype.ext (map_one φ)

theorem projMapTwistIso_hom_pullbackGlobalSection (d : ℕ) (s : 𝒜 d) :
    ((projMapTwistIso φ hf hgen d).hom.app ⊤)
        (pullbackGlobalSection (Proj.map φ hf) (twistSection d s (op ⊤))) =
      twistSection d ⟨φ s, φ.map_mem s.2⟩ (op ⊤) := by
  have e1 := pullbackCongr_hom_pullbackGlobalSection (N := projTwistingSheaf 𝒜 d)
    (toDom_ppm φ hf).symm
    (twistSection d s (op ⊤))
  have e2 := pullbackComp_inv_pullbackGlobalSection (N := projTwistingSheaf 𝒜 d) (toDom φ hf)
    (projPartialMap φ)
    (twistSection d s (op ⊤))
  have e3 := pullback_map_pullbackGlobalSection (toDom φ hf)
    ((ProjTwistPullback.pullbackTwistIso φ d hgen).hom ≫
        (Scheme.Modules.restrictFunctorIsoPullback (projPartialDomain φ).ι).hom.app _)
    (pullbackGlobalSection (projPartialMap φ) (twistSection d s (op ⊤)))
  have e5 := pullbackComp_hom_pullbackGlobalSection (N := projTwistingSheaf ℬ d) (toDom φ hf)
    (projPartialDomain φ).ι (twistSection d ⟨φ s, φ.map_mem s.2⟩ (op ⊤))
  have e6 := pullbackCongr_hom_pullbackGlobalSection (N := projTwistingSheaf ℬ d) (toDom_ι φ hf)
    (twistSection d ⟨φ s, φ.map_mem s.2⟩ (op ⊤))
  have e7 := pullbackId_hom_pullbackGlobalSection (N := projTwistingSheaf ℬ d) (twistSection d ⟨φ s, φ.map_mem s.2⟩ (op ⊤))
  simp only [projMapTwistIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom,
    Iso.app_inv, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  rw [e1, e2, e3, psiAdj_restrict_pullbackGlobalSection, e5, e6, e7]

/-- `j^* ε^* 𝒪(n) ≅ 𝒪(n)` for `j ≫ ε = Proj.map φ`. -/
def pullbackPullbackTwistIso {Y : Scheme.{u}} (ε : Y ⟶ Proj 𝒜) (j : Proj ℬ ⟶ Y)
    (h : j ≫ ε = Proj.map φ hf) (n : ℤ) :
    (Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback ε).obj (projTwistingSheaf 𝒜 n)) ≅
      projTwistingSheaf ℬ n :=
  (Scheme.Modules.pullbackComp j ε).app _ ≪≫ (Scheme.Modules.pullbackCongr h).app _ ≪≫
    projMapTwistIso φ hf hgen n

theorem pullbackPullbackTwistIso_pullbackTop {Y : Scheme.{u}} (ε : Y ⟶ Proj 𝒜)
    (j : Proj ℬ ⟶ Y) (h : j ≫ ε = Proj.map φ hf) {W : Y.Opens} (hW : ⊤ ≤ j ⁻¹ᵁ W) (d : ℕ)
    (s : 𝒜 d) :
    ((pullbackPullbackTwistIso φ hf hgen ε j h d).hom.app ⊤).hom.comp
        (pullbackTopAddHom j ((Scheme.Modules.pullback ε).obj (projTwistingSheaf 𝒜 d)) hW)
        (((Scheme.Modules.pullback ε).obj (projTwistingSheaf 𝒜 d)).presheaf.map
          (homOfLE le_top).op (pullbackGlobalSection (N := projTwistingSheaf 𝒜 d) ε
            (twistSection d s (op ⊤)))) =
      twistSection d ⟨φ s, φ.map_mem s.2⟩ (op ⊤) := by
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, pullbackTopAddHom_apply]
  rw [pullbackSection_restrict, Scheme.Modules.map_map_homOfLE]
  change ((pullbackPullbackTwistIso φ hf hgen ε j h d).hom.app ⊤)
    (pullbackGlobalSection j _) = _
  simp only [pullbackPullbackTwistIso, Iso.trans_hom, Iso.app_hom, Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply]
  rw [pullbackComp_hom_pullbackGlobalSection, pullbackCongr_hom_pullbackGlobalSection,
    projMapTwistIso_hom_pullbackGlobalSection]

end ProjMap


/-! ### Functions from `Spec S₀` acting on twisted sections -/

section ToSpecZero

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜]

/-- The value at `x` of the function on `Proj S` pulled back from `t ∈ S₀` along
`Proj S ⟶ Spec S₀` is `t / 1`. -/
theorem toSpecZero_appTop_val (t : 𝒜 0) (x : Proj 𝒜) :
    (((Proj.toSpecZero 𝒜).appTop ((Scheme.ΓSpecIso (.of (𝒜 0))).inv t)).1 ⟨x, trivial⟩).val =
      Localization.mk (t : A) 1 := by
  simp only [Proj.toSpecZero, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  rw [← CommRingCat.comp_apply (Scheme.ΓSpecIso _).inv, ← Scheme.ΓSpecIso_inv_naturality,
    CommRingCat.comp_apply]
  rw [show Scheme.Hom.appTop (Proj.basicOpenToSpec 𝒜 1) = _ from Proj.basicOpenToSpec_app_top _ 1]
  simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply]
  simp only [Scheme.isoOfEq_inv, Scheme.homOfLE_appTop, Scheme.Opens.topIso_inv]
  have h1 : (⊤ : (Proj 𝒜).Opens) ≤ Proj.basicOpen 𝒜 1 := by rw [Proj.basicOpen_one]
  erw [topIso_inv_appTop_presheaf_map_map h1]
  change (((Proj.awayToSection 𝒜 1).hom (HomogeneousLocalization.fromZeroRingHom 𝒜
    (Submonoid.powers 1) t)).1 ⟨x, h1 trivial⟩).val = _
  erw [ProjectiveSpectrum.Proj.awayToSection_apply]
  change IsLocalization.map _ _ _ (Localization.mk (t : A) 1) = _
  rw [Localization.mk_one_eq_algebraMap, IsLocalization.map_eq, RingHom.id_apply,
    Localization.mk_one_eq_algebraMap]

/-- The function pulled back from `t ∈ S₀` along `Proj S ⟶ Spec S₀` multiplies `s / 1` by `t`. -/
theorem toSpecZero_appTop_smul_twistSection (t : 𝒜 0) (d : ℕ) (m : 𝒜 d) :
    ((Proj.toSpecZero 𝒜).appTop ((Scheme.ΓSpecIso (.of (𝒜 0))).inv t)) •
        (show Γ(projTwistingSheaf 𝒜 d, ⊤) from twistSection d m (op ⊤)) =
      twistSection d ⟨(t : A) * m, by simpa using SetLike.mul_mem_graded t.2 m.2⟩ (op ⊤) := by
  refine ProjGradedModuleSheaf.section_ext (𝒜 := 𝒜) (ℳ := gradedTwist 𝒜 d) (U := op ⊤)
    fun x => ?_
  change ((Proj.toSpecZero 𝒜).appTop ((Scheme.ΓSpecIso (.of (𝒜 0))).inv t)).1 x •
    twistFraction d x.1 m.2 = twistFraction d x.1
      (show (t : A) * m ∈ 𝒜 d by simpa using SetLike.mul_mem_graded t.2 m.2)
  ext
  rw [HomogeneousLocalizedModule.val_smul]
  erw [toSpecZero_appTop_val t x.1]
  rw [twistFraction_val, twistFraction_val]
  exact (LocalizedModule.mk_smul_mk _ _ _ _).trans (by rw [smul_eq_mul, mul_one])

/-- The functions on `Proj S` pulled back from `Γ(X, U)` along `Proj S ⟶ Spec S₀ ⟶ Spec Γ(X, U) ≅ U`
are those pulled back from `S₀`. -/
theorem toSpecZero_comp_appLE {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (α : Γ(X, U) ⟶ CommRingCat.of (𝒜 0))
    (hle : ⊤ ≤ (Proj.toSpecZero 𝒜 ≫ Spec.map α ≫ hU.fromSpec) ⁻¹ᵁ U) :
    (Proj.toSpecZero 𝒜 ≫ Spec.map α ≫ hU.fromSpec).appLE U ⊤ hle =
      α ≫ (Scheme.ΓSpecIso _).inv ≫ (Proj.toSpecZero 𝒜).appTop := by
  have h1 : hU.fromSpec.appLE U ⊤ hU.fromSpec_preimage_self.ge = (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    convert Category.comp_id _
    exact (Spec Γ(X, U)).presheaf.map_id _
  calc (Proj.toSpecZero 𝒜 ≫ Spec.map α ≫ hU.fromSpec).appLE U ⊤ hle =
      hU.fromSpec.appLE U ⊤ hU.fromSpec_preimage_self.ge ≫
        (Spec.map α).appLE ⊤ ⊤ le_rfl ≫ (Proj.toSpecZero 𝒜).appLE ⊤ ⊤ le_rfl := by
        rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
        simp only [Category.assoc]
    _ = α ≫ (Scheme.ΓSpecIso _).inv ≫ (Proj.toSpecZero 𝒜).appTop := by
        have htop : ∀ {Y Y' : Scheme.{u}} (g : Y ⟶ Y') (h : ⊤ ≤ g ⁻¹ᵁ ⊤), g.appLE ⊤ ⊤ h = g.appTop :=
          fun g h => by
            rw [Scheme.Hom.appLE, show homOfLE h = 𝟙 _ from rfl]
            exact (congrArg (Scheme.Hom.app g ⊤ ≫ ·) (CategoryTheory.Functor.map_id _ _)).trans
              (Category.comp_id _)
        rw [h1, htop, htop, ← Category.assoc,
          ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]

end ToSpecZero


/-! ### The charts `Proj T(U) ⟶ Z` over `ℙʳ_ℤ` and over `X` -/

section Chart

attribute [local instance] MvPolynomial.gradedAlgebra

variable {r : ℕ} {X Z : Scheme.{u}} (i : Z ⟶ projectiveSpaceOverScheme r X) [IsClosedImmersion i]
  [IsIntegral Z]

/-- The graded homomorphism `ℤ[x₀, …, xᵣ] → T(U) = Γ(X, U)[x₀, …, xᵣ] / I_U`. -/
def coordHom (U : X.AffineZariskiSite) :
    GeneratedProj.intGrading.{u} r →+*ᵍ (coordinateAlgebra i).grading U :=
  (gradedQuotientMk _ (chartIdeal i U.1 U.2)).comp
    (projectiveSpaceComparisonHom Γ(X, U.1) r (Equiv.refl _))

omit [IsClosedImmersion i] in
theorem irrelevant_le_coordHom (U : X.AffineZariskiSite) :
    HomogeneousIdeal.irrelevant ((coordinateAlgebra i).grading U) ≤
      (HomogeneousIdeal.irrelevant (GeneratedProj.intGrading.{u} r)).map (coordHom i U) :=
  HomogeneousIdeal.irrelevant_le_map_comp
    (GeneratedProj.irrelevant_le_map_evalGradedHom _ (projectiveSpaceGenerators_mem Γ(X, U.1) r _)
      (adjoin_projectiveSpaceGenerators Γ(X, U.1) r _))
    (ProjTruncation.irrelevant_le_map_of_surjective (gradedQuotientMk_surjective _ _))

/-- **The chart `Proj T(U) ⟶ Z` over `ℙʳ_ℤ`**: followed by `Z ⟶ ℙʳ_X ⟶ ℙʳ_ℤ` it is the morphism
`Proj T(U) ⟶ Proj ℤ[x]` induced by `ℤ[x] → T(U)`. -/
theorem coordToZ_comp_fst (U : X.AffineZariskiSite) :
    coordToZ i U ≫ i ≫ pullback.fst (projectiveSpaceOverIntegersMap r) (schemeToSpecZ X) =
      Proj.map (coordHom i U) (irrelevant_le_coordHom i U) := by
  rw [reassoc_of% coordToZ_comp, chartToProjectiveSpace, Category.assoc, Category.assoc,
    projectiveSpaceOverSchemeMap_fst, projectiveSpaceOverSpecIso_hom,
    projToProjectiveSpaceOverSpec_fst]
  exact (Proj.map_comp _ _ _ _).symm

theorem preimage_coordToZ_comp (U : X.AffineZariskiSite) :
    (coordToZ i U ≫ i ≫ projectiveSpaceOverSchemeProjection r X) ⁻¹ᵁ U.1 = ⊤ := by
  rw [coordToZ_base]
  ext x
  simp

/-- The functions on `Proj T(U)` pulled back from `Γ(X, U)` along `Proj T(U) ⟶ Z ⟶ X` are those
pulled back from `T(U)₀` along `Proj T(U) ⟶ Spec T(U)₀`. -/
theorem coordToZ_comp_app (U : X.AffineZariskiSite) (a : Γ(X, U.1)) :
    (coordToZ i U ≫ i ≫ projectiveSpaceOverSchemeProjection r X).appLE U.1 ⊤
        (preimage_coordToZ_comp i U).ge a =
      (Proj.toSpecZero ((coordinateAlgebra i).grading U)).appTop
        ((Scheme.ΓSpecIso _).inv ((coordinateAlgebra i).toZero U a)) := by
  have key : ∀ (g : Proj ((coordinateAlgebra i).grading U) ⟶ X) (hle : ⊤ ≤ g ⁻¹ᵁ U.1)
      (_ : g = Proj.toSpecZero _ ≫ Spec.map ((coordinateAlgebra i).toZero U) ≫ U.2.fromSpec),
      g.appLE U.1 ⊤ hle a = (Proj.toSpecZero ((coordinateAlgebra i).grading U)).appTop
          ((Scheme.ΓSpecIso _).inv ((coordinateAlgebra i).toZero U a)) := by
    rintro _ hle rfl
    exact congr($(toSpecZero_comp_appLE U.2 _ hle) a)
  exact key _ _ ((coordToZ_base i U).trans (QuasiCoherentGradedAlgebra.projToOpen_ι _ U))

end Chart

/-! ### The comparison `T(U)_n ≅ Γ(f⁻¹(U), 𝒪(n)|_Z)` -/

section Comparison

attribute [local instance] MvPolynomial.gradedAlgebra

variable {r : ℕ} {X Z : Scheme.{u}} (i : Z ⟶ projectiveSpaceOverScheme r X)

/-- `Z ⟶ ℙʳ_X ⟶ ℙʳ_ℤ`. -/
abbrev toIntProj : Z ⟶ Proj (GeneratedProj.intGrading.{u} r) :=
  i ≫ pullback.fst (projectiveSpaceOverIntegersMap r) (schemeToSpecZ X)

/-- The twisting sheaf `𝒪(n)` of `ℙʳ_ℤ` pulled back to `Z`. -/
abbrev twistOnZ (n : ℕ) : Z.Modules :=
  (Scheme.Modules.pullback (toIntProj i)).obj
    (projTwistingSheaf (GeneratedProj.intGrading.{u} r) n)

theorem monomial_mem_intGrading {n : ℕ} {α : Fin (r + 1) →₀ ℕ} (h : α.degree = n) :
    MvPolynomial.monomial α (1 : ULift.{u} ℤ) ∈ GeneratedProj.intGrading.{u} r n :=
  MvPolynomial.isHomogeneous_monomial _ h

/-- The pulled-back monomial `x^α`, a global section of `𝒪(n)` on `Z` (zero unless `|α| = n`). -/
def monomialSection (n : ℕ) (α : Fin (r + 1) →₀ ℕ) : Γ(twistOnZ i n, ⊤) :=
  if h : α.degree = n then
    pullbackGlobalSection (N := projTwistingSheaf (GeneratedProj.intGrading.{u} r) n)
      (toIntProj i) (twistSection n ⟨_, monomial_mem_intGrading h⟩ (op ⊤))
  else 0

/-- **The comparison map** `Γ(X, U)[x₀, …, xᵣ] → Γ(f⁻¹(U), 𝒪(n)|_Z)`,
`∑ a_α x^α ↦ ∑ f^*(a_α) x^α` (only the monomials of degree `n` contribute). -/
def polyTwistSection (U : X.Opens) (n : ℕ) (p : MvPolynomial (Fin (r + 1)) Γ(X, U)) :
    Γ(twistOnZ i n, (i ≫ projectiveSpaceOverSchemeProjection r X) ⁻¹ᵁ U) :=
  (AddMonoidAlgebra.coeff p).sum fun α a => (i ≫ projectiveSpaceOverSchemeProjection r X).app U a •
    (twistOnZ i n).presheaf.map (homOfLE le_top).op (monomialSection i n α)

theorem polyTwistSection_add (U : X.Opens) (n : ℕ) (p q : MvPolynomial (Fin (r + 1)) Γ(X, U)) :
    polyTwistSection i U n (p + q) = polyTwistSection i U n p + polyTwistSection i U n q :=
  (congrArg (Finsupp.sum · _) (AddMonoidAlgebra.coeff_add p q)).trans <| Finsupp.sum_add_index' (fun _ => by rw [map_zero, zero_smul])
    (fun _ _ _ => by rw [map_add, add_smul])

theorem polyTwistSection_zero (U : X.Opens) (n : ℕ) : polyTwistSection i U n 0 = 0 :=
  (congrArg (Finsupp.sum · _) (AddMonoidAlgebra.coeff_zero)).trans Finsupp.sum_zero_index

theorem polyTwistSection_monomial (U : X.Opens) (n : ℕ) (α : Fin (r + 1) →₀ ℕ) (a : Γ(X, U)) :
    polyTwistSection i U n (MvPolynomial.monomial α a) =
      (i ≫ projectiveSpaceOverSchemeProjection r X).app U a •
        (twistOnZ i n).presheaf.map (homOfLE le_top).op (monomialSection i n α) :=
  (congrArg (Finsupp.sum · _) (AddMonoidAlgebra.coeff_single α a)).trans
    (Finsupp.sum_single_index (by rw [map_zero, zero_smul]))

/-- The comparison map is `Γ(X, U)`-linear. -/
theorem polyTwistSection_C_mul (U : X.Opens) (n : ℕ) (b : Γ(X, U))
    (p : MvPolynomial (Fin (r + 1)) Γ(X, U)) :
    polyTwistSection i U n (MvPolynomial.C b * p) =
      (i ≫ projectiveSpaceOverSchemeProjection r X).app U b • polyTwistSection i U n p := by
  induction p using MvPolynomial.induction_on' with
  | monomial α a =>
    rw [MvPolynomial.C_mul_monomial, polyTwistSection_monomial, polyTwistSection_monomial, map_mul, mul_smul]
  | add p q hp hq => rw [mul_add, polyTwistSection_add, polyTwistSection_add, hp, hq, smul_add]

/-- The comparison map is compatible with restriction. -/
theorem polyTwistSection_restrict {U V : X.Opens} (h : V ≤ U) (n : ℕ)
    (p : MvPolynomial (Fin (r + 1)) Γ(X, U)) :
    (twistOnZ i n).presheaf.map
        (homOfLE ((i ≫ projectiveSpaceOverSchemeProjection r X).preimage_mono h)).op
        (polyTwistSection i U n p) =
      polyTwistSection i V n (polyMap (r := r) (X.presheaf.map (homOfLE h).op).hom p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial α a =>
    rw [polyMap_apply, MvPolynomial.map_monomial, polyTwistSection_monomial, polyTwistSection_monomial,
      Scheme.Modules.map_smul, Scheme.Modules.map_map_homOfLE]
    congr 1
    exact congr($((i ≫ projectiveSpaceOverSchemeProjection r X).naturality (homOfLE h).op) a).symm
  | add p q hp hq => rw [map_add, polyTwistSection_add, polyTwistSection_add, map_add, hp, hq]

variable [IsClosedImmersion i] [IsIntegral Z]

/-- `j_U^* (𝒪(n)|_Z) ≅ 𝒪_{Proj T(U)}(n)` along the chart `j_U : Proj T(U) ⟶ Z`. -/
def chartTwistIso (U : X.AffineZariskiSite) (n : ℕ) :
    (Scheme.Modules.pullback (coordToZ i U)).obj (twistOnZ i n) ≅
      projTwistingSheaf ((coordinateAlgebra i).grading U) n :=
  pullbackPullbackTwistIso (coordHom i U) (irrelevant_le_coordHom i U)
    (adjoin_intGrading_one_eq_top r) (toIntProj i) (coordToZ i U) (coordToZ_comp_fst i U) n

theorem preimage_preimage_coordToZ (U : X.AffineZariskiSite) :
    coordToZ i U ⁻¹ᵁ ((i ≫ projectiveSpaceOverSchemeProjection r X) ⁻¹ᵁ U.1) = ⊤ :=
  preimage_coordToZ_comp i U

/-- **The chart comparison** `Γ(f⁻¹(U), 𝒪(n)|_Z) → Γ(Proj T(U), 𝒪(n))`: pull back along the chart
`Proj T(U) ≅ f⁻¹(U)` and identify the pulled-back twisting sheaf. -/
def chartTwistSection (U : X.AffineZariskiSite) (n : ℕ) :=
  ((chartTwistIso i U n).hom.app ⊤).hom.comp
    (pullbackTopAddHom (coordToZ i U) (twistOnZ i n) (preimage_preimage_coordToZ i U).ge)

theorem chartTwistSection_bijective (U : X.AffineZariskiSite) (n : ℕ) :
    Function.Bijective (chartTwistSection i U n) :=
  bijective_iso_comp_pullbackTopAddHom _ _ _ (coordToZ_range i U).le _

theorem chartTwistSection_monomialSection (U : X.AffineZariskiSite) {n : ℕ}
    {α : Fin (r + 1) →₀ ℕ} (h : α.degree = n) :
    chartTwistSection i U n ((twistOnZ i n).presheaf.map (homOfLE le_top).op
        (monomialSection i n α)) =
      twistSection n ⟨coordHom i U (MvPolynomial.monomial α 1),
        (coordHom i U).map_mem (monomial_mem_intGrading h)⟩ (op ⊤) := by
  rw [monomialSection, dif_pos h]
  exact pullbackPullbackTwistIso_pullbackTop _ _ _ _ _ _ _ _ _

/-- `ℤ[x] → T(U)` sends the monomial `x^α` to the class of `x^α`. -/
theorem coordHom_monomial (U : X.AffineZariskiSite) (α : Fin (r + 1) →₀ ℕ) :
    (coordHom i U (MvPolynomial.monomial α 1) : MvPolynomial (Fin (r + 1)) Γ(X, U.1) ⧸
      (chartIdeal i U.1 U.2).toIdeal) = Ideal.Quotient.mk _ (MvPolynomial.monomial α 1) := by
  change Ideal.Quotient.mk _ (GeneratedProj.evalRingHom _ (MvPolynomial.monomial α 1)) = _
  congr 1
  rw [GeneratedProj.evalRingHom, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial,
    MvPolynomial.monomial_eq]
  simp [projectiveSpaceGenerators]

-- The presentations of `Proj T(U)` in the types of `coordToZ` and `chartTwistIso` differ by
-- auxiliary proof terms; unifying them needs more than the default heartbeats.
set_option maxHeartbeats 1000000 in
/-- **`Γ(X, U)`-scalars pass through the chart map.** For `a ∈ Γ(X, U)`, the chart comparison
sends `f^*(a) • s` to the function pulled back from `a` along `Proj T(U) ⟶ Z ⟶ X` times the image
of `s`. -/
theorem chartTwistSection_smul (U : X.AffineZariskiSite) (n : ℕ) (a : Γ(X, U.1))
    (s : Γ(twistOnZ i n, (i ≫ projectiveSpaceOverSchemeProjection r X) ⁻¹ᵁ U.1)) :
    chartTwistSection i U n ((i ≫ projectiveSpaceOverSchemeProjection r X).app U.1 a • s) =
      (coordToZ i U ≫ i ≫ projectiveSpaceOverSchemeProjection r X).appLE U.1 ⊤
        (preimage_coordToZ_comp i U).ge a • chartTwistSection i U n s :=
  iso_comp_pullbackTopAddHom_smul (coordToZ i U) (twistOnZ i n)
    (i ≫ projectiveSpaceOverSchemeProjection r X) (preimage_preimage_coordToZ i U).ge
    (chartTwistIso i U n) a _ (preimage_coordToZ_comp i U).ge rfl s

section TS
variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜]

/-- `s ↦ s / 1`, `S_n → Γ(Proj S, 𝒪(n))`, is additive. -/
theorem twistSection_add (n : ℕ) (s s' : 𝒜 n) :
    twistSection n (s + s') (op ⊤) = twistSection n s (op ⊤) + twistSection n s' (op ⊤) := by
  apply ProjGradedModuleSheaf.section_ext
  intro x
  apply HomogeneousLocalizedModule.ext
  change LocalizedModule.mk ((s : A) + s') 1 =
    LocalizedModule.mk (s : A) 1 + LocalizedModule.mk (s' : A) 1
  rw [LocalizedModule.mk_add_mk, one_smul, one_smul, mul_one]

/-- `0 / 1 = 0` in `Γ(Proj S, 𝒪(n))`. -/
theorem twistSection_zero (n : ℕ) : twistSection n (0 : 𝒜 n) (op ⊤) = 0 := by
  apply ProjGradedModuleSheaf.section_ext
  intro x
  apply HomogeneousLocalizedModule.ext
  change LocalizedModule.mk ((0 : 𝒜 n) : A) 1 = 0
  rw [ZeroMemClass.coe_zero, LocalizedModule.zero_mk]
end TS

/-- The class of the degree-`n` component of `p` lies in `T(U)_n`. -/
theorem mk_homogeneousComponent_mem (U : X.AffineZariskiSite) (n : ℕ)
    (p : MvPolynomial (Fin (r + 1)) Γ(X, U.1)) :
    Ideal.Quotient.mk (chartIdeal i U.1 U.2).toIdeal (MvPolynomial.homogeneousComponent n p) ∈
      (coordinateAlgebra i).grading U n :=
  mk_mem_gradedQuotient (MvPolynomial.homogeneousComponent_mem n p)

/-- If the degree-`n` component of `p` vanishes, so does its section `p_n / 1`. -/
theorem twistSection_mk_homogeneousComponent_eq_zero (U : X.AffineZariskiSite) {n : ℕ}
    {p : MvPolynomial (Fin (r + 1)) Γ(X, U.1)} (hp : MvPolynomial.homogeneousComponent n p = 0) :
    twistSection (𝒜 := (coordinateAlgebra i).grading U) n
      ⟨_, mk_homogeneousComponent_mem i U n p⟩ (op ⊤) = 0 := by
  have : (⟨_, mk_homogeneousComponent_mem i U n p⟩ : (coordinateAlgebra i).grading U n) = 0 :=
    Subtype.ext (by simp only [hp, map_zero]; rfl)
  exact (congrArg (fun x => twistSection n x (op ⊤)) this).trans (twistSection_zero n)

-- The presentations of `Proj T(U)` in the types of `coordToZ` and `chartTwistIso` differ by
-- auxiliary proof terms; unifying them needs more than the default heartbeats.
set_option maxHeartbeats 1000000 in
/-- **The key identity.** For every `p ∈ Γ(X, U)[x₀, …, xᵣ]`, the chart comparison sends
`∑ f^*(a_α) x^α` (degree-`n` monomials) to the section `p_n / 1` of `𝒪(n)` on `Proj T(U)`, where
`p_n` is the class in `T(U)` of the degree-`n` component of `p`. -/
theorem chartTwistSection_polyTwistSection (U : X.AffineZariskiSite) (n : ℕ)
    (p : MvPolynomial (Fin (r + 1)) Γ(X, U.1)) :
    chartTwistSection i U n (polyTwistSection i U.1 n p) =
      twistSection (𝒜 := (coordinateAlgebra i).grading U) n
        ⟨_, mk_homogeneousComponent_mem i U n p⟩ (op ⊤) := by
  induction p using MvPolynomial.induction_on' with
  | monomial α a =>
    by_cases h : α.degree = n
    · simp only [polyTwistSection_monomial]
      erw [chartTwistSection_smul]
      refine (congrArg (fun x => _ • x) (chartTwistSection_monomialSection i U h)).trans ?_
      rw [coordToZ_comp_app]
      refine (toSpecZero_appTop_smul_twistSection _ n _).trans ?_
      refine congrArg (fun x => twistSection n x (op ⊤)) (Subtype.ext ?_)
      change ((coordinateAlgebra i).toZero U a : MvPolynomial (Fin (r + 1)) Γ(X, U.1) ⧸
        (chartIdeal i U.1 U.2).toIdeal) * (coordHom i U (MvPolynomial.monomial α 1) : _) =
        Ideal.Quotient.mk _ (MvPolynomial.homogeneousComponent n (MvPolynomial.monomial α a))
      rw [MvPolynomial.homogeneousComponent_of_mem ((MvPolynomial.mem_homogeneousSubmodule _ _).2
        (MvPolynomial.isHomogeneous_monomial a h)), if_pos rfl]
      change Ideal.Quotient.mk _ (MvPolynomial.C a) *
        (coordHom i U (MvPolynomial.monomial α 1) : _) = _
      rw [coordHom_monomial, ← map_mul, MvPolynomial.C_mul_monomial, mul_one]
    · have h0 : MvPolynomial.homogeneousComponent n (MvPolynomial.monomial α a) = 0 := by
        rw [MvPolynomial.homogeneousComponent_of_mem ((MvPolynomial.mem_homogeneousSubmodule _ _).2
          (MvPolynomial.isHomogeneous_monomial a rfl)), if_neg (Ne.symm h)]
      refine Eq.trans ?_ (twistSection_mk_homogeneousComponent_eq_zero i U h0).symm
      simp only [polyTwistSection_monomial, monomialSection, dif_neg h, map_zero, smul_zero]
      rfl
  | add p q hp hq =>
    simp only [polyTwistSection_add, map_add]
    rw [hp, hq]
    exact (twistSection_add n ⟨_, mk_homogeneousComponent_mem i U n p⟩
      ⟨_, mk_homogeneousComponent_mem i U n q⟩).symm

/-- The key identity for `p` homogeneous of degree `n`: the image is `[p] / 1`. -/
theorem chartTwistSection_polyTwistSection_of_mem (U : X.AffineZariskiSite) {n : ℕ}
    {p : MvPolynomial (Fin (r + 1)) Γ(X, U.1)}
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin (r + 1)) Γ(X, U.1) n) :
    chartTwistSection i U n (polyTwistSection i U.1 n p) =
      twistSection (𝒜 := (coordinateAlgebra i).grading U) n
        ⟨_, mk_mem_gradedQuotient (I := chartIdeal i U.1 U.2) hp⟩ (op ⊤) :=
  (chartTwistSection_polyTwistSection i U n p).trans
    (congrArg (fun x => twistSection n x (op ⊤)) (Subtype.ext (by
      change Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
      rw [MvPolynomial.homogeneousComponent_of_mem hp, if_pos rfl])))

/-- A homogeneous lift to `Γ(X, U)[x₀, …, xᵣ]_n` of an element of `T(U)_n`. -/
noncomputable def coordLift (U : X.AffineZariskiSite) {n : ℕ}
    (x : (coordinateAlgebra i).grading U n) : MvPolynomial (Fin (r + 1)) Γ(X, U.1) :=
  Classical.choose (mem_gradedQuotient_iff.mp x.2)

/-- The lift is homogeneous of degree `n`. -/
theorem coordLift_mem (U : X.AffineZariskiSite) {n : ℕ} (x : (coordinateAlgebra i).grading U n) :
    coordLift i U x ∈ MvPolynomial.homogeneousSubmodule (Fin (r + 1)) Γ(X, U.1) n :=
  (Classical.choose_spec (mem_gradedQuotient_iff.mp x.2)).1

/-- The lift is a lift. -/
theorem mk_coordLift (U : X.AffineZariskiSite) {n : ℕ} (x : (coordinateAlgebra i).grading U n) :
    Ideal.Quotient.mk (chartIdeal i U.1 U.2).toIdeal (coordLift i U x) = x :=
  (Classical.choose_spec (mem_gradedQuotient_iff.mp x.2)).2

/-- The chart comparison sends the section built from the lift of `x` to `x / 1`. -/
theorem chartTwistSection_polyTwistSection_coordLift (U : X.AffineZariskiSite) {n : ℕ}
    (x : (coordinateAlgebra i).grading U n) :
    chartTwistSection i U n (polyTwistSection i U.1 n (coordLift i U x)) =
      twistSection n x (op ⊤) :=
  (chartTwistSection_polyTwistSection_of_mem i U (coordLift_mem i U x)).trans
    (congrArg (fun x => twistSection n x (op ⊤)) (Subtype.ext (mk_coordLift i U x)))

/-- The section built from the lift is additive in `x`. -/
theorem polyTwistSection_coordLift_add (U : X.AffineZariskiSite) {n : ℕ}
    (x y : (coordinateAlgebra i).grading U n) :
    polyTwistSection i U.1 n (coordLift i U (x + y)) =
      polyTwistSection i U.1 n (coordLift i U x) + polyTwistSection i U.1 n (coordLift i U y) :=
  (chartTwistSection_bijective i U n).1 <|
    (chartTwistSection_polyTwistSection_coordLift i U (x + y)).trans <|
      (twistSection_add n x y).trans <|
        ((congrArg₂ (· + ·) (chartTwistSection_polyTwistSection_coordLift i U x)
          (chartTwistSection_polyTwistSection_coordLift i U y)).symm.trans (map_add _ _ _).symm)

/-- **The comparison `T(U)_n → Γ(f⁻¹(U), 𝒪(n)|_Z)`**, `[p] ↦ ∑ f^*(a_α) x^α` for homogeneous `p`
of degree `n` (well defined by the key identity, since the chart comparison is injective). -/
noncomputable def coordTwistSection (U : X.AffineZariskiSite) (n : ℕ) :
    (coordinateAlgebra i).grading U n →+
      Γ(twistOnZ i n, (i ≫ projectiveSpaceOverSchemeProjection r X) ⁻¹ᵁ U.1) :=
  AddMonoidHom.mk' (fun x => polyTwistSection i U.1 n (coordLift i U x))
    (polyTwistSection_coordLift_add i U)

/-- Followed by the chart comparison, the comparison is `x ↦ x / 1`. -/
theorem chartTwistSection_coordTwistSection (U : X.AffineZariskiSite) {n : ℕ}
    (x : (coordinateAlgebra i).grading U n) :
    chartTwistSection i U n (coordTwistSection i U n x) = twistSection n x (op ⊤) :=
  chartTwistSection_polyTwistSection_coordLift i U x

/-- The comparison sends `[p]` to `∑ f^*(a_α) x^α` for `p` homogeneous of degree `n`. -/
theorem coordTwistSection_mk (U : X.AffineZariskiSite) {n : ℕ}
    {p : MvPolynomial (Fin (r + 1)) Γ(X, U.1)}
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin (r + 1)) Γ(X, U.1) n) :
    coordTwistSection i U n ⟨_, mk_mem_gradedQuotient (I := chartIdeal i U.1 U.2) hp⟩ =
      polyTwistSection i U.1 n p :=
  (chartTwistSection_bijective i U n).1 ((chartTwistSection_coordTwistSection i U _).trans
    (chartTwistSection_polyTwistSection_of_mem i U hp).symm)

open Scheme.AffineZariskiSite in
/-- **Naturality**: the comparison commutes with restriction along affine opens `V ⊆ U`. -/
theorem coordTwistSection_restrict {U V : X.AffineZariskiSite} (h : V ⟶ U) {n : ℕ}
    (x : (coordinateAlgebra i).grading U n) :
    (twistOnZ i n).presheaf.map
        (homOfLE ((i ≫ projectiveSpaceOverSchemeProjection r X).preimage_mono
          (toOpens_mono h.le))).op (coordTwistSection i U n x) =
      coordTwistSection i V n ⟨(coordinateAlgebra i).restrict h x,
        (coordinateAlgebra i).map_mem h x.2⟩ := by
  have hV := (polyMap (r := r) (X.presheaf.map (homOfLE (toOpens_mono h.le)).op).hom).map_mem
    (coordLift_mem i U x)
  refine (polyTwistSection_restrict i (toOpens_mono h.le) n (coordLift i U x)).trans
    ((coordTwistSection_mk i V hV).symm.trans (congrArg _ (Subtype.ext ?_)))
  change _ = coordRestrict i V.2 U.2 (toOpens_mono h.le) (x : _)
  rw [← mk_coordLift i U x, coordRestrict_mk]
  rfl

/-- `T(U)_n` is a `Γ(X, U)`-submodule of `T(U)`. -/
theorem structureMap_mul_mem (U : X.AffineZariskiSite) {n : ℕ} (a : Γ(X, U.1))
    (x : (coordinateAlgebra i).grading U n) :
    (coordinateAlgebra i).structureMap.app (op U) a * x ∈ (coordinateAlgebra i).grading U n := by
  simpa using SetLike.mul_mem_graded ((coordinateAlgebra i).structureMap_mem U a) x.2

/-- **Linearity**: the comparison is `Γ(X, U)`-linear. -/
theorem coordTwistSection_structureMap_mul (U : X.AffineZariskiSite) {n : ℕ} (a : Γ(X, U.1))
    (x : (coordinateAlgebra i).grading U n) :
    coordTwistSection i U n ⟨_, structureMap_mul_mem i U a x⟩ =
      (i ≫ projectiveSpaceOverSchemeProjection r X).app U.1 a • coordTwistSection i U n x := by
  have hC : MvPolynomial.C a * coordLift i U x ∈
      MvPolynomial.homogeneousSubmodule (Fin (r + 1)) Γ(X, U.1) n := by
    simpa using SetLike.mul_mem_graded ((MvPolynomial.mem_homogeneousSubmodule _ _).2
      (MvPolynomial.isHomogeneous_C (Fin (r + 1)) a)) (coordLift_mem i U x)
  refine (congrArg _ (Subtype.ext ?_)).trans ((coordTwistSection_mk i U hC).trans
    (polyTwistSection_C_mul i U.1 n a _))
  change Ideal.Quotient.mk (chartIdeal i U.1 U.2).toIdeal (MvPolynomial.C a) * (x : _) = _
  rw [← mk_coordLift i U x, ← map_mul]

/-- The comparison `T(U)_n → Γ(f⁻¹(U), 𝒪(n)|_Z)` is bijective in every degree in which
`T(U)_n → Γ(Proj T(U), 𝒪(n))`, `s ↦ s / 1`, is. -/
theorem coordTwistSection_bijective (U : X.AffineZariskiSite) {n : ℕ}
    (hbij : Function.Bijective (fun a : gradedQuotient (MvPolynomial.homogeneousSubmodule
      (Fin (r + 1)) Γ(X, U.1)) (chartIdeal i U.1 U.2) n => twistSection n a (op ⊤))) :
    Function.Bijective (coordTwistSection i U n) := by
  refine (Function.Bijective.of_comp_iff' (chartTwistSection_bijective i U n) _).mp ?_
  have e : (chartTwistSection i U n ∘ coordTwistSection i U n) = fun a => twistSection n a (op ⊤) :=
    funext (chartTwistSection_coordTwistSection i U)
  rw [e]
  exact hbij

/-- The tensor power `L^{n}` of `L = i^* 𝒪(1)`, as an `𝒪_Z`-module. -/
abbrev tensorPowerL (n : ℕ) : Z.Modules :=
  moduleSheafTensorPower n ((Scheme.Modules.pullback i).obj (projectiveSpaceTwistingSheaf r X 1))

/-- `L^{n} ≅ 𝒪(n)|_Z` for `n > 0` (Proposition 5.12(b), pulled back to `Z`). -/
noncomputable def tensorPowerTwistOnZIso (n : ℕ) (hn : 0 < n) : tensorPowerL i n ≅ twistOnZ i n :=
  eqToIso (by rw [Nat.sub_add_cancel hn]) ≪≫
    tensorPowerPullbackProjectiveSpaceTwistIso i (n - 1) ≪≫
    (Scheme.Modules.pullbackComp i
      (pullback.fst (projectiveSpaceOverIntegersMap r) (schemeToSpecZ X))).app _ ≪≫
    eqToIso (by rw [Nat.sub_add_cancel hn]; rfl)

private theorem mul_pos_of_neZero {m : ℕ} (d : ℕ) [NeZero d] (hm : 0 < m) : 0 < m * d :=
  Nat.mul_pos hm (Nat.pos_of_ne_zero (NeZero.ne d))

/-- **The comparison `T(U)^{(d)}_m → Γ(f⁻¹(U), L^{md})`** (`m > 0`): `T(U)^{(d)}_m = T(U)_{md}`,
then the comparison with `𝒪(md)|_Z`, then `𝒪(md)|_Z ≅ L^{md}`. -/
noncomputable def veroneseTwistSection (d : ℕ) [NeZero d] (U : X.AffineZariskiSite) {m : ℕ}
    (hm : 0 < m) :
    ((coordinateAlgebra i).veronese d).grading U m →+
      Γ(tensorPowerL i (m * d), (i ≫ projectiveSpaceOverSchemeProjection r X) ⁻¹ᵁ U.1) :=
  ((tensorPowerTwistOnZIso i (m * d) (mul_pos_of_neZero d hm)).inv.app _).hom.comp
    ((coordTwistSection i U (m * d)).comp (veronesePieceEquiv _ d m).toAddMonoidHom)

/-- The comparison is bijective when `s ↦ s / 1` is bijective in degree `md`. -/
theorem veroneseTwistSection_bijective (d : ℕ) [NeZero d] (U : X.AffineZariskiSite) {m : ℕ}
    (hm : 0 < m)
    (hbij : Function.Bijective (fun a : gradedQuotient (MvPolynomial.homogeneousSubmodule
      (Fin (r + 1)) Γ(X, U.1)) (chartIdeal i U.1 U.2) (m * d) => twistSection (m * d) a (op ⊤))) :
    Function.Bijective (veroneseTwistSection i d U hm) :=
  (bijective_app_of_iso (tensorPowerTwistOnZIso i (m * d) (mul_pos_of_neZero d hm)).symm _).comp
    ((coordTwistSection_bijective i U hbij).comp (veronesePieceEquiv _ d m).bijective)

-- The presentations of `Proj T(U)` in the types of `coordToZ` and `chartTwistIso` differ by
-- auxiliary proof terms; unifying them needs more than the default heartbeats.
set_option maxHeartbeats 1000000 in
open Scheme.AffineZariskiSite in
/-- The comparison commutes with restriction along affine opens `V ⊆ U`. -/
theorem veroneseTwistSection_restrict (d : ℕ) [NeZero d] {U V : X.AffineZariskiSite} (h : V ⟶ U)
    {m : ℕ} (hm : 0 < m) (y : ((coordinateAlgebra i).veronese d).grading U m) :
    (tensorPowerL i (m * d)).presheaf.map
        (homOfLE ((i ≫ projectiveSpaceOverSchemeProjection r X).preimage_mono
          (toOpens_mono h.le))).op (veroneseTwistSection i d U hm y) =
      veroneseTwistSection i d V hm
        ⟨((coordinateAlgebra i).veronese d).restrict h y,
          ((coordinateAlgebra i).veronese d).map_mem h y.2⟩ := by
  simp only [veroneseTwistSection, AddMonoidHom.coe_comp, Function.comp_apply]
  rw [← hom_app_map, AddEquiv.coe_toAddMonoidHom, AddEquiv.coe_toAddMonoidHom,
    coordTwistSection_restrict i h]
  exact congrArg _ (congrArg _ (Subtype.ext rfl))

/-- `T(U)^{(d)}_m` is a `Γ(X, U)`-submodule of `T(U)^{(d)}`. -/
theorem veronese_structureMap_mul_mem (d : ℕ) [NeZero d] (U : X.AffineZariskiSite) {m : ℕ}
    (a : Γ(X, U.1)) (y : ((coordinateAlgebra i).veronese d).grading U m) :
    ((coordinateAlgebra i).veronese d).structureMap.app (op U) a * y ∈
      ((coordinateAlgebra i).veronese d).grading U m := by
  simpa using SetLike.mul_mem_graded (((coordinateAlgebra i).veronese d).structureMap_mem U a) y.2

-- The presentations of `Proj T(U)` in the types of `coordToZ` and `chartTwistIso` differ by
-- auxiliary proof terms; unifying them needs more than the default heartbeats.
set_option maxHeartbeats 1000000 in
/-- The comparison is `Γ(X, U)`-linear. -/
theorem veroneseTwistSection_structureMap_mul (d : ℕ) [NeZero d] (U : X.AffineZariskiSite)
    {m : ℕ} (hm : 0 < m) (a : Γ(X, U.1)) (y : ((coordinateAlgebra i).veronese d).grading U m) :
    veroneseTwistSection i d U hm ⟨_, veronese_structureMap_mul_mem i d U a y⟩ =
      (i ≫ projectiveSpaceOverSchemeProjection r X).app U.1 a •
        veroneseTwistSection i d U hm y := by
  simp only [veroneseTwistSection, AddMonoidHom.coe_comp, Function.comp_apply,
    AddEquiv.coe_toAddMonoidHom]
  rw [← Scheme.Modules.Hom.app_smul, ← coordTwistSection_structureMap_mul]
  exact congrArg _ (congrArg _ (Subtype.ext rfl))

-- The presentations of `Proj T(U)` in the types of `coordToZ` and `chartTwistIso` differ by
-- auxiliary proof terms; unifying them needs more than the default heartbeats.
set_option maxHeartbeats 1000000 in
open Scheme.AffineZariskiSite in
/-- **The section-algebra model of a projective birational morphism, sheaf form** (Hartshorne II,
proof of Theorem 7.17, Steps 1–3). Let `X` be an integral quasi-compact scheme locally of finite
type over a field `k`, `i : Z ⟶ ℙʳ_X` a closed immersion of an integral scheme, `f = π ∘ i`
sending the generic point of `Z` to that of `X`, and `L = i^* 𝒪(1)`. There is a `d₀` such that for
every `d ≥ d₀` there is a quasi-coherent graded `𝒪_X`-algebra `S` satisfying the hypotheses for
relative Proj (`S₀ = 𝒪_X`, `S₁` coherent, generated by `S₁`) with `Proj_X S ≅ Z` over `X`, together
with isomorphisms `Γ(f⁻¹(U), L^{md}) ≅ S(U)_m` (`U` affine, `m ≥ 1`) compatible with restriction
and `Γ(X, U)`-linear: an isomorphism `f_* L^{md} ≅ S_m` of `𝒪_X`-modules on the affine opens. -/
theorem exists_sectionAlgebraModel_natural (k : Type u) [Field k] [IsIntegral X] [CompactSpace X]
    (pX : X ⟶ Spec (.of k)) [LocallyOfFiniteType pX]
    (hf : (i ≫ projectiveSpaceOverSchemeProjection r X) (genericPoint Z) = genericPoint X) :
    letI : IsNoetherian X :=
      { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian pX }
    ∃ d₀ : ℕ, ∀ (d : ℕ) [NeZero d], d₀ ≤ d → ∃ D : RelativeProjData X,
      ∃ E : ∀ (U : X.AffineZariskiSite) {m : ℕ}, 0 < m →
        Γ(tensorPowerL i (m * d), (i ≫ projectiveSpaceOverSchemeProjection r X) ⁻¹ᵁ U.1) ≃+
          D.algebra.grading U m,
      (∀ (U V : X.AffineZariskiSite) (h : V ⟶ U) {m : ℕ} (hm : 0 < m)
          (s : Γ(tensorPowerL i (m * d), (i ≫ projectiveSpaceOverSchemeProjection r X) ⁻¹ᵁ U.1)),
        (E V hm ((tensorPowerL i (m * d)).presheaf.map
            (homOfLE ((i ≫ projectiveSpaceOverSchemeProjection r X).preimage_mono
              (toOpens_mono h.le))).op s) : D.algebra.obj.obj (op V)) =
          D.algebra.obj.map h.op (E U hm s)) ∧
      (∀ (U : X.AffineZariskiSite) {m : ℕ} (hm : 0 < m) (a : Γ(X, U.1))
          (s : Γ(tensorPowerL i (m * d), (i ≫ projectiveSpaceOverSchemeProjection r X) ⁻¹ᵁ U.1)),
        (E U hm ((i ≫ projectiveSpaceOverSchemeProjection r X).app U.1 a • s) :
            D.algebra.obj.obj (op U)) =
          D.algebra.structureMap.app (op U) a * E U hm s) ∧
      ∃ e : D.relativeProj ≅ Z, e.hom ≫ (i ≫ projectiveSpaceOverSchemeProjection r X) =
        D.projection := by
  let : IsNoetherian X :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian pX }
  obtain ⟨d₀, hd₀⟩ := exists_bound_bijective_twistSection i k pX
  refine ⟨d₀, fun d _ hd => ?_⟩
  have hG : ∀ (U : X.AffineZariskiSite) {m : ℕ} (hm : 0 < m),
      Function.Bijective (veroneseTwistSection i d U hm) := fun U m hm =>
    veroneseTwistSection_bijective i d U hm
      (hd₀ U (m * d) (hd.trans (Nat.le_mul_of_pos_left d hm)))
  refine ⟨sectionAlgebraRelativeProjData i hf d,
    fun U m hm => (AddEquiv.ofBijective (veroneseTwistSection i d U hm) (hG U hm)).symm,
    fun U V h m hm s => ?_, fun U m hm a s => ?_, sectionAlgebraRelativeProjIso i hf d,
    sectionAlgebraRelativeProjIso_hom_comp i hf d⟩
  · have hy := AddEquiv.ofBijective_apply_symm_apply (n := s) (veroneseTwistSection i d U hm)
      (hG U hm)
    have hz := AddEquiv.ofBijective_apply_symm_apply (veroneseTwistSection i d V hm) (hG V hm)
      (n := (tensorPowerL i (m * d)).presheaf.map
        (homOfLE ((i ≫ projectiveSpaceOverSchemeProjection r X).preimage_mono
          (toOpens_mono h.le))).op s)
    have key := veroneseTwistSection_restrict i d h hm
      ((AddEquiv.ofBijective (veroneseTwistSection i d U hm) (hG U hm)).symm s)
    have := (hG V hm).1 (hz.trans ((congrArg (fun t => (tensorPowerL i (m * d)).presheaf.map
        (homOfLE ((i ≫ projectiveSpaceOverSchemeProjection r X).preimage_mono
          (toOpens_mono h.le))).op t) hy.symm).trans key))
    exact congrArg Subtype.val this
  · have hy := AddEquiv.ofBijective_apply_symm_apply (n := s) (veroneseTwistSection i d U hm)
      (hG U hm)
    have hz := AddEquiv.ofBijective_apply_symm_apply (veroneseTwistSection i d U hm) (hG U hm)
      (n := (i ≫ projectiveSpaceOverSchemeProjection r X).app U.1 a • s)
    have key := veroneseTwistSection_structureMap_mul i d U hm a
      ((AddEquiv.ofBijective (veroneseTwistSection i d U hm) (hG U hm)).symm s)
    have := (hG U hm).1 (hz.trans ((congrArg (fun t =>
      (i ≫ projectiveSpaceOverSchemeProjection r X).app U.1 a • t) hy.symm).trans key.symm))
    exact congrArg Subtype.val this

end Comparison

end SectionAlgebraModel

end Hartshorne

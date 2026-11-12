/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.SectionAlgebraUniformBound
import Hartshorne.Scheme.ProjectionFromPoint

/-!
# The section-algebra model as a sheaf of graded algebras

Hartshorne, *Algebraic Geometry*, II, proof of Theorem 7.17, Steps 1–3 (pp. 166–167).
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

end ToSpecZero

end SectionAlgebraModel

end Hartshorne

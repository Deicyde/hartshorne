/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ProjectiveBundleTwist
import Hartshorne.Scheme.ProjectiveGlobalSectionsFinite

/-!
# Degree-`l` sections and the pushforwards of the relative twisting sheaves

Let `S` be a quasi-coherent sheaf of graded `𝒪_X`-algebras, `π : Proj_X S ⟶ X` and `l ≥ 0`.
Over an affine open `U ⊆ X` every `s ∈ S(U)_l` gives the global section `s / 1` of
`𝒪_{Proj S(U)}(l)`, and `π⁻¹(U) = Proj S(U)`. These sections are compatible with restriction to
basic opens, so they glue: for an `𝒪_X`-module `F` with maps `Γ(U, F) → S(U)_l` compatible with
restriction and with the `𝒪_X`-action, a section of `F` over an open `V ⊆ X` gives a section of
`𝒪_{Proj_X S}(l)` over `π⁻¹(V)`. This is a morphism of `𝒪_X`-modules
`F ⟶ π_* 𝒪_{Proj_X S}(l)`.

## Main definitions and results

* `AlgebraicGeometry.Scheme.Modules.isIso_of_forall_exists_bijective`: a morphism of module
  sheaves which is bijective on sections over arbitrarily small neighbourhoods of every point is
  an isomorphism.
* `Hartshorne.ProjTwistMap.twistRestrictHom_app_twistSection`: the comparison of twisting sheaves
  along a graded ring map `φ` sends `s / 1` to `φ(s) / 1`.
* `Hartshorne.ProjTwistMap.twistSection_top_bijective_of_bijective`,
  `Hartshorne.ProjTwistMap.eq_zero_of_bijective`: bijectivity of `s ↦ s / 1` on global sections,
  and vanishing of global sections, transported along graded ring isomorphisms.
* `Hartshorne.QuasiCoherentGradedAlgebra.GradedSectionsMap`: maps `Γ(U, F) → S(U)_l` compatible
  with restriction and with the `𝒪_X`-action.
* `Hartshorne.QuasiCoherentGradedAlgebra.pushforwardTwistHom`: the morphism
  `F ⟶ π_* M` for a module `M` on `Proj_X S` identified with the twisting sheaves on the affine
  pieces, and `pushforwardTwistHom_app_restrict`: over an affine open it is `s ↦ s / 1`.
* `Hartshorne.QuasiCoherentGradedAlgebra.pushforwardTwistHom_app_bijective`: bijectivity on the
  sections over an affine open on which `s ↦ s / 1` is bijective.
* `Hartshorne.QuasiCoherentGradedAlgebra.isZero_pushforward_of_twist_eq_zero`: `π_* M = 0` if the
  twisting sheaves of the affine pieces of a basis have no nonzero global sections.
-/

universe u

open CategoryTheory Opposite TopologicalSpace Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry.Scheme.Modules

/-- **A basis criterion for isomorphisms of module sheaves**: a morphism of `𝒪_X`-modules is an
isomorphism if every point has arbitrarily small open neighbourhoods over which it is bijective
on sections. -/
theorem isIso_of_forall_exists_bijective {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ (x : X) (W : X.Opens), x ∈ W →
      ∃ V : X.Opens, x ∈ V ∧ V ≤ W ∧ Function.Bijective (φ.app V)) :
    IsIso φ := by
  rw [← isIso_iff_of_reflects_iso _ (Scheme.Modules.toPresheaf X), NatTrans.isIso_iff_isIso_app]
  intro U
  let f : (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) ⟶
      ⟨N.presheaf, N.isSheaf⟩ := ⟨φ.mapPresheaf⟩
  refine (ConcreteCategory.isIso_iff_bijective _).2
    (TopCat.Presheaf.app_bijective_of_stalkFunctor_map_bijective f U.unop fun x _ => ?_)
  constructor
  · intro s t hst
    obtain ⟨V, hxV, s, rfl⟩ := M.presheaf.exists_germ_eq s
    obtain ⟨V', hxV', t, rfl⟩ := M.presheaf.exists_germ_eq t
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
      TopCat.Presheaf.stalkFunctor_map_germ_apply] at hst
    obtain ⟨W, hxW, iV, iV', heq⟩ := N.presheaf.germ_eq x hxV hxV' _ _ hst
    obtain ⟨W', hxW', hW'W, hbij⟩ := h x W hxW
    have h1 : φ.app W' (M.presheaf.map (homOfLE (hW'W.trans iV.le)).op s) =
        φ.app W' (M.presheaf.map (homOfLE (hW'W.trans iV'.le)).op t) := by
      have h2 := congrArg (N.presheaf.map (homOfLE hW'W).op) heq
      change N.presheaf.map (homOfLE hW'W).op (N.presheaf.map (homOfLE iV.le).op (φ.app V s)) =
        N.presheaf.map (homOfLE hW'W).op (N.presheaf.map (homOfLE iV'.le).op (φ.app V' t)) at h2
      rw [Scheme.Modules.map_map_homOfLE, Scheme.Modules.map_map_homOfLE] at h2
      rw [Hartshorne.hom_app_map, Hartshorne.hom_app_map]
      exact h2
    have h3 := hbij.1 h1
    rw [← TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE (hW'W.trans iV.le)) x hxW',
      ← TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE (hW'W.trans iV'.le)) x hxW']
    exact congrArg (M.presheaf.germ W' x hxW') h3
  · intro t
    obtain ⟨V, hxV, t, rfl⟩ := N.presheaf.exists_germ_eq t
    obtain ⟨W', hxW', hW'V, hbij⟩ := h x V hxV
    obtain ⟨s, hs⟩ := hbij.2 (N.presheaf.map (homOfLE hW'V).op t)
    refine ⟨M.presheaf.germ W' x hxW' s, ?_⟩
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    change N.presheaf.germ W' x hxW' (φ.app W' s) = _
    rw [hs, TopCat.Presheaf.germ_res_apply]

end AlgebraicGeometry.Scheme.Modules

namespace Hartshorne

open AlgebraicGeometry

/-! ### The sections `s / 1` -/

namespace GradedGlobalSections

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜]

/-- `s ↦ s / 1` is additive. -/
theorem twistSection_add (d : ℕ) (s t : 𝒜 d) (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    twistSection d (s + t) U = twistSection d s U + twistSection d t U := by
  apply Subtype.ext
  funext y
  change twistFraction d y.1 (s + t).2 = twistFraction d y.1 s.2 + twistFraction d y.1 t.2
  apply HomogeneousLocalizedModule.ext
  simp only [HomogeneousLocalizedModule.val_add, twistFraction_val, AddMemClass.coe_add,
    LocalizedModule.mk_add_mk, one_smul, mul_one]

/-- `s ↦ s / 1` sends `0` to `0`. -/
theorem twistSection_zero (d : ℕ) (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    twistSection d (0 : 𝒜 d) U = 0 := by
  apply Subtype.ext
  funext y
  change twistFraction d y.1 (0 : 𝒜 d).2 = 0
  apply HomogeneousLocalizedModule.ext
  simp only [twistFraction_val, ZeroMemClass.coe_zero, LocalizedModule.zero_mk]
  rfl

/-- **Degree-zero elements act through the structure map**: for `c ∈ S₀` and `s ∈ S_d`,
`(c s) / 1 = c · (s / 1)`, where `c` acts as the global function `c / 1` of `Proj S`. -/
theorem twistSection_mul_of_mem_zero (d : ℕ) (c : 𝒜 0) (s : 𝒜 d) (h : (c : A) * s ∈ 𝒜 d) :
    twistSection d ⟨(c : A) * s, h⟩ (op ⊤) =
      ProjectiveGlobalSectionsFinite.degreeZeroToGlobal 𝒜 c • twistSection d s (op ⊤) := by
  apply Subtype.ext
  funext y
  change twistFraction d y.1 h =
    (ProjectiveGlobalSectionsFinite.degreeZeroToGlobal 𝒜 c).1 y • twistFraction d y.1 s.2
  apply HomogeneousLocalizedModule.ext
  rw [HomogeneousLocalizedModule.val_smul, twistFraction_val, twistFraction_val,
    ProjectiveGlobalSectionsFinite.degreeZeroToGlobal_val c y.1, LocalizedModule.mk_smul_mk,
    smul_eq_mul, mul_one]

end GradedGlobalSections

/-! ### Transport along graded ring isomorphisms -/

namespace ProjTwistMap

open HomogeneousIdeal Graded

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- **The comparison of twisting sheaves sends `s / 1` to `φ(s) / 1`**: for a graded `φ : S → T`
whose `Proj` map is an open immersion, the morphism `𝒪_{Proj S}(d)|_{Proj T} ⟶ 𝒪_{Proj T}(d)`
sends the section `s / 1`, `s ∈ S_d`, to `φ(s) / 1`. -/
theorem twistRestrictHom_app_twistSection (φ : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map φ)
    [IsOpenImmersion (Proj.map φ hf)] (d : ℕ) (s : 𝒜 d) (W : (Proj ℬ).Opens) :
    (twistRestrictHom φ hf d).app W
        (GradedGlobalSections.twistSection d s (op (Proj.map φ hf ''ᵁ W))) =
      GradedGlobalSections.twistSection d ⟨φ s, φ.map_mem s.2⟩ (op W) := by
  apply Subtype.ext
  funext y
  rw [twistRestrictHom_app_apply]
  change twistFiber φ d _ (GradedGlobalSections.twistFraction d _ s.2) =
    GradedGlobalSections.twistFraction d y.1 (φ.map_mem s.2)
  rw [GradedGlobalSections.twistFraction, twistFiber_mk]
  simp only [map_one]
  rfl

variable (φ : 𝒜 →+*ᵍ ℬ) (hφ : Function.Bijective φ)
include hφ

omit [AddSubgroupClass σ A] [AddSubgroupClass τ B] [GradedRing 𝒜] [GradedRing ℬ] in
/-- A bijective graded ring map exhibits its target as the localization away from `1`. -/
private lemma isLocalizationAway_one_of_bijective :
    letI := φ.toRingHom.toAlgebra
    IsLocalization.Away (1 : A) B :=
  letI := φ.toRingHom.toAlgebra
  IsLocalization.away_of_isUnit_of_bijective B isUnit_one hφ

private lemma irrelevant_le_of_bijective : ℬ₊ ≤ 𝒜₊.map φ :=
  letI := φ.toRingHom.toAlgebra
  haveI := isLocalizationAway_one_of_bijective φ hφ
  irrelevant_le_map_of_isLocalizationAway (s := (1 : A)) φ SetLike.GradedOne.one_mem
    (fun _ => rfl)

private lemma isIso_projMap_of_bijective (hf : ℬ₊ ≤ 𝒜₊.map φ) :
    IsIso (Proj.map φ hf) :=
  (projIsoOfBijective φ hφ).isIso_hom

private lemma isIso_twistRestrictHom_of_bijective (hf : ℬ₊ ≤ 𝒜₊.map φ) (n : ℤ) :
    haveI := isIso_projMap_of_bijective φ hφ hf
    IsIso (twistRestrictHom φ hf n) :=
  letI := φ.toRingHom.toAlgebra
  haveI := isLocalizationAway_one_of_bijective φ hφ
  haveI := isIso_projMap_of_bijective φ hφ hf
  isIso_twistRestrictHom φ hf n (s := (1 : A)) SetLike.GradedOne.one_mem (fun _ => rfl)

private lemma projMap_image_top (hf : ℬ₊ ≤ 𝒜₊.map φ) :
    haveI := isIso_projMap_of_bijective φ hφ hf
    Proj.map φ hf ''ᵁ ⊤ = ⊤ := by
  have := isIso_projMap_of_bijective φ hφ hf
  rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_of_isIso]

/-- The global sections of `𝒪_{Proj S}(n)` and `𝒪_{Proj T}(n)` correspond under a graded ring
isomorphism `φ : S ≅ T`: the map `Γ(Proj S, 𝒪(n)) → Γ(Proj T, 𝒪(n))` given by the comparison of
twisting sheaves is bijective. -/
private lemma twistTop_bijective (hf : ℬ₊ ≤ 𝒜₊.map φ) (n : ℤ) :
    haveI := isIso_projMap_of_bijective φ hφ hf
    Function.Bijective fun g : Γ(projTwistingSheaf 𝒜 n, ⊤) =>
      (twistRestrictHom φ hf n).app ⊤
        ((projTwistingSheaf 𝒜 n).presheaf.map
          (homOfLE (le_top : Proj.map φ hf ''ᵁ ⊤ ≤ ⊤)).op g) := by
  have := isIso_projMap_of_bijective φ hφ hf
  have := isIso_twistRestrictHom_of_bijective φ hφ hf n
  have hres : ∀ {W W' : (Proj 𝒜).Opens} (h : W = W'),
      Function.Bijective ((projTwistingSheaf 𝒜 n).presheaf.map (homOfLE h.le).op) := by
    rintro W _ rfl
    rw [show (homOfLE (le_refl W)) = 𝟙 W from rfl, op_id, CategoryTheory.Functor.map_id]
    exact Function.bijective_id
  exact (ConcreteCategory.bijective_of_isIso ((twistRestrictHom φ hf n).app ⊤)).comp
    (hres (projMap_image_top φ hφ hf))

/-- **`s ↦ s / 1` on global sections, transported along a graded ring isomorphism**: if
`φ : S → T` is a bijective graded ring map and `s ↦ s / 1` is a bijection
`S_d → Γ(Proj S, 𝒪(d))`, then so is `t ↦ t / 1`, `T_d → Γ(Proj T, 𝒪(d))`. -/
theorem twistSection_top_bijective_of_bijective (d : ℕ)
    (h : Function.Bijective fun s : 𝒜 d => GradedGlobalSections.twistSection d s (op ⊤)) :
    Function.Bijective fun t : ℬ d => GradedGlobalSections.twistSection d t (op ⊤) := by
  have hf := irrelevant_le_of_bijective φ hφ
  have := isIso_projMap_of_bijective φ hφ hf
  let φd : 𝒜 d → ℬ d := fun s => ⟨φ s, φ.map_mem s.2⟩
  have hφd : Function.Bijective φd := by
    refine ⟨fun s s' hs => Subtype.ext (hφ.1 (congrArg Subtype.val hs)), fun t => ?_⟩
    obtain ⟨a, ha⟩ := hφ.2 t
    refine ⟨⟨a, ?_⟩, Subtype.ext ha⟩
    have := (gradedInvOfBijective φ hφ).map_mem t.2
    convert this
    exact ((RingEquiv.ofBijective φ.toRingHom hφ).symm_apply_eq.2 ha.symm).symm
  have key : (fun t : ℬ d => GradedGlobalSections.twistSection d t (op ⊤)) ∘ φd =
      (fun g : Γ(projTwistingSheaf 𝒜 d, ⊤) => (twistRestrictHom φ hf d).app ⊤
        ((projTwistingSheaf 𝒜 d).presheaf.map
          (homOfLE (le_top : Proj.map φ hf ''ᵁ ⊤ ≤ ⊤)).op g)) ∘
      (fun s : 𝒜 d => GradedGlobalSections.twistSection d s (op ⊤)) := by
    funext s
    exact (twistRestrictHom_app_twistSection φ hf d s ⊤).symm
  have := (twistTop_bijective φ hφ hf d).comp h
  rw [← key] at this
  exact (Function.Bijective.of_comp_iff _ hφd).1 this

/-- **Vanishing of global sections, transported along a graded ring isomorphism**: if
`φ : S → T` is a bijective graded ring map and `𝒪_{Proj S}(n)` has no nonzero global sections,
neither has `𝒪_{Proj T}(n)`. -/
theorem eq_zero_of_bijective (n : ℤ) (h : ∀ g : Γ(projTwistingSheaf 𝒜 n, ⊤), g = 0)
    (g : Γ(projTwistingSheaf ℬ n, ⊤)) : g = 0 := by
  have hf := irrelevant_le_of_bijective φ hφ
  have := isIso_projMap_of_bijective φ hφ hf
  obtain ⟨g', rfl⟩ := (twistTop_bijective φ hφ hf n).2 g
  dsimp only
  rw [h g', map_zero, map_zero]

end ProjTwistMap

/-! ### The morphism `F ⟶ π_* 𝒪_{Proj_X S}(l)` -/

namespace QuasiCoherentGradedAlgebra

open Scheme.AffineZariskiSite

variable {X : Scheme.{u}} (S : QuasiCoherentGradedAlgebra X) (l : ℕ)

/-- **Degree-`l` sections of a module**: maps `Γ(U, F) → S(U)_l` over the affine opens `U ⊆ X`,
compatible with restriction along the basic open inclusions and with the action of `𝒪_X`. -/
structure GradedSectionsMap (F : X.Modules) where
  /-- The maps `Γ(U, F) → S(U)_l`. -/
  toFun : ∀ U : X.AffineZariskiSite, Γ(F, U.1) →+ S.grading U l
  /-- Compatibility with the action of `Γ(U, 𝒪_X)`, which acts on `S(U)` through the structure
  map. -/
  map_smul : ∀ (U : X.AffineZariskiSite) (r : Γ(X, U.1)) (a : Γ(F, U.1)),
    (toFun U (r • a) : S.obj.obj (op U)) = S.structureMap.app (op U) r * toFun U a
  /-- Compatibility with restriction. -/
  map_restrict : ∀ {U V : X.AffineZariskiSite} (f : U ⟶ V) (a : Γ(F, V.1)),
    (toFun U (F.presheaf.map ((toOpensFunctor X).map f).op a) : S.obj.obj (op U)) =
      S.restrict f (toFun V a)

theorem projι_image_top_eq (U : X.AffineZariskiSite) :
    S.projι U ''ᵁ ⊤ = S.relProjToBase ⁻¹ᵁ U.1 := by
  rw [Scheme.Hom.image_top_eq_opensRange]
  exact (S.relProjToBase_preimage U).symm

theorem projMap_restrict_projι {U V : X.AffineZariskiSite} (f : U ⟶ V) :
    Proj.map (S.restrict f) (S.irrelevant_le f) ≫ S.projι V = S.projι U :=
  colimit.w S.relativeGluingData.functor f

theorem projι_image_le {U V : X.AffineZariskiSite} (f : U ⟶ V) :
    S.projι V ''ᵁ (Proj.map (S.restrict f) (S.irrelevant_le f) ''ᵁ ⊤) ≤ S.projι U ''ᵁ ⊤ := by
  rintro _ ⟨_, ⟨y, -, rfl⟩, rfl⟩
  exact ⟨y, trivial, by rw [← S.projMap_restrict_projι f]; rfl⟩

variable {S l}

section Pieces

variable (M : S.relProj.Modules) (α : ∀ U, M.restrict (S.projι U) ≅ S.twistingSheaf (l : ℤ) U)

/-- Compatibility of isomorphisms `M|_{Proj S(U)} ≅ 𝒪_{Proj S(U)}(l)` with the transition maps of
the twisting sheaves along the arrows of affine opens. -/
def TwistCompatible : Prop :=
  ∀ {U V : X.AffineZariskiSite} (f : U ⟶ V) (x : Γ(M, S.projι U ''ᵁ ⊤)),
    (α U).hom.app ⊤ x = (S.twistTransitionHom (l : ℤ) f).app ⊤
      ((α V).hom.app _ (M.presheaf.map (homOfLE (S.projι_image_le f)).op x))

variable (S l) in
/-- The relative twisting sheaf with its restrictions to the affine pieces is compatible with the
transition maps. -/
theorem twistCompatible_relTwistingSheaf :
    TwistCompatible (S.relTwistingSheaf (l : ℤ)) (S.relTwistingSheafRestrictIso (l : ℤ)) :=
  fun f x => (S.twistData (l : ℤ)).ψ_hom_app_top f (S.projMap_restrict_projι f)
    (S.projι_image_le f) x

/-- The section `s / 1` of `𝒪_{Proj S(U)}(l)`, for `s ∈ S(U)_l`, as a section of `M` over the
affine piece `Proj S(U)`. -/
def pieceTwistSection (U : X.AffineZariskiSite) (a : S.grading U l) : Γ(M, S.projι U ''ᵁ ⊤) :=
  (α U).inv.app ⊤ (GradedGlobalSections.twistSection l a (op ⊤))

theorem pieceTwistSection_hom (U : X.AffineZariskiSite) (a : S.grading U l) :
    (α U).hom.app ⊤ (pieceTwistSection M α U a) = GradedGlobalSections.twistSection l a (op ⊤) := by
  rw [pieceTwistSection, ← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
    (α U).inv_hom_id, Scheme.Modules.Hom.id_app]
  rfl

theorem pieceTwistSection_add (U : X.AffineZariskiSite) (a b : S.grading U l) :
    pieceTwistSection M α U (a + b) = pieceTwistSection M α U a + pieceTwistSection M α U b := by
  rw [pieceTwistSection, GradedGlobalSections.twistSection_add, map_add]
  rfl

theorem pieceTwistSection_zero (U : X.AffineZariskiSite) : pieceTwistSection M α U 0 = 0 := by
  rw [pieceTwistSection, GradedGlobalSections.twistSection_zero, map_zero]

theorem pieceTwistSection_restrict (hα : TwistCompatible M α) {U V : X.AffineZariskiSite}
    (f : U ⟶ V)
    (a : S.grading V l) (hle : S.projι U ''ᵁ ⊤ ≤ S.projι V ''ᵁ ⊤) :
    M.presheaf.map (homOfLE hle).op (pieceTwistSection M α V a) =
      pieceTwistSection M α U ⟨S.restrict f a, S.map_mem f a.2⟩ := by
  apply (ConcreteCategory.bijective_of_isIso ((α U).hom.app ⊤)).1
  rw [pieceTwistSection_hom, hα f,
    DirectedModuleGluing.pmap_map M _ _ (homOfLE (Scheme.Hom.image_mono _ le_top)).op,
    Hartshorne.restrict_iso_hom_app_map, pieceTwistSection_hom]
  exact ProjTwistMap.twistRestrictHom_app_twistSection _ _ l a ⊤

/-- The global function of `Proj S(U)` given by a function on the base: restricting `π^# r` to the
piece over an affine `U ⊆ V` gives the image `r|_U / 1` of `r|_U ∈ Γ(U, 𝒪_X) → S(U)₀`. -/
theorem appIso_hom_relProjToBase_app {U : X.AffineZariskiSite} {V : X.Opens} (hUV : U.1 ≤ V)
    (h : S.projι U ''ᵁ ⊤ ≤ S.relProjToBase ⁻¹ᵁ V) (r : Γ(X, V)) :
    ((S.projι U).appIso ⊤).hom (S.relProj.presheaf.map (homOfLE h).op
        (S.relProjToBase.app V r)) =
      ProjectiveGlobalSectionsFinite.degreeZeroToGlobal (S.grading U)
        (S.toZero U (X.presheaf.map (homOfLE hUV).op r)) := by
  have hg : S.projι U ≫ S.relProjToBase =
      (Proj.toSpecZero (S.grading U) ≫ Spec.map (S.toZero U)) ≫ U.2.fromSpec := by
    rw [projι_relProjToBase, projToOpen_ι, Category.assoc]
  rw [Scheme.Hom.appIso_hom', ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    Scheme.Hom.map_appLE, ← Scheme.Hom.comp_appLE]
  have key : ∀ (g : Proj (S.grading U) ⟶ X)
      (_ : g = (Proj.toSpecZero (S.grading U) ≫ Spec.map (S.toZero U)) ≫ U.2.fromSpec) (e),
      g.appLE V ⊤ e r = ProjectiveGlobalSectionsFinite.degreeZeroToGlobal (S.grading U)
        (S.toZero U (X.presheaf.map (homOfLE hUV).op r)) := by
    rintro _ rfl e
    rw [Scheme.Hom.comp_appLE, IsAffineOpen.fromSpec_app_of_le U.2 V hUV]
    simp only [Category.assoc, Scheme.Hom.map_appLE]
    have htop : ∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z) (e' : (⊤ : Y.Opens) ≤ f ⁻¹ᵁ ⊤),
        f.appLE ⊤ ⊤ e' = f.appTop := by
      intro Y Z f e'
      rw [Scheme.Hom.appLE]
      conv_rhs => rw [← Category.comp_id f.appTop, ← Y.presheaf.map_id]
      rfl
    rw [htop, Scheme.Hom.comp_appTop, ← Category.assoc (Scheme.ΓSpecIso _).inv,
      ← Scheme.ΓSpecIso_inv_naturality]
    rfl
  exact key _ hg _

/-- **Degree-zero elements act through the base**: if `c ∈ Γ(π⁻¹(U), 𝒪)` restricts on the piece
`Proj S(U)` to the image of `r ∈ Γ(U, 𝒪_X)` in `S(U)₀`, then `c · (a / 1) = (r a) / 1`. -/
theorem pieceTwistSection_smul (U : X.AffineZariskiSite) (r : Γ(X, U.1)) (a b : S.grading U l)
    (hb : (b : S.obj.obj (op U)) = S.structureMap.app (op U) r * a)
    (c : Γ(S.relProj, S.projι U ''ᵁ ⊤))
    (hc : ((S.projι U).appIso ⊤).hom c =
      ProjectiveGlobalSectionsFinite.degreeZeroToGlobal (S.grading U) (S.toZero U r)) :
    pieceTwistSection M α U b = c • pieceTwistSection M α U a := by
  obtain ⟨b, hb'⟩ := b
  obtain rfl : b = ((S.toZero U r : S.grading U 0) : S.obj.obj (op U)) * a := hb
  rw [pieceTwistSection, pieceTwistSection,
    GradedGlobalSections.twistSection_mul_of_mem_zero l (S.toZero U r) a hb',
    Scheme.Modules.Hom.app_smul, ← hc]
  exact (Hartshorne.restrictAppIso_inv_smul (S.projι U) M ⊤ c
    ((α U).inv.app ⊤ (GradedGlobalSections.twistSection l a (op ⊤)))).symm

end Pieces

/-- The affine opens of `X` contained in an open `V`. -/
abbrev AffineOpensIn (V : X.Opens) : Type u := {U : X.AffineZariskiSite // U.1 ≤ V}

variable (S) in
theorem projι_image_top_le {V : X.Opens} (U : AffineOpensIn V) :
    S.projι U.1 ''ᵁ ⊤ ≤ S.relProjToBase ⁻¹ᵁ V := by
  rw [projι_image_top_eq]
  exact Scheme.Hom.preimage_mono _ U.2

variable (S) in
theorem preimage_le_iSup (V : X.Opens) :
    S.relProjToBase ⁻¹ᵁ V ≤ ⨆ U : AffineOpensIn V, S.projι U.1 ''ᵁ ⊤ := by
  intro p hp
  obtain ⟨W, hW, hpW, hWV⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hp
  refine Opens.mem_iSup.2 ⟨⟨⟨W, hW⟩, hWV⟩, ?_⟩
  rw [projι_image_top_eq]
  exact hpW

/-- Sections of a module on `Proj_X S` over `π⁻¹(V)` agree if they agree on the affine pieces over
the affine opens contained in `V`. -/
theorem relProj_sections_ext (M : S.relProj.Modules) {V : X.Opens}
    {t t' : Γ(M, S.relProjToBase ⁻¹ᵁ V)}
    (h : ∀ U : AffineOpensIn V, M.presheaf.map (homOfLE (S.projι_image_top_le U)).op t =
      M.presheaf.map (homOfLE (S.projι_image_top_le U)).op t') : t = t' :=
  DirectedModuleGluing.mod_ext M _ (fun U => S.projι_image_top_le U) (S.preimage_le_iSup V) t t' h

section Glue

variable (M : S.relProj.Modules) (α : ∀ U, M.restrict (S.projι U) ≅ S.twistingSheaf (l : ℤ) U)
  {F : X.Modules} (τ : S.GradedSectionsMap l F)

/-- The section `s|_U / 1` of `𝒪_{Proj S(U)}(l)` given by a section `s` of `F` over `V ⊇ U`. -/
def localTwistSection {V : X.Opens} (s : Γ(F, V)) (U : AffineOpensIn V) : Γ(M, S.projι U.1 ''ᵁ ⊤) :=
  pieceTwistSection M α U.1 (τ.toFun U.1 (F.presheaf.map (homOfLE U.2).op s))

theorem localTwistSection_restrict (hα : TwistCompatible M α) {V : X.Opens} (s : Γ(F, V))
    {U W : AffineOpensIn V} (f : W.1 ⟶ U.1) (hle : S.projι W.1 ''ᵁ ⊤ ≤ S.projι U.1 ''ᵁ ⊤) :
    M.presheaf.map (homOfLE hle).op (localTwistSection M α τ s U) =
      localTwistSection M α τ s W := by
  rw [localTwistSection, pieceTwistSection_restrict M α hα f]
  congr 1
  apply Subtype.ext
  change (S.restrict f) _ = _
  rw [← τ.map_restrict f]
  exact congrArg (fun x => ((τ.toFun W.1 x : S.grading W.1 l) : S.obj.obj (op W.1)))
    (DirectedModuleGluing.pmap_map F _ _ _ s)

theorem exists_twistSections_glue (hα : TwistCompatible M α) {V : X.Opens} (s : Γ(F, V)) :
    ∃ t : Γ(M, S.relProjToBase ⁻¹ᵁ V), ∀ U : AffineOpensIn V,
      M.presheaf.map (homOfLE (S.projι_image_top_le U)).op t = localTwistSection M α τ s U := by
  refine DirectedModuleGluing.mod_glue M (fun U : AffineOpensIn V => S.projι U.1 ''ᵁ ⊤)
    (fun U => S.projι_image_top_le U) (S.preimage_le_iSup V)
    (fun U => localTwistSection M α τ s U) ?_
  intro k k'
  have hx : ∀ p : ↥(S.projι k.1 ''ᵁ ⊤ ⊓ S.projι k'.1 ''ᵁ ⊤),
      S.relProjToBase p.1 ∈ k.1.1 ⊓ k'.1.1 := by
    rintro ⟨q, hq⟩
    rw [projι_image_top_eq, projι_image_top_eq] at hq
    exact hq
  choose R T hRT hpR using fun p => exists_basicOpen_le_affine_inter k.1.2 k'.1.2 _ (hx p)
  let W : ↥(S.projι k.1 ''ᵁ ⊤ ⊓ S.projι k'.1 ''ᵁ ⊤) → AffineOpensIn V :=
    fun p => ⟨k.1.basicOpen (R p), (X.basicOpen_le _).trans k.2⟩
  have hW : ∀ p, S.projι (W p).1 ''ᵁ ⊤ = S.relProjToBase ⁻¹ᵁ X.basicOpen (R p) :=
    fun p => S.projι_image_top_eq _
  have h1 : ∀ p, S.projι (W p).1 ''ᵁ ⊤ ≤ S.projι k.1 ''ᵁ ⊤ := fun p => by
    rw [hW, projι_image_top_eq]
    exact Scheme.Hom.preimage_mono _ (X.basicOpen_le _)
  have h2 : ∀ p, S.projι (W p).1 ''ᵁ ⊤ ≤ S.projι k'.1 ''ᵁ ⊤ := fun p => by
    rw [hW, projι_image_top_eq, hRT]
    exact Scheme.Hom.preimage_mono _ (X.basicOpen_le _)
  refine DirectedModuleGluing.mod_ext M (fun p => S.projι (W p).1 ''ᵁ ⊤)
    (fun p => le_inf (h1 p) (h2 p)) ?_ _ _ fun p => ?_
  · intro q hq
    refine Opens.mem_iSup.2 ⟨⟨q, hq⟩, ?_⟩
    change q ∈ S.projι (W ⟨q, hq⟩).1 ''ᵁ ⊤
    rw [hW]
    exact hpR ⟨q, hq⟩
  · rw [DirectedModuleGluing.pmap_map M _ _ (homOfLE (h1 p)).op,
      DirectedModuleGluing.pmap_map M _ _ (homOfLE (h2 p)).op,
      localTwistSection_restrict M α τ hα s (homOfLE (k.1.basicOpen_le (R p))),
      localTwistSection_restrict M α τ hα s (W := W p) (U := k')
        (homOfLE (show (W p).1 ≤ k'.1 from ⟨T p, (hRT p).symm⟩))]

/-- The section of `M` over `π⁻¹(V)` glued from the sections `s|_U / 1` over the affine pieces,
for a section `s` of `F` over `V`. -/
def twistSectionsMap (hα : TwistCompatible M α) (V : X.Opens) (s : Γ(F, V)) :
    Γ(M, S.relProjToBase ⁻¹ᵁ V) :=
  (exists_twistSections_glue M α τ hα s).choose

theorem twistSectionsMap_spec (hα : TwistCompatible M α) {V : X.Opens} (s : Γ(F, V))
    (U : AffineOpensIn V) :
    M.presheaf.map (homOfLE (S.projι_image_top_le U)).op (twistSectionsMap M α τ hα V s) =
      localTwistSection M α τ s U :=
  (exists_twistSections_glue M α τ hα s).choose_spec U

theorem twistSectionsMap_add (hα : TwistCompatible M α) {V : X.Opens} (s s' : Γ(F, V)) :
    twistSectionsMap M α τ hα V (s + s') =
      twistSectionsMap M α τ hα V s + twistSectionsMap M α τ hα V s' := by
  refine relProj_sections_ext M fun U => ?_
  rw [map_add, twistSectionsMap_spec, twistSectionsMap_spec, twistSectionsMap_spec,
    localTwistSection, localTwistSection,
    localTwistSection, map_add, map_add, pieceTwistSection_add]

theorem twistSectionsMap_zero (hα : TwistCompatible M α) (V : X.Opens) :
    twistSectionsMap M α τ hα V 0 = 0 := by
  refine relProj_sections_ext M fun U => ?_
  rw [map_zero, twistSectionsMap_spec, localTwistSection, map_zero, map_zero,
    pieceTwistSection_zero]

theorem twistSectionsMap_restrict (hα : TwistCompatible M α) {V V' : X.Opens} (h : V' ≤ V)
    (s : Γ(F, V)) :
    M.presheaf.map (homOfLE (Scheme.Hom.preimage_mono _ h)).op (twistSectionsMap M α τ hα V s) =
      twistSectionsMap M α τ hα V' (F.presheaf.map (homOfLE h).op s) := by
  refine relProj_sections_ext M fun U => ?_
  rw [DirectedModuleGluing.pmap_map M _ _
      (homOfLE (S.projι_image_top_le (⟨U.1, U.2.trans h⟩ : AffineOpensIn V))).op,
    twistSectionsMap_spec, twistSectionsMap_spec, localTwistSection, localTwistSection,
    DirectedModuleGluing.pmap_map F _ _ (homOfLE (U.2.trans h)).op]

theorem twistSectionsMap_smul (hα : TwistCompatible M α) {V : X.Opens} (r : Γ(X, V)) (s : Γ(F, V)) :
    twistSectionsMap M α τ hα V (r • s) =
      S.relProjToBase.app V r • twistSectionsMap M α τ hα V s := by
  refine relProj_sections_ext M fun U => ?_
  rw [Scheme.Modules.map_smul, twistSectionsMap_spec, twistSectionsMap_spec,
    localTwistSection, localTwistSection,
    Scheme.Modules.map_smul]
  exact pieceTwistSection_smul M α U.1 _ _ _
    (τ.map_smul U.1 (X.presheaf.map (homOfLE U.2).op r) (F.presheaf.map (homOfLE U.2).op s))
    _ (appIso_hom_relProjToBase_app U.2 _ r)

/-- The additive map `Γ(V, F) → Γ(π⁻¹(V), M)`. -/
def twistSectionsAddHom (hα : TwistCompatible M α) (V : X.Opens) :
    Γ(F, V) →+ Γ(M, S.relProjToBase ⁻¹ᵁ V) where
  toFun := twistSectionsMap M α τ hα V
  map_zero' := twistSectionsMap_zero M α τ hα V
  map_add' := twistSectionsMap_add M α τ hα

/-- **The morphism `F ⟶ π_* M`**: a section `s` of `F` over `V` goes to the section of `M` over
`π⁻¹(V)` which on the piece `Proj S(U)` over each affine `U ⊆ V` is `s|_U / 1`. -/
def pushforwardTwistHom (hα : TwistCompatible M α) :
    F ⟶ (Scheme.Modules.pushforward S.relProjToBase).obj M :=
  ⟨PresheafOfModules.homMk
    { app := fun V => AddCommGrpCat.ofHom (twistSectionsAddHom M α τ hα V.unop)
      naturality := fun V V' i => by
        ext s
        exact (twistSectionsMap_restrict M α τ hα (leOfHom i.unop) s).symm }
    fun V r s => twistSectionsMap_smul M α τ hα r s⟩

theorem pushforwardTwistHom_app (hα : TwistCompatible M α) (V : X.Opens) (s : Γ(F, V)) :
    (pushforwardTwistHom M α τ hα).app V s = twistSectionsMap M α τ hα V s :=
  rfl

/-- **Over an affine open the morphism is `s ↦ s / 1`**: for an affine open `U ⊆ V`, the section
of `M` attached to `s ∈ Γ(V, F)`, restricted to the piece `Proj S(U)`, is `s|_U / 1`. -/
theorem pushforwardTwistHom_app_restrict (hα : TwistCompatible M α) {V : X.Opens}
    (U : X.AffineZariskiSite) (hUV : U.1 ≤ V) (s : Γ(F, V)) :
    (α U).hom.app ⊤ (M.presheaf.map (homOfLE (S.projι_image_top_le ⟨U, hUV⟩)).op
        ((pushforwardTwistHom M α τ hα).app V s)) =
      GradedGlobalSections.twistSection l (τ.toFun U (F.presheaf.map (homOfLE hUV).op s))
        (op ⊤) := by
  rw [pushforwardTwistHom_app, twistSectionsMap_spec, localTwistSection, pieceTwistSection_hom]

/-- **Bijectivity over an affine open**: if `Γ(U, F) → S(U)_l` and `s ↦ s / 1`,
`S(U)_l → Γ(Proj S(U), 𝒪(l))`, are bijective, then so is `Γ(U, F) → Γ(π⁻¹(U), M)`. -/
theorem pushforwardTwistHom_app_bijective (hα : TwistCompatible M α) (U : X.AffineZariskiSite)
    (hτ : Function.Bijective (τ.toFun U))
    (hU : Function.Bijective fun a : S.grading U l =>
      GradedGlobalSections.twistSection l a (op ⊤)) :
    Function.Bijective ((pushforwardTwistHom M α τ hα).app U.1) := by
  have hres : ∀ {W W' : S.relProj.Opens} (h : W = W'),
      Function.Bijective (M.presheaf.map (homOfLE h.le).op) := by
    rintro W _ rfl
    rw [show (homOfLE (le_refl W)) = 𝟙 W from rfl, op_id, CategoryTheory.Functor.map_id]
    exact Function.bijective_id
  have hresF : Function.Bijective (F.presheaf.map (homOfLE (le_refl U.1)).op) := by
    rw [show (homOfLE (le_refl U.1)) = 𝟙 U.1 from rfl, op_id, CategoryTheory.Functor.map_id]
    exact Function.bijective_id
  have key : (fun s => (α U).hom.app ⊤ (M.presheaf.map
      (homOfLE (S.projι_image_top_le ⟨U, le_refl U.1⟩)).op
        ((pushforwardTwistHom M α τ hα).app U.1 s))) =
      (fun a : S.grading U l => GradedGlobalSections.twistSection l a (op ⊤)) ∘ τ.toFun U ∘
        F.presheaf.map (homOfLE (le_refl U.1)).op := by
    funext s
    exact pushforwardTwistHom_app_restrict M α τ hα U (le_refl U.1) s
  have h := hU.comp (hτ.comp hresF)
  rw [← key] at h
  have h' : Function.Bijective (((α U).hom.app ⊤) ∘
      (M.presheaf.map (homOfLE (S.projι_image_top_le ⟨U, le_refl U.1⟩)).op) ∘
        ((pushforwardTwistHom M α τ hα).app U.1)) := h
  exact (Function.Bijective.of_comp_iff' (hres (S.projι_image_top_eq U)) _).1
    ((Function.Bijective.of_comp_iff'
      (ConcreteCategory.bijective_of_isIso ((α U).hom.app ⊤)) _).1 h')

end Glue

/-- **Vanishing of `π_* M`**: if `M` is identified with the twisting sheaves `𝒪_{Proj S(U)}(n)`
on the affine pieces, and every point of `X` has arbitrarily small affine neighbourhoods `U` with
`Γ(Proj S(U), 𝒪(n)) = 0`, then `M` has no nonzero sections over any `π⁻¹(V)`. -/
theorem eq_zero_of_twist_eq_zero {n : ℤ} (M : S.relProj.Modules)
    (α : ∀ U, M.restrict (S.projι U) ≅ S.twistingSheaf n U)
    (h : ∀ (x : X) (W : X.Opens), x ∈ W → ∃ U : X.AffineZariskiSite, x ∈ U.1 ∧ U.1 ≤ W ∧
      Subsingleton Γ(S.twistingSheaf n U, ⊤))
    (V : X.Opens) (t : Γ(M, S.relProjToBase ⁻¹ᵁ V)) : t = 0 := by
  have hcov : S.relProjToBase ⁻¹ᵁ V ≤
      ⨆ U : {U : AffineOpensIn V // Subsingleton Γ(S.twistingSheaf n U.1, ⊤)},
        S.projι U.1.1 ''ᵁ ⊤ := by
    intro p hp
    have hp' : S.relProjToBase p ∈ V := hp
    have hU := h _ V hp'
    obtain ⟨U, hpU, hUV, hU⟩ := hU
    refine Opens.mem_iSup.2 ⟨⟨⟨U, hUV⟩, hU⟩, ?_⟩
    rw [projι_image_top_eq]
    exact hpU
  let κ : Type u := {U : AffineOpensIn V // Subsingleton Γ(S.twistingSheaf n U.1, ⊤)}
  let Wf : κ → S.relProj.Opens := fun U => S.projι U.1.1 ''ᵁ ⊤
  have hWf : ∀ U : κ, Wf U ≤ S.relProjToBase ⁻¹ᵁ V := fun U => S.projι_image_top_le U.1
  have key : ∀ U : κ, M.presheaf.map (homOfLE (hWf U)).op t =
      M.presheaf.map (homOfLE (hWf U)).op 0 := by
    intro U
    have := U.2
    have : Subsingleton Γ(M.restrict (S.projι U.1.1), ⊤) :=
      (ConcreteCategory.bijective_of_isIso ((α U.1.1).hom.app ⊤)).1.subsingleton
    have : Subsingleton Γ(M, S.projι U.1.1 ''ᵁ ⊤) :=
      (ConcreteCategory.bijective_of_isIso (M.restrictAppIso (S.projι U.1.1) ⊤).inv).1.subsingleton
    exact Subsingleton.elim _ _
  exact DirectedModuleGluing.mod_ext M Wf hWf hcov t 0 key

/-- **Vanishing of `π_* M`**: under the hypotheses of `eq_zero_of_twist_eq_zero`, `π_* M = 0`. -/
theorem isZero_pushforward_of_twist_eq_zero {n : ℤ} (M : S.relProj.Modules)
    (α : ∀ U, M.restrict (S.projι U) ≅ S.twistingSheaf n U)
    (h : ∀ (x : X) (W : X.Opens), x ∈ W → ∃ U : X.AffineZariskiSite, x ∈ U.1 ∧ U.1 ≤ W ∧
      Subsingleton Γ(S.twistingSheaf n U, ⊤)) :
    IsZero ((Scheme.Modules.pushforward S.relProjToBase).obj M) := by
  rw [IsZero.iff_id_eq_zero]
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  ext t
  exact eq_zero_of_twist_eq_zero M α h V t

end QuasiCoherentGradedAlgebra

end Hartshorne

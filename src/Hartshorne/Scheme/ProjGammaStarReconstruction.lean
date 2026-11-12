/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.GradedGlobalSections
import Hartshorne.Scheme.InvertibleSectionClearingDenominators
import Hartshorne.Scheme.SerreGlobalGeneration

/-!
# Reconstruction of a quasi-coherent sheaf on `Proj` from `Γ_*`

Hartshorne, *Algebraic Geometry*, II, Proposition 5.15 (p. 119).

Work in progress: building blocks.
-/

universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Hartshorne

open AlgebraicGeometry CategoryTheory MonoidalCategory HomogeneousLocalization TopologicalSpace
  Opposite

namespace GammaStarReconstruction

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜]

open ProjGradedModuleSheaf GradedGlobalSections Ringed

/-! ### Dividing by a homogeneous element -/

theorem exists_divFraction {d : ℕ} {g : A} (hg : g ∈ 𝒜 d) (x : ProjectiveSpectrum 𝒜)
    (hgx : g ∉ x.asHomogeneousIdeal)
    (z : HomogeneousLocalizedModule 𝒜 (gradedTwist 𝒜 d)
      x.asHomogeneousIdeal.toIdeal.primeCompl) :
    ∃ a : HomogeneousLocalization.AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal,
      a.val = Localization.mk 1 ⟨g, hgx⟩ * (show Localization _ from z.val) := by
  obtain ⟨j, c, hc, s, hs, hsx, rfl⟩ := HomogeneousLocalizedModule.mk_surjective z
  have hc' : c ∈ 𝒜 (d + j) := (mem_gradedTwist_of_eq (by push_cast; ring)).1 hc
  refine ⟨HomogeneousLocalization.mk ⟨d + j, ⟨c, hc'⟩, ⟨g * s, SetLike.GradedMul.mul_mem hg hs⟩,
    x.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem hgx hsx⟩, ?_⟩
  rw [HomogeneousLocalization.val_mk, HomogeneousLocalizedModule.val_mk]
  change Localization.mk c _ = Localization.mk 1 _ * Localization.mk c _
  rw [Localization.mk_mul, one_mul]
  rfl

/-- For `g ∈ S_d` outside `x`, division by `g`, `S(d)_(x) → S_(x)`. -/
def divFraction {d : ℕ} {g : A} (hg : g ∈ 𝒜 d) (x : ProjectiveSpectrum 𝒜)
    (hgx : g ∉ x.asHomogeneousIdeal)
    (z : HomogeneousLocalizedModule 𝒜 (gradedTwist 𝒜 d)
      x.asHomogeneousIdeal.toIdeal.primeCompl) :
    HomogeneousLocalization.AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal :=
  (exists_divFraction hg x hgx z).choose

theorem val_divFraction {d : ℕ} {g : A} (hg : g ∈ 𝒜 d) (x : ProjectiveSpectrum 𝒜)
    (hgx : g ∉ x.asHomogeneousIdeal)
    (z : HomogeneousLocalizedModule 𝒜 (gradedTwist 𝒜 d)
      x.asHomogeneousIdeal.toIdeal.primeCompl) :
    (divFraction hg x hgx z).val = Localization.mk 1 ⟨g, hgx⟩ * (show Localization _ from z.val) :=
  (exists_divFraction hg x hgx z).choose_spec

theorem divFraction_mk {d : ℕ} {g : A} (hg : g ∈ 𝒜 d) (x : ProjectiveSpectrum 𝒜)
    (hgx : g ∉ x.asHomogeneousIdeal) (j : ℕ) (c : A) (hc : c ∈ 𝒜 (d + j)) (s : A)
    (hs : s ∈ 𝒜 j) (hsx : s ∈ x.asHomogeneousIdeal.toIdeal.primeCompl)
    (hc' : c ∈ gradedTwist 𝒜 d j) :
    divFraction hg x hgx (HomogeneousLocalizedModule.mk j c hc' s hs hsx) =
      HomogeneousLocalization.mk ⟨d + j, ⟨c, hc⟩, ⟨g * s, SetLike.GradedMul.mul_mem hg hs⟩,
        x.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem hgx hsx⟩ := by
  apply HomogeneousLocalization.val_injective
  rw [val_divFraction, HomogeneousLocalization.val_mk, HomogeneousLocalizedModule.val_mk]
  change Localization.mk 1 _ * Localization.mk c _ = Localization.mk c _
  rw [Localization.mk_mul, one_mul]
  rfl

/-- `(z / g) · (g / 1) = z`. -/
theorem divFraction_smul_twistFraction {d : ℕ} {g : A} (hg : g ∈ 𝒜 d) (x : ProjectiveSpectrum 𝒜)
    (hgx : g ∉ x.asHomogeneousIdeal)
    (z : HomogeneousLocalizedModule 𝒜 (gradedTwist 𝒜 d)
      x.asHomogeneousIdeal.toIdeal.primeCompl) :
    divFraction hg x hgx z • twistFraction d x hg = z := by
  ext
  rw [HomogeneousLocalizedModule.val_smul, val_divFraction, twistFraction_val]
  change (Localization.mk 1 ⟨g, hgx⟩ * (show Localization _ from z.val)) *
    Localization.mk g 1 = (show Localization _ from z.val)
  rw [mul_comm, ← mul_assoc, Localization.mk_mul, one_mul, mul_one,
    Localization.mk_self ⟨g, hgx⟩, one_mul]

theorem eq_of_smul_twistFraction_eq {d : ℕ} {g : A} (hg : g ∈ 𝒜 d) (x : ProjectiveSpectrum 𝒜)
    (hgx : g ∉ x.asHomogeneousIdeal)
    {a b : HomogeneousLocalization.AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal}
    (h : a • twistFraction d x hg = b • twistFraction d x hg) : a = b := by
  have h' := congrArg HomogeneousLocalizedModule.val h
  rw [HomogeneousLocalizedModule.val_smul, HomogeneousLocalizedModule.val_smul,
    twistFraction_val] at h'
  change a.val * Localization.mk g 1 = b.val * Localization.mk g 1 at h'
  apply HomogeneousLocalization.val_injective
  have hu : IsUnit (Localization.mk g 1 : Localization x.asHomogeneousIdeal.toIdeal.primeCompl) :=
    by
      refine isUnit_iff_exists_inv.2 ⟨Localization.mk 1 ⟨g, hgx⟩, ?_⟩
      rw [Localization.mk_mul, one_mul, mul_one]
      exact Localization.mk_self ⟨g, hgx⟩
  exact hu.mul_right_cancel h'


/-! ### The section `g / 1` trivializes `𝒪_X(d)` on `D₊(g)` -/

theorem twistingSheaf_smul_apply {n : ℤ} {V : (Proj 𝒜).Opens}
    (a : Γ(Proj 𝒜, V)) (t : Γ(projTwistingSheaf 𝒜 n, V)) (y : V) :
    (((a • t : Γ(projTwistingSheaf 𝒜 n, V)) : (projTwistingSheaf 𝒜 n).val.obj (op V)) :
        (sheafInType 𝒜 (gradedTwist 𝒜 n)).1.obj (op V)).1 y =
      a.1 y • ((t : (projTwistingSheaf 𝒜 n).val.obj (op V)) :
        (sheafInType 𝒜 (gradedTwist 𝒜 n)).1.obj (op V)).1 y := rfl

/-- **The section `g / 1` of `𝒪_X(d)` trivializes `𝒪_X(d)` on `D₊(g)`**, for `g ∈ S_d`: every
section of `𝒪_X(d)` over an open `V ⊆ D₊(g)` is uniquely `a · g / 1`, with `a = t / g`. -/
theorem isTrivializingSection_twistSection {d : ℕ} (g : 𝒜 d) :
    IsTrivializingSection (projTwistingSheaf 𝒜 d) (Proj.basicOpen 𝒜 (g : A))
      (twistSection d g (op (Proj.basicOpen 𝒜 (g : A)))) := by
  intro V hV
  refine ⟨fun a b hab => ?_, fun t => ?_⟩
  · apply Subtype.ext
    funext y
    apply eq_of_smul_twistFraction_eq g.2 y.1 (hV y.2)
    have := congrArg (fun t : Γ(projTwistingSheaf 𝒜 d, V) =>
      (t : (sheafInType 𝒜 (gradedTwist 𝒜 d)).1.obj (op V)).1 y) hab
    simp only [twistingSheaf_smul_apply] at this
    exact this
  · refine ⟨⟨fun y => divFraction g.2 y.1 (hV y.2)
      ((t : (sheafInType 𝒜 (gradedTwist 𝒜 d)).1.obj (op V)).1 y), ?_⟩, ?_⟩
    · intro y
      obtain ⟨W, hyW, i, j, c, hc, s, hs, nin, w⟩ :=
        (t : (sheafInType 𝒜 (gradedTwist 𝒜 d)).1.obj (op V)).2 y
      have hc' : c ∈ 𝒜 (d + j) := (mem_gradedTwist_of_eq (by push_cast; ring)).1 hc
      refine ⟨W, hyW, i, d + j, ⟨c, hc'⟩, ⟨g * s, SetLike.GradedMul.mul_mem g.2 hs⟩,
        fun z => ?_, fun z => ?_⟩
      · exact (z.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (hV (i z).2) (nin z))
      · change divFraction g.2 (i z).1 (hV (i z).2)
          ((t : (sheafInType 𝒜 (gradedTwist 𝒜 d)).1.obj (op V)).1 (i z)) = _
        exact (congrArg (divFraction g.2 (i z).1 (hV (i z).2)) (w z)).trans
          (divFraction_mk g.2 _ _ j c hc' s hs _ hc)
    · apply section_ext
      intro y
      exact divFraction_smul_twistFraction g.2 y.1 (hV y.2) _

/-! ### Sections with prescribed germs -/

/-- On a sheaf of modules, a family of germs over `U` which is locally given by sections is the
family of germs of a unique section over `U`. -/
theorem existsUnique_section_of_germ {X : Scheme.{u}} (F : X.Modules) (U : X.Opens)
    (φ : ∀ x : U, F.presheaf.stalk x.1)
    (hφ : ∀ x : U, ∃ (V : X.Opens) (_ : x.1 ∈ V) (hVU : V ≤ U) (t : Γ(F, V)),
      ∀ (y : X) (hy : y ∈ V), F.presheaf.germ V y hy t = φ ⟨y, hVU hy⟩) :
    ∃! t : Γ(F, U), ∀ x : U, F.presheaf.germ U x.1 x.2 t = φ x := by
  let F' : TopCat.Sheaf Ab.{u} X := ⟨F.presheaf, F.isSheaf⟩
  choose V hxV hVU t ht using hφ
  have hcover : U ≤ iSup V := fun x hx => Opens.mem_iSup.2 ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  have hcomp : TopCat.Presheaf.IsCompatible F'.1 V t := by
    intro i j
    apply TopCat.Presheaf.section_ext F'
    intro y hy
    change F.presheaf.germ _ y hy (F.presheaf.map _ (t i)) =
      F.presheaf.germ _ y hy (F.presheaf.map _ (t j))
    rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, ht i y hy.1,
      ht j y hy.2]
  obtain ⟨s, hs, -⟩ := F'.existsUnique_gluing' V U (fun i => homOfLE (hVU i)) hcover t hcomp
  have hgerm : ∀ x : U, F.presheaf.germ U x.1 x.2 s = φ x := by
    intro x
    rw [← TopCat.Presheaf.germ_res_apply F.presheaf (homOfLE (hVU x)) x.1 (hxV x) s]
    change F.presheaf.germ _ x.1 (hxV x) (F'.1.map (homOfLE (hVU x)).op s) = φ x
    rw [hs x, ht x x.1 (hxV x)]
  refine ⟨s, hgerm, fun s' hs' => ?_⟩
  apply TopCat.Presheaf.section_ext F'
  intro y hy
  exact (hs' ⟨y, hy⟩).trans (hgerm ⟨y, hy⟩).symm

/-! ### The sections `m / g` -/

theorem app_bijective_of_iso {X : Scheme.{u}} {F G : X.Modules} (e : F ≅ G)
    (U : X.Opensᵒᵖ) : Function.Bijective (e.hom.val.app U) := by
  refine Function.bijective_iff_has_inverse.2 ⟨e.inv.val.app U, fun x => ?_, fun y => ?_⟩
  · exact congrArg (fun φ : F ⟶ F => (φ.val.app U).hom x) e.hom_inv_id
  · exact congrArg (fun φ : G ⟶ G => (φ.val.app U).hom y) e.inv_hom_id

section Frac

variable (F : (Proj 𝒜).Modules)

/-- Multiplication by the section `g / 1` of `𝒪_X(d)`, `F ⟶ F ⊗ 𝒪_X(d)`, `s ↦ s ⊗ g / 1`. -/
def secMap (d : ℕ) (g : 𝒜 d) : F ⟶ F ⊗ projTwistingSheaf 𝒜 d :=
  (ρ_ F).inv ≫ (F ◁ twistHom d g)

theorem secMap_app (d : ℕ) (g : 𝒜 d) {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}
    (s : F.val.obj U) :
    (secMap F d g).val.app U s = tmulSection _ _ s (twistSection d g U) := by
  change (F ◁ twistHom d g).val.app U ((ρ_ F).inv.val.app U s) = _
  rw [rightUnitor_inv_app, scheme_whiskerLeft_tmulSection, twistHom_app_one]

/-- On opens inside `D₊(g)`, `s ↦ s ⊗ g / 1` is bijective. -/
theorem secMap_app_bijective (d : ℕ) (g : 𝒜 d) {V : (Proj 𝒜).Opens}
    (hV : V ≤ Proj.basicOpen 𝒜 (g : A)) :
    Function.Bijective ((secMap F d g).val.app (op V)) := by
  have h := tensorSectionHom_app_bijective F (projTwistingSheaf 𝒜 d) (twistSection d g (op ⊤))
    (W := Proj.basicOpen 𝒜 (g : A)) (isTrivializingSection_twistSection g) hV
  have key : ⇑((secMap F d g).val.app (op V)) =
      ⇑((moduleSheafTensorIsoTensor F (projTwistingSheaf 𝒜 d)).hom.val.app (op V)) ∘
        ⇑((tensorSectionHom F (projTwistingSheaf 𝒜 d) (twistSection d g (op ⊤))).app V) := by
    funext s
    rw [Function.comp_apply, secMap_app, tensorSectionHom_app]
    exact (moduleSheafTensorIsoTensor_hom_bilinear F (projTwistingSheaf 𝒜 d) s _).symm
  rw [key]
  exact (app_bijective_of_iso _ _).comp h

/-- **The section `m / g` of `F` over `D₊(g)`**, for `m ∈ Γ(X, F(d))` and `g ∈ S_d`: the unique
section with `(m / g) ⊗ g / 1 = m`. -/
def frac (d : ℕ) (g : 𝒜 d) (m : twistGlobal F d) :
    F.val.obj (op (Proj.basicOpen 𝒜 (g : A))) :=
  Function.surjInv (secMap_app_bijective F d g le_rfl).2
    ((F ⊗ projTwistingSheaf 𝒜 d).val.map (homOfLE le_top).op m)

theorem secMap_frac (d : ℕ) (g : 𝒜 d) (m : twistGlobal F d) :
    (secMap F d g).val.app _ (frac F d g m) =
      (F ⊗ projTwistingSheaf 𝒜 d).val.map (homOfLE le_top).op m :=
  Function.surjInv_eq _ _

/-- `m / g` is characterized on every open inside `D₊(g)`. -/
theorem eq_frac_res (d : ℕ) (g : 𝒜 d) (m : twistGlobal F d) {V : (Proj 𝒜).Opens}
    (hV : V ≤ Proj.basicOpen 𝒜 (g : A)) (t : F.val.obj (op V))
    (ht : (secMap F d g).val.app _ t =
      (F ⊗ projTwistingSheaf 𝒜 d).val.map (homOfLE le_top).op m) :
    t = F.val.map (homOfLE hV).op (frac F d g m) := by
  apply (secMap_app_bijective F d g hV).1
  rw [ht, PresheafOfModules.naturality_apply, secMap_frac]
  exact (Scheme.Modules.map_map_homOfLE (F ⊗ projTwistingSheaf 𝒜 d) le_top hV m).symm

theorem twistSection_res (d : ℕ) (g : 𝒜 d) {U V : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}
    (i : U ⟶ V) :
    (projTwistingSheaf 𝒜 d).val.map i (twistSection d g U) = twistSection d g V := rfl

theorem secMap_frac_res (d : ℕ) (g : 𝒜 d) (m : twistGlobal F d) {V : (Proj 𝒜).Opens}
    (hV : V ≤ Proj.basicOpen 𝒜 (g : A)) :
    (secMap F d g).val.app (op V) (F.val.map (homOfLE hV).op (frac F d g m)) =
      (F ⊗ projTwistingSheaf 𝒜 d).val.map (homOfLE le_top).op m := by
  rw [PresheafOfModules.naturality_apply, secMap_frac]
  exact Scheme.Modules.map_map_homOfLE (F ⊗ projTwistingSheaf 𝒜 d) le_top hV m

/-- `(g / 1) · (a / 1) = g a / 1` in `𝒪_X(d + e)`. -/
theorem twistMulHom_twistSection (d e : ℕ) (g : 𝒜 d) (a : 𝒜 e)
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    (twistMulHom 𝒜 d e).val.app U (tmulSection _ _ (twistSection d g U) (twistSection e a U)) =
      twistSection (d + e) ⟨(g : A) * a, SetLike.GradedMul.mul_mem g.2 a.2⟩ U := by
  apply section_ext
  intro x
  apply HomogeneousLocalizedModule.ext
  rw [twistMulHom_tmul_twistSection_apply, twistSection_apply, twistSection_apply,
    twistFraction_val, twistFraction_val]
  rw [LocalizedModule.smul'_mk, smul_eq_mul, mul_comm]

/-- **`m / g = a m / a g`** on `D₊(a g)`, for `a ∈ S_e`. -/
theorem frac_res_mulGlobal (d e : ℕ) (g : 𝒜 d) (a : 𝒜 e) (m : twistGlobal F d)
    {V : (Proj 𝒜).Opens} (hV : V ≤ Proj.basicOpen 𝒜 ((g : A) * a)) :
    F.presheaf.map (homOfLE (hV.trans (ProjectiveSpectrum.basicOpen_mul_le_left 𝒜 _ _))).op
        (frac F d g m) =
      F.presheaf.map (homOfLE hV).op
        (frac F (d + e) ⟨(g : A) * a, SetLike.GradedMul.mul_mem g.2 a.2⟩ (mulGlobal F d e a m)) := by
  refine eq_frac_res F (d + e) ⟨(g : A) * a, SetLike.GradedMul.mul_mem g.2 a.2⟩
    (mulGlobal F d e a m) hV _ ?_
  rw [secMap_app]
  have h1 := secMap_frac_res F d g m (hV.trans (ProjectiveSpectrum.basicOpen_mul_le_left 𝒜 _ _))
  rw [secMap_app] at h1
  change _ = (F ⊗ projTwistingSheaf 𝒜 (d + e)).val.map (homOfLE le_top).op
    ((mulMap F d e a).val.app (op ⊤) m)
  rw [← PresheafOfModules.naturality_apply, ← h1, mulMap_tmulSection, twistMulHom_twistSection]
  rfl

theorem frac_add (d : ℕ) (g : 𝒜 d) (m m' : twistGlobal F d) :
    frac F d g (m + m') = frac F d g m + frac F d g m' := by
  apply (secMap_app_bijective F d g le_rfl).1
  rw [map_add, secMap_frac, secMap_frac, secMap_frac, map_add]
  rfl

theorem frac_zero (d : ℕ) (g : 𝒜 d) : frac F d g 0 = 0 := by
  apply (secMap_app_bijective F d g le_rfl).1
  rw [map_zero, secMap_frac, map_zero]
  rfl

omit [GradedRing 𝒜] in
/-- `(r • f) ⊗ g = f ⊗ (r • g)`, for module sheaves on a ringed space. -/
theorem tmulSection_smul_left_right' {X : TopCat.{u}}
    {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
    {G H : SheafOfModules.{u} (ringCatSheafOf R)} {U : (Opens X)ᵒᵖ}
    (r : (R.obj ⋙ forget₂ CommRingCat RingCat).obj U) (f : G.val.obj U) (g : H.val.obj U) :
    tmulSection G H (r • f) g = tmulSection G H f (r • g) :=
  congrArg ((tensorπ G H).app U).hom (TensorProduct.smul_tmul r f g)

omit [GradedRing 𝒜] in
/-- `(r • f) ⊗ g = f ⊗ (r • g)`, on a scheme. -/
theorem tmulSection_smul_left_right {X : Scheme.{u}} {G H : X.Modules} {U : X.Opens}
    (r : Γ(X, U)) (f : Γ(G, U)) (g : Γ(H, U)) :
    tmulSection G H (r • f : Γ(G, U)) g = tmulSection G H f (r • g : Γ(H, U)) :=
  tmulSection_smul_left_right' (R := X.sheaf) (U := op U) r f g

end Frac

/-- The section `c / h` of `𝒪_X` over `D₊(h)`, for `c, h ∈ S_j`. -/
def ringFrac (j : ℕ) (c h : 𝒜 j) : Γ(Proj 𝒜, Proj.basicOpen 𝒜 (h : A)) :=
  ⟨fun y => HomogeneousLocalization.mk ⟨j, c, h, y.2⟩,
    fun y => ⟨Proj.basicOpen 𝒜 (h : A), y.2, 𝟙 _, j, c, h, fun z => z.2, fun _ => rfl⟩⟩

section Frac

variable (F : (Proj 𝒜).Modules)

/-- **`c m / h g = (c / h) · (m / g)`** on `D₊(g h)`, for `c, h ∈ S_j`. -/
theorem frac_res_mulGlobal_eq_smul (d j : ℕ) (g : 𝒜 d) (c h : 𝒜 j) (m : twistGlobal F d)
    {V : (Proj 𝒜).Opens} (hV : V ≤ Proj.basicOpen 𝒜 ((g : A) * h)) :
    F.presheaf.map (homOfLE hV).op
        (frac F (d + j) ⟨(g : A) * h, SetLike.GradedMul.mul_mem g.2 h.2⟩
          (mulGlobal F d j c m)) =
      ((Proj 𝒜).presheaf.map
          (homOfLE (hV.trans (ProjectiveSpectrum.basicOpen_mul_le_right 𝒜 _ _))).op
          (ringFrac j c h) : Γ(Proj 𝒜, V)) •
        F.presheaf.map (homOfLE (hV.trans (ProjectiveSpectrum.basicOpen_mul_le_left 𝒜 _ _))).op
          (frac F d g m) := by
  symm
  refine eq_frac_res F (d + j) ⟨(g : A) * h, SetLike.GradedMul.mul_mem g.2 h.2⟩
    (mulGlobal F d j c m) hV _ ?_
  have h1 := secMap_frac_res F d g m (hV.trans (ProjectiveSpectrum.basicOpen_mul_le_left 𝒜 _ _))
  rw [secMap_app] at h1
  change _ = (F ⊗ projTwistingSheaf 𝒜 (d + j)).val.map (homOfLE le_top).op
    ((mulMap F d j c).val.app (op ⊤) m)
  rw [← PresheafOfModules.naturality_apply, ← h1, mulMap_tmulSection]
  rw [secMap_app]
  erw [tmulSection_smul_left_right]
  congr 1
  apply section_ext
  intro y
  rw [twistingSheaf_smul_apply]
  apply HomogeneousLocalizedModule.ext
  rw [HomogeneousLocalizedModule.val_smul, twistMulHom_tmul_twistSection_apply,
    twistSection_apply, twistSection_apply, twistFraction_val, twistFraction_val]
  change (HomogeneousLocalization.mk (𝒜 := 𝒜) ⟨j, c, h, ProjectiveSpectrum.basicOpen_mul_le_right 𝒜 _ _ (hV y.2)⟩).val •
      LocalizedModule.mk ((g : A) * h) 1 = (c : A) • LocalizedModule.mk (g : A) 1
  rw [HomogeneousLocalization.val_mk, LocalizedModule.smul'_mk]
  change Localization.mk (c : A) ⟨h, _⟩ * Localization.mk ((g : A) * h) 1 =
    Localization.mk ((c : A) • (g : A)) 1
  rw [Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul, smul_eq_mul]; ring⟩

end Frac

/-! ### `Γ_*(F)` as a graded module and the fractions `m / g` -/

section Graded

variable (F : (Proj 𝒜).Modules)

attribute [local instance] gammaStarModule

/-- The grading of `Γ_*(F) = ⨁ₙ Γ(X, F(n))` by its summands. -/
def gammaStarGrading (n : ℤ) : AddSubgroup (GammaStar F) :=
  (DirectSum.of (fun m => twistGlobal F m) n).range

theorem of_mem_gammaStarGrading (n : ℤ) (y : twistGlobal F n) :
    DirectSum.of (fun m => twistGlobal F m) n y ∈ gammaStarGrading F n :=
  ⟨y, rfl⟩

theorem eq_of_mem_gammaStarGrading {n : ℤ} {z : GammaStar F} (hz : z ∈ gammaStarGrading F n) :
    DirectSum.of (fun m => twistGlobal F m) n (z n) = z := by
  obtain ⟨y, rfl⟩ := hz
  rw [DirectSum.of_eq_same]

instance gammaStarGrading.gradedSMul : SetLike.GradedSMul 𝒜 (gammaStarGrading F) where
  smul_mem := by
    rintro i j a z ha ⟨y, rfl⟩
    rw [smul_of F ha]
    change _ ∈ gammaStarGrading F ((i : ℤ) + j)
    rw [add_comm (i : ℤ) j]
    exact of_mem_gammaStarGrading F _ _

/-- **Hartshorne's `Γ_*(F)~`**: the sheaf on `Proj S` of the graded `S`-module `Γ_*(F)`. -/
def gammaStarTilde : (Proj 𝒜).Modules :=
  projGradedModuleSheaf 𝒜 (gammaStarGrading F)

/-- The fraction `z / g` of `F` over `D₊(g)`, for `z ∈ Γ_*(F)` and `g ∈ S_n`, through the degree
`n` component of `z`. -/
def fracM (n : ℕ) (g : 𝒜 n) (z : GammaStar F) : F.val.obj (op (Proj.basicOpen 𝒜 (g : A))) :=
  frac F n g (z n)

theorem germ_fracM_congr {n n' : ℕ} (hn : n = n') (g : 𝒜 n) (g' : 𝒜 n') (hg : (g : A) = g')
    {z z' : GammaStar F} (hz : z = z') (x : Proj 𝒜) (hx : x ∈ Proj.basicOpen 𝒜 (g : A))
    (hx' : x ∈ Proj.basicOpen 𝒜 (g' : A)) :
    F.presheaf.germ _ x hx (fracM F n g z) = F.presheaf.germ _ x hx' (fracM F n' g' z') := by
  subst hn hz
  obtain rfl : g = g' := Subtype.ext hg
  rfl

theorem smul_apply_of_mem {k e : ℕ} {z : GammaStar F} (hz : z ∈ gammaStarGrading F k)
    (a : 𝒜 e) : (a : A) • z = DirectSum.of (fun m => twistGlobal F m) ((k : ℤ) + e)
      (mulGlobal F k e a (z k)) := by
  conv_lhs => rw [← eq_of_mem_gammaStarGrading F hz]
  exact smul_of F a.2 k (z k)

/-- **`z / g = a z / a g`** at the level of germs, for `z ∈ Γ(X, F(k))` and `a ∈ S_e`. -/
theorem germ_fracM_smul {k e : ℕ} (g : 𝒜 k) (a : 𝒜 e) {z : GammaStar F}
    (hz : z ∈ gammaStarGrading F k) (x : Proj 𝒜)
    (hx : x ∈ Proj.basicOpen 𝒜 ((g : A) * a)) :
    F.presheaf.germ _ x hx (fracM F (k + e) ⟨(g : A) * a, SetLike.GradedMul.mul_mem g.2 a.2⟩
        ((a : A) • z)) =
      F.presheaf.germ _ x (ProjectiveSpectrum.basicOpen_mul_le_left 𝒜 _ _ hx) (fracM F k g z) := by
  have hc : ((a : A) • z) ((k + e : ℕ) : ℤ) = mulGlobal F k e a (z k) := by
    rw [smul_apply_of_mem F hz a]
    exact DirectSum.of_eq_same _ _
  have h := congrArg (F.presheaf.germ _ x hx) (frac_res_mulGlobal F k e g a (z k) le_rfl)
  rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at h
  unfold fracM
  rw [hc]
  exact h.symm

theorem mulGlobal_zero (k : ℤ) (e : ℕ) (y : twistGlobal F k) : mulGlobal F k e 0 y = 0 := by
  change (mulMap F k e 0).val.app (op ⊤) y = 0
  rw [mulMap_zero]
  rfl

/-- If `u z = 0` for a homogeneous `z ∈ Γ_*(F)`, then every homogeneous component of `u` kills
`z`. -/
theorem decompose_smul_eq_zero {k : ℤ} {z : GammaStar F} (hz : z ∈ gammaStarGrading F k) {u : A}
    (hu : u • z = 0) (j : ℕ) : (DirectSum.decompose 𝒜 u j : A) • z = 0 := by
  classical
  obtain ⟨y, rfl⟩ := hz
  have hsum : u • DirectSum.of (fun m => twistGlobal F m) k y =
      ∑ i ∈ (DirectSum.decompose 𝒜 u).support, DirectSum.of (fun m => twistGlobal F m) (k + i)
        (mulGlobal F k i (DirectSum.decompose 𝒜 u i) y) := by
    conv_lhs => rw [← DirectSum.sum_support_decompose 𝒜 u]
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun i _ => smul_of F (DirectSum.decompose 𝒜 u i).2 k y
  rw [smul_of F (DirectSum.decompose 𝒜 u j).2]
  have hcomp := congrArg (fun w : GammaStar F => w (k + j)) (hsum.symm.trans hu)
  simp only [DirectSum.zero_apply] at hcomp
  rw [DFinsupp.finsetSum_apply, Finset.sum_eq_single j] at hcomp
  · rw [DirectSum.of_eq_same] at hcomp
    exact (congrArg (DirectSum.of (fun m => twistGlobal F m) (k + j)) hcomp).trans (map_zero _)
  · intro i _ hij
    exact DirectSum.of_eq_of_ne _ _ _ (by omega)
  · intro hj
    rw [DFinsupp.notMem_support_iff.1 hj, DirectSum.of_eq_same, mulGlobal_zero]

/-- **Equal fractions have equal germs**: if `m / s = m' / s'` in `Γ_*(F)_(x)`, then the sections
`m / s` and `m' / s'` of `F` have the same germ at `x`. -/
theorem germ_fracM_eq_of_mk_eq (x : Proj 𝒜) {n n' : ℕ} {m m' : GammaStar F}
    (hm : m ∈ gammaStarGrading F n) (hm' : m' ∈ gammaStarGrading F n') {s s' : A}
    (hs : s ∈ 𝒜 n) (hs' : s' ∈ 𝒜 n') (hsx : s ∈ x.asHomogeneousIdeal.toIdeal.primeCompl)
    (hsx' : s' ∈ x.asHomogeneousIdeal.toIdeal.primeCompl)
    (h : HomogeneousLocalizedModule.mk n m hm s hs hsx =
      HomogeneousLocalizedModule.mk n' m' hm' s' hs' hsx') :
    F.presheaf.germ (Proj.basicOpen 𝒜 s) x hsx (fracM F n ⟨s, hs⟩ m) =
      F.presheaf.germ (Proj.basicOpen 𝒜 s') x hsx' (fracM F n' ⟨s', hs'⟩ m') := by
  have h' := congrArg HomogeneousLocalizedModule.val h
  simp only [HomogeneousLocalizedModule.val_mk] at h'
  obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.1 h'
  simp only [Submonoid.smul_def] at hu
  have hD : (u : A) • (s' • m - s • m') = 0 := by
    rw [smul_sub, sub_eq_zero]
    exact hu
  have h1 : s' • m ∈ gammaStarGrading F ((n + n' : ℕ) : ℤ) := by
    have := smul_mem_graded_nat 𝒜 (gammaStarGrading F) hs' hm
    rwa [show ((n' : ℕ) : ℤ) + n = ((n + n' : ℕ) : ℤ) by push_cast; ring] at this
  have h2 : s • m' ∈ gammaStarGrading F ((n + n' : ℕ) : ℤ) := by
    have := smul_mem_graded_nat 𝒜 (gammaStarGrading F) hs hm'
    rwa [show ((n : ℕ) : ℤ) + n' = ((n + n' : ℕ) : ℤ) by push_cast; ring] at this
  obtain ⟨j, hj⟩ : ∃ j, (DirectSum.decompose 𝒜 (u : A) j : A) ∉ x.asHomogeneousIdeal := by
    by_contra hcon
    exact u.2 ((x.asHomogeneousIdeal.isHomogeneous.mem_iff).2
      fun i => not_not.1 (not_exists.1 hcon i))
  set t := DirectSum.decompose 𝒜 (u : A) j
  have ht := decompose_smul_eq_zero F (sub_mem h1 h2) hD j
  have heq : ((t : A) * s') • m = ((t : A) * s) • m' := by
    rw [mul_smul, mul_smul, ← sub_eq_zero, ← smul_sub]
    exact ht
  have hx1 : x ∈ Proj.basicOpen 𝒜 (s * ((t : A) * s')) :=
    x.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem hsx
      (x.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem hj hsx')
  have hx2 : x ∈ Proj.basicOpen 𝒜 (s' * ((t : A) * s)) :=
    x.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem hsx'
      (x.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem hj hsx)
  refine ((germ_fracM_smul F ⟨s, hs⟩ ⟨(t : A) * s', SetLike.GradedMul.mul_mem t.2 hs'⟩
    hm x hx1).symm.trans ?_).trans
    (germ_fracM_smul F ⟨s', hs'⟩ ⟨(t : A) * s, SetLike.GradedMul.mul_mem t.2 hs⟩ hm' x hx2)
  exact germ_fracM_congr F (show n + (j + n') = n' + (j + n) by omega)
    ⟨s * ((t : A) * s'), SetLike.GradedMul.mul_mem hs (SetLike.GradedMul.mul_mem t.2 hs')⟩
    ⟨s' * ((t : A) * s), SetLike.GradedMul.mul_mem hs' (SetLike.GradedMul.mul_mem t.2 hs)⟩
    (by simp only; ring) heq x _ _

theorem exists_stalkEval (x : Proj 𝒜)
    (z : HomogeneousLocalizedModule 𝒜 (gammaStarGrading F)
      x.asHomogeneousIdeal.toIdeal.primeCompl) :
    ∃ w : F.presheaf.stalk x, ∀ (n : ℕ) (m : GammaStar F) (hm : m ∈ gammaStarGrading F n)
      (s : A) (hs : s ∈ 𝒜 n) (hsx : s ∈ x.asHomogeneousIdeal.toIdeal.primeCompl),
      z = HomogeneousLocalizedModule.mk n m hm s hs hsx →
        w = F.presheaf.germ (Proj.basicOpen 𝒜 s) x hsx (fracM F n ⟨s, hs⟩ m) := by
  obtain ⟨n, m, hm, s, hs, hsx, rfl⟩ := HomogeneousLocalizedModule.mk_surjective z
  exact ⟨_, fun n' m' hm' s' hs' hsx' h => germ_fracM_eq_of_mk_eq F x hm hm' hs hs' hsx hsx' h⟩

/-- **The evaluation map on stalks**, `Γ_*(F)_(x) → F_x`, `m / s ↦` the germ of `m / s`. -/
def stalkEval (x : Proj 𝒜)
    (z : HomogeneousLocalizedModule 𝒜 (gammaStarGrading F)
      x.asHomogeneousIdeal.toIdeal.primeCompl) : F.presheaf.stalk x :=
  (exists_stalkEval F x z).choose

theorem stalkEval_mk (x : Proj 𝒜) (n : ℕ) (m : GammaStar F) (hm : m ∈ gammaStarGrading F n)
    (s : A) (hs : s ∈ 𝒜 n) (hsx : s ∈ x.asHomogeneousIdeal.toIdeal.primeCompl) :
    stalkEval F x (HomogeneousLocalizedModule.mk n m hm s hs hsx) =
      F.presheaf.germ (Proj.basicOpen 𝒜 s) x hsx (fracM F n ⟨s, hs⟩ m) :=
  (exists_stalkEval F x _).choose_spec n m hm s hs hsx rfl

theorem smul_mem_gammaStarGrading {n n' : ℕ} {s' : A} (hs' : s' ∈ 𝒜 n') {m : GammaStar F}
    (hm : m ∈ gammaStarGrading F n) : s' • m ∈ gammaStarGrading F ((n + n' : ℕ) : ℤ) := by
  have := smul_mem_graded_nat 𝒜 (gammaStarGrading F) hs' hm
  rwa [show ((n' : ℕ) : ℤ) + n = ((n + n' : ℕ) : ℤ) by push_cast; ring] at this

theorem fracM_add (n : ℕ) (g : 𝒜 n) (z z' : GammaStar F) :
    fracM F n g (z + z') = fracM F n g z + fracM F n g z' := by
  unfold fracM
  rw [DirectSum.add_apply, frac_add]

theorem stalkEval_add (x : Proj 𝒜)
    (z z' : HomogeneousLocalizedModule 𝒜 (gammaStarGrading F)
      x.asHomogeneousIdeal.toIdeal.primeCompl) :
    stalkEval F x (z + z') = stalkEval F x z + stalkEval F x z' := by
  obtain ⟨n, m, hm, s, hs, hsx, rfl⟩ := HomogeneousLocalizedModule.mk_surjective z
  obtain ⟨n', m', hm', s', hs', hsx', rfl⟩ := HomogeneousLocalizedModule.mk_surjective z'
  have hsum : HomogeneousLocalizedModule.mk n m hm s hs hsx +
      HomogeneousLocalizedModule.mk n' m' hm' s' hs' hsx' =
      HomogeneousLocalizedModule.mk (n + n') (s' • m + s • m')
        (add_mem (smul_mem_gammaStarGrading F hs' hm)
          (by rw [add_comm n n']; exact smul_mem_gammaStarGrading F hs hm'))
        (s * s') (SetLike.GradedMul.mul_mem hs hs')
        (x.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem hsx hsx') := by
    ext
    simp only [HomogeneousLocalizedModule.val_add, HomogeneousLocalizedModule.val_mk,
      LocalizedModule.mk_add_mk]
    rfl
  rw [hsum, stalkEval_mk, stalkEval_mk, stalkEval_mk, fracM_add]
  erw [map_add]
  congr 1
  · exact germ_fracM_smul F ⟨s, hs⟩ ⟨s', hs'⟩ hm x _
  · refine (germ_fracM_congr F (show n + n' = n' + n by omega)
      ⟨s * s', SetLike.GradedMul.mul_mem hs hs'⟩ ⟨s' * s, SetLike.GradedMul.mul_mem hs' hs⟩
      (mul_comm _ _) rfl x _ ?_).trans (germ_fracM_smul F ⟨s', hs'⟩ ⟨s, hs⟩ hm' x _)
    exact x.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem hsx' hsx

theorem germ_smul_section {V : (Proj 𝒜).Opens} (x : Proj 𝒜) (hx : x ∈ V) (r : Γ(Proj 𝒜, V))
    (t : Γ(F, V)) :
    F.presheaf.germ V x hx (r • t) = (Proj 𝒜).presheaf.germ V x hx r • F.presheaf.germ V x hx t :=
  let M : PresheafOfModules.{u} ((Proj 𝒜).presheaf ⋙ forget₂ CommRingCat RingCat) := F.val
  PresheafOfModules.germ_smul M x V hx r t

theorem germ_ringFrac (j : ℕ) (c h : 𝒜 j) (x : Proj 𝒜) (hx : x ∈ Proj.basicOpen 𝒜 (h : A)) :
    (Proj 𝒜).presheaf.germ _ x hx (ringFrac j c h) =
      stalkRingHomInv 𝒜 x (HomogeneousLocalization.mk ⟨j, c, h, hx⟩) :=
  (RingEquiv.eq_symm_apply _).2 (Proj.stalkIso'_germ 𝒜 _ x hx _)

theorem stalkEval_smul (x : Proj 𝒜)
    (c : HomogeneousLocalization.AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal)
    (z : HomogeneousLocalizedModule 𝒜 (gammaStarGrading F)
      x.asHomogeneousIdeal.toIdeal.primeCompl) :
    stalkEval F x (c • z) = stalkRingHomInv 𝒜 x c • stalkEval F x z := by
  obtain ⟨⟨j, a, h, hh⟩, rfl⟩ := HomogeneousLocalization.mk_surjective c
  obtain ⟨n, m, hm, s, hs, hsx, rfl⟩ := HomogeneousLocalizedModule.mk_surjective z
  have hx : x ∈ Proj.basicOpen 𝒜 (s * (h : A)) :=
    x.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem hsx hh
  have hprod : HomogeneousLocalization.mk ⟨j, a, h, hh⟩ •
      HomogeneousLocalizedModule.mk n m hm s hs hsx =
      HomogeneousLocalizedModule.mk (n + j) ((a : A) • m) (smul_mem_gammaStarGrading F a.2 hm)
        (s * h) (SetLike.GradedMul.mul_mem hs h.2) hx := by
    ext
    rw [HomogeneousLocalizedModule.val_smul, HomogeneousLocalization.val_mk,
      HomogeneousLocalizedModule.val_mk, HomogeneousLocalizedModule.val_mk]
    rw [LocalizedModule.mk_smul_mk]
    congr 1
    exact Subtype.ext (mul_comm _ _)
  rw [hprod, stalkEval_mk, stalkEval_mk]
  have key := congrArg (F.presheaf.germ _ x hx)
    (frac_res_mulGlobal_eq_smul F n j ⟨s, hs⟩ a h (m n) (V := Proj.basicOpen 𝒜 (s * (h : A)))
      le_rfl)
  rw [TopCat.Presheaf.germ_res_apply, germ_smul_section, TopCat.Presheaf.germ_res_apply,
    TopCat.Presheaf.germ_res_apply] at key
  have hc : ((a : A) • m) ((n + j : ℕ) : ℤ) = mulGlobal F n j a (m n) := by
    rw [smul_apply_of_mem F hm a]
    exact DirectSum.of_eq_same _ _
  unfold fracM
  rw [hc, ← germ_ringFrac j a h x hh]
  exact key

end Graded

/-! ### The evaluation morphism `Γ_*(F)~ ⟶ F` -/

section Eval

variable (F : (Proj 𝒜).Modules)

attribute [local instance] gammaStarModule

/-- The value at a point of a section of `Γ_*(F)~`. -/
abbrev secVal {U : (Proj 𝒜).Opens} (s : Γ(gammaStarTilde F, U)) (x : U) :
    HomogeneousLocalizedModule 𝒜 (gammaStarGrading F) x.1.asHomogeneousIdeal.toIdeal.primeCompl :=
  ((s : (gammaStarTilde F).val.obj (op U)) :
    (sheafInType 𝒜 (gammaStarGrading F)).1.obj (op U)).1 x

theorem existsUnique_evalSection {U : (Proj 𝒜).Opens} (s : Γ(gammaStarTilde F, U)) :
    ∃! t : Γ(F, U), ∀ x : U, F.presheaf.germ U x.1 x.2 t = stalkEval F x.1 (secVal F s x) := by
  apply existsUnique_section_of_germ
  intro x
  obtain ⟨V, hxV, i, n, m, hm, g, hg, nin, w⟩ :=
    ((s : (gammaStarTilde F).val.obj (op U)) :
      (sheafInType 𝒜 (gammaStarGrading F)).1.obj (op U)).2 x
  have hVg : V ≤ Proj.basicOpen 𝒜 g := fun y hy => nin ⟨y, hy⟩
  refine ⟨V, hxV, i.le, F.presheaf.map (homOfLE hVg).op (fracM F n ⟨g, hg⟩ m), fun y hy => ?_⟩
  refine (TopCat.Presheaf.germ_res_apply F.presheaf (homOfLE hVg) y hy _).trans ?_
  exact ((congrArg (stalkEval F y) (w ⟨y, hy⟩)).trans (stalkEval_mk F y n m hm g hg _)).symm

/-- The evaluation map on sections over `U`: the section of `F` whose germ at each `x ∈ U` is
`stalkEval` of the value at `x`. -/
def evalSection {U : (Proj 𝒜).Opens} (s : Γ(gammaStarTilde F, U)) : Γ(F, U) :=
  (existsUnique_evalSection F s).exists.choose

theorem germ_evalSection {U : (Proj 𝒜).Opens} (s : Γ(gammaStarTilde F, U)) (x : U) :
    F.presheaf.germ U x.1 x.2 (evalSection F s) = stalkEval F x.1 (secVal F s x) :=
  (existsUnique_evalSection F s).exists.choose_spec x

theorem eq_evalSection {U : (Proj 𝒜).Opens} (s : Γ(gammaStarTilde F, U)) (t : Γ(F, U))
    (ht : ∀ x : U, F.presheaf.germ U x.1 x.2 t = stalkEval F x.1 (secVal F s x)) :
    t = evalSection F s :=
  (existsUnique_evalSection F s).unique ht (germ_evalSection F s)

theorem germ_eq_stalkRingHomInv {U : (Proj 𝒜).Opens} (r : Γ(Proj 𝒜, U)) (x : U) :
    (Proj 𝒜).presheaf.germ U x.1 x.2 r = stalkRingHomInv 𝒜 x.1 (r.1 x) :=
  (RingEquiv.eq_symm_apply _).2 (Proj.stalkIso'_germ 𝒜 _ x.1 x.2 _)

theorem evalSection_add {U : (Proj 𝒜).Opens} (s s' : Γ(gammaStarTilde F, U)) :
    evalSection F (s + s') = evalSection F s + evalSection F s' := by
  refine (eq_evalSection F _ _ fun x => ?_).symm
  erw [map_add, germ_evalSection, germ_evalSection]
  exact (stalkEval_add F x.1 _ _).symm

theorem evalSection_smul {U : (Proj 𝒜).Opens} (r : Γ(Proj 𝒜, U)) (s : Γ(gammaStarTilde F, U)) :
    evalSection F (r • s) = r • evalSection F s := by
  refine (eq_evalSection F _ _ fun x => ?_).symm
  rw [germ_smul_section, germ_evalSection, germ_eq_stalkRingHomInv]
  exact (stalkEval_smul F x.1 _ _).symm

theorem evalSection_res {U V : (Proj 𝒜).Opens} (h : V ≤ U) (s : Γ(gammaStarTilde F, U)) :
    evalSection F ((gammaStarTilde F).presheaf.map (homOfLE h).op s) =
      F.presheaf.map (homOfLE h).op (evalSection F s) := by
  refine (eq_evalSection F _ _ fun x => ?_).symm
  rw [TopCat.Presheaf.germ_res_apply]
  exact germ_evalSection F s ⟨x.1, h x.2⟩

/-- **The evaluation morphism** `Γ_*(F)~ ⟶ F` (Hartshorne II.5, proof of Proposition 5.15): on
`D₊(g)` the section `m / g` of `Γ_*(F)~` goes to the section `m / g` of `F`, the unique section
whose product with `g / 1 ∈ Γ(D₊(g), 𝒪_X(d))` is `m|_{D₊(g)} ∈ Γ(D₊(g), F(d))`. -/
def gammaStarEval : gammaStarTilde F ⟶ F :=
  Ringed.modulesHomMk (R := (Proj 𝒜).sheaf)
    (fun U =>
      { toFun := evalSection F (U := U)
        map_add' := evalSection_add F
        map_smul' := evalSection_smul F })
    (fun _ _ i s => evalSection_res F i s)

theorem gammaStarEval_app {U : (Proj 𝒜).Opens} (s : Γ(gammaStarTilde F, U)) :
    (gammaStarEval F).val.app (op U) s = evalSection F s := rfl

/-- On stalks, the evaluation morphism is `stalkEval` composed with the stalk formula
`Γ_*(F)~_x ≅ Γ_*(F)_(x)`. -/
theorem stalk_gammaStarEval (x : Proj 𝒜) (w : (gammaStarTilde F).presheaf.stalk x) :
    (TopCat.Presheaf.stalkFunctor Ab x).map
        ((SheafOfModules.toSheaf (Proj 𝒜).ringCatSheaf).map (gammaStarEval F)).hom w =
      stalkEval F x (stalkLinearEquiv 𝒜 (gammaStarGrading F) x w) := by
  obtain ⟨U, hxU, s, rfl⟩ := (gammaStarTilde F).presheaf.exists_germ_eq w
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  erw [stalkLinearEquiv_germ]
  exact germ_evalSection F s ⟨x, hxU⟩

/-- If `stalkEval` is bijective at every point, the evaluation morphism is an isomorphism. -/
theorem isIso_gammaStarEval_of_bijective (h : ∀ x : Proj 𝒜, Function.Bijective (stalkEval F x)) :
    IsIso (gammaStarEval F) := by
  have : IsIso ((SheafOfModules.toSheaf.{u} (Proj 𝒜).ringCatSheaf).map (gammaStarEval F)) := by
    apply (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso _).2
    intro x
    rw [ConcreteCategory.isIso_iff_bijective]
    have hfun : ⇑((TopCat.Presheaf.stalkFunctor Ab x).map
        ((SheafOfModules.toSheaf (Proj 𝒜).ringCatSheaf).map (gammaStarEval F)).hom) =
        stalkEval F x ∘ stalkLinearEquiv 𝒜 (gammaStarGrading F) x := by
      funext w
      exact stalk_gammaStarEval F x w
    rw [hfun]
    exact (h x).comp (stalkLinearEquiv 𝒜 (gammaStarGrading F) x).bijective
  have hr : (SheafOfModules.toSheaf.{u} (Proj 𝒜).ringCatSheaf).ReflectsIsomorphisms :=
    inferInstance
  exact hr.reflects (gammaStarEval F)

end Eval

/-! ### Tensor powers of `𝒪_X(e)` and the sections `f^n s` of Lemma 5.14 -/

section TensorPower

theorem pow_mem_mul {e : ℕ} {h : A} (hh : h ∈ 𝒜 e) (N : ℕ) : h ^ N ∈ 𝒜 (e * N) := by
  have := SetLike.pow_mem_graded N hh
  rwa [smul_eq_mul, mul_comm] at this

omit [GradedRing 𝒜] in
/-- `T^{N+1} L ≅ T^N L ⊗ L`, as an isomorphism of `𝒪_X`-modules on a scheme. -/
def succIsoX {X : Scheme.{u}} (L : X.Modules) (N : ℕ) :
    moduleSheafTensorPower (N + 1) L ≅ moduleSheafTensor (moduleSheafTensorPower N L) L :=
  Ringed.moduleSheafTensorPowerSuccIso L N

omit [GradedRing 𝒜] in
/-- `T^0 L ≅ 𝒪_X`, as an isomorphism of `𝒪_X`-modules on a scheme. -/
def zeroIsoX {X : Scheme.{u}} (L : X.Modules) :
    moduleSheafTensorPower 0 L ≅ 𝟙_ X.Modules :=
  Ringed.moduleSheafTensorPowerZeroIso L

omit [GradedRing 𝒜] in
/-- The comparison `moduleSheafTensor F G ≅ F ⊗ G`, on a scheme. -/
def tensorIsoX {X : Scheme.{u}} (F G : X.Modules) : moduleSheafTensor F G ≅ F ⊗ G :=
  moduleSheafTensorIsoTensor F G

omit [GradedRing 𝒜] in
theorem tensorIsoX_hom_bilinear {X : Scheme.{u}} (F G : X.Modules) {U : X.Opens} (f : Γ(F, U))
    (g : Γ(G, U)) :
    (tensorIsoX F G).hom.val.app (op U) ((moduleSheafTensorBilinear F G).app (op U) f g) =
      tmulSection F G f g :=
  moduleSheafTensorIsoTensor_hom_bilinear F G f g

/-- `𝒪_X(e)^{⊗ N} ⟶ 𝒪_X(eN)`, multiplying the factors. -/
def powMap (e : ℕ) : ∀ N : ℕ,
    moduleSheafTensorPower N (projTwistingSheaf 𝒜 e) ⟶ projTwistingSheaf 𝒜 ((e * N : ℕ) : ℤ)
  | 0 => (zeroIsoX (projTwistingSheaf 𝒜 e)).hom ≫ twistHom 0 ⟨1, SetLike.GradedOne.one_mem⟩
  | N + 1 => (succIsoX (projTwistingSheaf 𝒜 e) N).hom ≫
      (tensorIsoX _ _).hom ≫ (powMap e N ▷ projTwistingSheaf 𝒜 e) ≫
        twistMulHom 𝒜 ((e * N : ℕ) : ℤ) e

theorem twistSection_congr {d d' : ℕ} (hd : d = d') (g : 𝒜 d) (g' : 𝒜 d') (hg : (g : A) = g')
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    HEq (twistSection d g U) (twistSection d' g' U) := by
  subst hd
  obtain rfl : g = g' := Subtype.ext hg
  rfl

theorem comp_app_apply {X : Scheme.{u}} {F G H : X.Modules} (f : F ⟶ G) (g : G ⟶ H)
    (U : X.Opensᵒᵖ) (x : F.val.obj U) : (f ≫ g).val.app U x = g.val.app U (f.val.app U x) :=
  rfl

omit [GradedRing 𝒜] in
theorem succIso_tprod {X : Scheme.{u}} (L : X.Modules) (N : ℕ) (U : X.Opens)
    (m : Fin (N + 1) → Γ(L, U)) :
    (succIsoX L N).hom.val.app (op U)
        ((moduleSheafTensorPowerMultilinear (N + 1) L).app (op U) m) =
      (moduleSheafTensorBilinear (moduleSheafTensorPower N L) L).app (op U)
        ((moduleSheafTensorPowerMultilinear N L).app (op U) (Fin.init m)) (m (Fin.last N)) :=
  Ringed.moduleSheafTensorPowerHomEquiv_symm_tprod _ U m

/-- `powMap` sends `h^{⊗ N}` to `h^N`, for `h ∈ S_e`. -/
theorem powMap_tprod (e : ℕ) (h : 𝒜 e) (U : (Proj 𝒜).Opens) : ∀ N : ℕ,
    (powMap e N).val.app (op U)
        ((moduleSheafTensorPowerMultilinear N (projTwistingSheaf 𝒜 e)).app (op U)
          (fun _ => twistSection e h (op U))) =
      twistSection (e * N) ⟨(h : A) ^ N, pow_mem_mul h.2 N⟩ (op U)
  | 0 => by
    change (twistHom 0 ⟨1, SetLike.GradedOne.one_mem⟩).val.app (op U)
      (Ringed.sectionsMap (Ringed.moduleSheafTensorPowerZeroIso (projTwistingSheaf 𝒜 e)).hom U
        ((moduleSheafTensorPowerMultilinear 0 (projTwistingSheaf 𝒜 e)).app (op U) _)) = _
    erw [Ringed.moduleSheafTensorPowerHomEquiv_symm_tprod]
    erw [twistHom_app_one]
    apply section_ext
    intro x
    apply HomogeneousLocalizedModule.ext
    rw [twistSection_apply, twistSection_apply, twistFraction_val, twistFraction_val]
    change LocalizedModule.mk (1 : A) 1 = LocalizedModule.mk ((h : A) ^ 0) 1
    rw [pow_zero]
  | N + 1 => by
    rw [powMap]
    erw [comp_app_apply, comp_app_apply, comp_app_apply]
    erw [succIso_tprod (projTwistingSheaf 𝒜 e) N U (fun _ => twistSection e h (op U))]
    erw [tensorIsoX_hom_bilinear (moduleSheafTensorPower N (projTwistingSheaf 𝒜 e))
      (projTwistingSheaf 𝒜 e)]
    erw [scheme_whiskerRight_tmulSection (powMap e N) (G := projTwistingSheaf 𝒜 e)]
    erw [powMap_tprod e h U N]
    refine (twistMulHom_twistSection (e * N) e ⟨(h : A) ^ N, pow_mem_mul h.2 N⟩ h (op U)).trans ?_
    apply section_ext
    intro x
    apply HomogeneousLocalizedModule.ext
    rw [twistSection_apply, twistSection_apply, twistFraction_val, twistFraction_val]
    change LocalizedModule.mk ((h : A) ^ N * h) 1 = LocalizedModule.mk ((h : A) ^ (N + 1)) 1
    rw [pow_succ]

variable (G : (Proj 𝒜).Modules)

/-- `G ⊗ 𝒪_X(e)^{⊗ N} ⟶ G ⊗ 𝒪_X(eN)`. -/
def powTwistMap (e N : ℕ) :
    tensorPowerTwist G (projTwistingSheaf 𝒜 e) N ⟶ G ⊗ projTwistingSheaf 𝒜 ((e * N : ℕ) : ℤ) :=
  (tensorIsoX G _).hom ≫ (G ◁ powMap e N)

/-- `powTwistMap` sends the section `h^N t` of Lemma 5.14 to `t ⊗ h^N / 1`. -/
theorem powTwistMap_sectionPowSMul (e N : ℕ) (h : 𝒜 e) (U : (Proj 𝒜).Opens) (t : Γ(G, U)) :
    (powTwistMap G e N).val.app (op U)
        (sectionPowSMul G (projTwistingSheaf 𝒜 e) N (twistSection e h (op U)) t) =
      tmulSection _ _ t (twistSection (e * N) ⟨(h : A) ^ N, pow_mem_mul h.2 N⟩ (op U)) := by
  rw [powTwistMap]
  erw [comp_app_apply]
  rw [sectionPowSMul]
  erw [tensorIsoX_hom_bilinear]
  rw [scheme_whiskerLeft_tmulSection]
  exact congrArg (tmulSection _ _ t) (powMap_tprod e h U N)

end TensorPower

/-! ### The nonvanishing locus of `h / 1` and homogeneous basic opens -/

section Nonvanishing

theorem isUnit_mk_iff (x : ProjectiveSpectrum 𝒜) {e : ℕ} (h g : 𝒜 e)
    (hg : (g : A) ∈ x.asHomogeneousIdeal.toIdeal.primeCompl) :
    IsUnit (HomogeneousLocalization.mk ⟨e, h, g, hg⟩ :
        HomogeneousLocalization.AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal) ↔
      (h : A) ∉ x.asHomogeneousIdeal := by
  refine (HomogeneousLocalization.isUnit_iff_isUnit_val 𝒜 _ _).symm.trans ?_
  rw [HomogeneousLocalization.val_mk, Localization.mk_eq_mk']
  exact IsLocalization.AtPrime.isUnit_mk'_iff _ _ _ _

/-- If `S` is generated by `S_1`, the nonvanishing locus of the section `h / 1` of `𝒪_X(e)` is
`D₊(h)`. -/
theorem mem_nonvanishingLocus_twistSection (hgen : Algebra.adjoin (𝒜 0) (𝒜 1 : Set A) = ⊤)
    {e : ℕ} (h : 𝒜 e) (x : Proj 𝒜) :
    x ∈ nonvanishingLocus (projTwistingSheaf 𝒜 e) (twistSection e h (op ⊤)) ↔
      (h : A) ∉ x.asHomogeneousIdeal := by
  obtain ⟨f, f_deg, hfx⟩ := ProjTwistingSheaf.exists_mem_one_notMem hgen x
  let g : 𝒜 e := ⟨f ^ e, by simpa using SetLike.pow_mem_graded e f_deg⟩
  have hx : x ∈ Proj.basicOpen 𝒜 (g : A) := fun hmem => hfx (x.isPrime.mem_of_pow_mem e hmem)
  have he := isTrivializingSection_twistSection g
  obtain ⟨a, ha⟩ := he.exists_eq_smul (twistSection e h (op ⊤))
  rw [he.mem_nonvanishingLocus_iff ha hx, Scheme.mem_basicOpen _ a x hx,
    germ_eq_stalkRingHomInv a ⟨x, hx⟩]
  change IsUnit ((stalkRingEquiv 𝒜 x).symm (a.1 ⟨x, hx⟩)) ↔ _
  rw [isUnit_map_iff]
  have hval := congrArg (fun t : Γ(projTwistingSheaf 𝒜 e, Proj.basicOpen 𝒜 (g : A)) =>
    (t : (sheafInType 𝒜 (gradedTwist 𝒜 e)).1.obj (op (Proj.basicOpen 𝒜 (g : A)))).1 ⟨x, hx⟩) ha
  simp only [twistingSheaf_smul_apply] at hval
  have hax : a.1 ⟨x, hx⟩ = HomogeneousLocalization.mk ⟨e, h, g, hx⟩ := by
    apply eq_of_smul_twistFraction_eq g.2 x hx
    refine (hval.symm.trans ?_)
    ext
    rw [HomogeneousLocalizedModule.val_smul, HomogeneousLocalization.val_mk]
    change LocalizedModule.mk (h : A) 1 = Localization.mk (h : A) ⟨g, hx⟩ *
      Localization.mk (g : A) 1
    rw [Localization.mk_mul]
    refine Localization.mk_eq_mk_iff.2 (Localization.r_iff_exists.2 ⟨1, ?_⟩)
    simp only [OneMemClass.coe_one, one_mul, mul_one]
    ring
  rw [hax]
  exact isUnit_mk_iff x h g hx

/-- Every neighbourhood of a point contains a homogeneous basic open neighbourhood. -/
theorem exists_homogeneous_basicOpen_le (x : Proj 𝒜) (W : (Proj 𝒜).Opens) (hxW : x ∈ W) :
    ∃ (e : ℕ) (h : 𝒜 e), x ∈ Proj.basicOpen 𝒜 (h : A) ∧ Proj.basicOpen 𝒜 (h : A) ≤ W := by
  obtain ⟨_, ⟨r, rfl⟩, hxr, hrW⟩ :=
    (ProjectiveSpectrum.isTopologicalBasis_basic_opens 𝒜).exists_subset_of_mem_open hxW W.isOpen
  obtain ⟨i, hi⟩ : ∃ i, (DirectSum.decompose 𝒜 r i : A) ∉ x.asHomogeneousIdeal := by
    by_contra hcon
    exact hxr ((x.asHomogeneousIdeal.isHomogeneous.mem_iff).2
      fun j => not_not.1 (not_exists.1 hcon j))
  refine ⟨i, DirectSum.decompose 𝒜 r i, hi, fun y hy => hrW ?_⟩
  intro hr
  exact hy ((y.asHomogeneousIdeal.isHomogeneous.mem_iff).1 hr i)

end Nonvanishing

end GammaStarReconstruction

end Hartshorne

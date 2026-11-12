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
    F.val.map (homOfLE (hV.trans (ProjectiveSpectrum.basicOpen_mul_le_left 𝒜 _ _))).op (frac F d g m) =
      F.val.map (homOfLE hV).op
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

end GammaStarReconstruction

end Hartshorne

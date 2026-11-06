/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Topology.Sheaves.AddCommGrpCat

/-!
# Exactness of global sections on an affine scheme

Hartshorne, *Algebraic Geometry*, II.5, Proposition 5.6, pp. 113–114.

Let `X` be an affine scheme and `0 ⟶ F' ⟶ F ⟶ F'' ⟶ 0` a short exact sequence of
`𝒪_X`-modules with `F'` quasi-coherent (no hypothesis on `F` or `F''`). Then the sequence of
global sections `0 ⟶ Γ(X, F') ⟶ Γ(X, F) ⟶ Γ(X, F'') ⟶ 0` of `Γ(X, 𝒪_X)`-modules is exact.

Left exactness holds on every open because the sections functor preserves finite limits. For
surjectivity we follow Hartshorne: on `Spec R`, a global section of `F''` lifts locally on
principal opens (an epimorphism of module sheaves is locally surjective); using Lemma 5.3 for
the quasi-coherent `F'` (sections over `D(f)` are the localization of global sections), for each
such `D(f)` some power `f ^ n` times the section lifts globally, after gluing suitably multiplied
local lifts on a finite principal cover. The elements `r` for which `r` times the section lifts
form an ideal that is contained in no maximal ideal, hence contains `1`. The general affine case
follows by restriction along the isomorphism `Spec Γ(X, 𝒪_X) ≅ X`.
-/

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Limits

namespace Hartshorne

variable {X : Scheme.{u}}

private lemma modules_toSheaf_preservesColimit {K : Type} [SmallCategory K]
    (D : K ⥤ X.Modules) :
    PreservesColimit D (SheafOfModules.toSheaf X.ringCatSheaf : X.Modules ⥤ _) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let D₀ : K ⥤ X.PresheafOfModules := D ⋙ SheafOfModules.forget _
  let D' : K ⥤ X.Modules := D₀ ⋙ PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let e : D ≅ D' := Functor.isoWhiskerLeft D (asIso adj.counit).symm
  have hc₀ := colimit.isColimit D₀
  have : PreservesColimitsOfSize.{0, 0}
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) :=
    adj.leftAdjoint_preservesColimits
  have h1 : PreservesColimit D₀ (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) :=
    inferInstance
  have h2 : PreservesColimit D₀
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj) ⋙
        SheafOfModules.toSheaf X.ringCatSheaf) :=
    preservesColimit_of_natIso D₀
      (PresheafOfModules.sheafificationCompToSheaf (𝟙 X.ringCatSheaf.obj)).symm
  have : PreservesColimit D' (SheafOfModules.toSheaf X.ringCatSheaf : X.Modules ⥤ _) :=
    preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) hc₀)
      (isColimitOfPreserves (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj) ⋙
        SheafOfModules.toSheaf X.ringCatSheaf) hc₀)
  exact preservesColimit_of_iso_diagram _ e.symm

private lemma modules_toSheaf_epi {F G : X.Modules} (g : F ⟶ G) [Epi g] :
    Epi ((SheafOfModules.toSheaf X.ringCatSheaf).map g) := by
  have h := modules_toSheaf_preservesColimit (span g g)
  exact @preserves_epi_of_preservesColimit _ _ _ _
    (SheafOfModules.toSheaf X.ringCatSheaf : X.Modules ⥤ _) _ _ g h ‹Epi g›

/-- An epimorphism of `𝒪_X`-modules is locally surjective on sections. -/
lemma modules_exists_local_lift {F G : X.Modules} (g : F ⟶ G) [Epi g] {U : X.Opens}
    (t : Γ(G, U)) {x : X} (hx : x ∈ U) :
    ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧
      ∃ s : Γ(F, V), g.app V s = G.presheaf.map (homOfLE hVU).op t := by
  have := modules_toSheaf_epi g
  have h := (TopCat.Sheaf.isLocallySurjective_iff_epi
    ((SheafOfModules.toSheaf X.ringCatSheaf).map g)).mpr this
  obtain ⟨V, hVU, ⟨s, hs⟩, hxV⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff _).mp h U t x hx
  exact ⟨V, hVU, hxV, s, hs⟩

/-- A monomorphism of `𝒪_X`-modules is injective on sections. -/
lemma modules_app_injective {F G : X.Modules} (i : F ⟶ G) [Mono i] (U : X.Opens) :
    Function.Injective (i.app U) := by
  let G : X.Modules ⥤ AddCommGrpCat.{u} :=
    Scheme.Modules.toPresheaf X ⋙ (evaluation _ _).obj (op U)
  have hG : PreservesFiniteLimits G := by
    have := PreservesLimitsOfSize.preservesFiniteLimits (Scheme.Modules.toPresheaf X)
    have := PreservesLimitsOfSize.preservesFiniteLimits
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U))
    exact comp_preservesFiniteLimits _ _
  have h : Mono (G.map i) := G.map_mono i
  exact (AddCommGrpCat.mono_iff_injective _).mp h

/-- Sections of a left exact sequence of `𝒪_X`-modules form a left exact sequence. -/
lemma modules_sections_exact {S : ShortComplex X.Modules} (hS : S.Exact) [Mono S.f]
    {U : X.Opens} (s : Γ(S.X₂, U)) (hs : S.g.app U s = 0) :
    ∃ t : Γ(S.X₁, U), S.f.app U t = s := by
  let G : X.Modules ⥤ AddCommGrpCat.{u} :=
    Scheme.Modules.toPresheaf X ⋙ (evaluation _ _).obj (op U)
  have hG : PreservesFiniteLimits G := by
    have := PreservesLimitsOfSize.preservesFiniteLimits (Scheme.Modules.toPresheaf X)
    have := PreservesLimitsOfSize.preservesFiniteLimits
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U))
    exact comp_preservesFiniteLimits _ _
  have : G.Additive := Functor.additive_of_preserves_binary_products _
  have key : PreservesFiniteLimits G → ∀ S : ShortComplex X.Modules,
      S.Exact ∧ Mono S.f → (S.map G).Exact ∧ Mono (G.map S.f) :=
    ((Functor.preservesFiniteLimits_tfae G).out 3 1).mp
  have h := key hG S ⟨hS, inferInstance⟩
  exact (ShortComplex.ab_exact_iff _).mp h.1 s hs


open PrimeSpectrum

variable {R : CommRingCat.{u}}

/-- The principal open `D(f)` of `Spec R`, as an open of the scheme. -/
private abbrev sD (f : R) : (Spec R).Opens := PrimeSpectrum.basicOpen f

/-- Restriction of sections of a module over `Spec R`. -/
private noncomputable abbrev sres (M : (Spec R).Modules) {U V : (Spec R).Opens} (h : V ≤ U)
    (x : Γ(M, U)) : Γ(M, V) :=
  M.presheaf.map (homOfLE h).op x

private lemma sres_sres (M : (Spec R).Modules) {U V W : (Spec R).Opens} (h : V ≤ U)
    (h' : W ≤ V) (x : Γ(M, U)) : sres M h' (sres M h x) = sres M (h'.trans h) x := by
  simp only [sres]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

private lemma sres_smul (M : (Spec R).Modules) {U V : (Spec R).Opens} (h : V ≤ U) (r : R)
    (x : Γ(M, U)) : sres M h (r • x) = r • sres M h x :=
  Scheme.Modules.map_smul_Spec (homOfLE h).op r x

private lemma sres_sub (M : (Spec R).Modules) {U V : (Spec R).Opens} (h : V ≤ U)
    (x y : Γ(M, U)) : sres M h (x - y) = sres M h x - sres M h y :=
  map_sub _ x y

private lemma sres_add (M : (Spec R).Modules) {U V : (Spec R).Opens} (h : V ≤ U)
    (x y : Γ(M, U)) : sres M h (x + y) = sres M h x + sres M h y :=
  map_add _ x y

private lemma sres_zero (M : (Spec R).Modules) {U V : (Spec R).Opens} (h : V ≤ U) :
    sres M h (0 : Γ(M, U)) = 0 :=
  map_zero _

private lemma app_sres {M N : (Spec R).Modules} (φ : M ⟶ N) {U V : (Spec R).Opens} (h : V ≤ U)
    (x : Γ(M, U)) : φ.app V (sres M h x) = sres N h (φ.app U x) := by
  have := ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE h).op) x
  simpa using this

private lemma app_smul_Spec {M N : (Spec R).Modules} (φ : M ⟶ N) {U : (Spec R).Opens} (r : R)
    (x : Γ(M, U)) : φ.app U (r • x) = r • φ.app U x := by
  rw [Scheme.Modules.smul_Spec_def, Scheme.Modules.smul_Spec_def, Scheme.Modules.Hom.app_smul]

section QC

variable (M : (Spec R).Modules) [M.IsQuasicoherent]

private lemma qc_isLocalizedModule (f : R) :
    IsLocalizedModule.Away f
      ((modulesSpecToSheaf.obj M).obj.map (PrimeSpectrum.basicOpen f).leTop.op).hom :=
  (isIso_fromTildeΓ_iff_isLocalizing M).mp inferInstance f

/-- Hartshorne II Lemma 5.3(a) for global sections. -/
private lemma qc_global_kill (f : R) (s : Γ(M, ⊤))
    (hs : sres M (le_top : sD f ≤ ⊤) s = 0) :
    ∃ n : ℕ, f ^ n • s = 0 := by
  have := qc_isLocalizedModule M f
  obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq (r := f)
    (f := ((modulesSpecToSheaf.obj M).obj.map (PrimeSpectrum.basicOpen f).leTop.op).hom)
    (x := s) (y := 0) (by rw [map_zero]; exact hs)
  exact ⟨n, hn.trans (smul_zero _)⟩

/-- Hartshorne II Lemma 5.3(b) for global sections. -/
private lemma qc_global_extend (f : R) (t : Γ(M, sD f)) :
    ∃ (n : ℕ) (s : Γ(M, ⊤)), sres M le_top s = f ^ n • t := by
  have := qc_isLocalizedModule M f
  obtain ⟨n, s, hs⟩ := IsLocalizedModule.Away.surj (r := f)
    (f := ((modulesSpecToSheaf.obj M).obj.map (sD f).leTop.op).hom)
    (show ((modulesSpecToSheaf.obj M).obj.obj (op (sD f)) : Type u) from t)
  exact ⟨n, s, hs.symm⟩

private lemma sD_mul_le (g f : R) : sD (g * f) ≤ sD g :=
  PrimeSpectrum.basicOpen_mul_le_left g f

private lemma sD_mul_le_right (g f : R) : sD (g * f) ≤ sD f :=
  PrimeSpectrum.basicOpen_mul_le_right g f

omit [M.IsQuasicoherent] in
private lemma qc_pow_bijective (g : R) (n : ℕ) {U : (Spec R).Opens} (hU : U ≤ sD g) :
    Function.Bijective (fun x : Γ(M, U) ↦ g ^ n • x) := by
  have h := (Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen (M := M) g hU).pow n
  rw [← map_pow, Module.End.isUnit_iff] at h
  exact h

omit [M.IsQuasicoherent] in
private lemma qc_pow_regular (g : R) (n : ℕ) {U : (Spec R).Opens} (hU : U ≤ sD g) :
    IsSMulRegular Γ(M, U) (g ^ n) :=
  (qc_pow_bijective M g n hU).injective

/-- Hartshorne II Lemma 5.3(a) on a principal open `D(g)`. -/
private lemma qc_local_kill (g f : R) (z : Γ(M, sD g)) (hz : sres M (sD_mul_le g f) z = 0) :
    ∃ n : ℕ, f ^ n • z = 0 := by
  obtain ⟨p, v, hv⟩ := qc_global_extend M g z
  have hv' : sres M (le_top : sD (g * f) ≤ ⊤) v = 0 := by
    rw [← sres_sres M (le_top : sD g ≤ ⊤) (sD_mul_le g f), hv, sres_smul, hz, smul_zero]
  obtain ⟨q, hq⟩ := qc_global_kill M (g * f) v hv'
  refine ⟨q, qc_pow_regular M g (q + p) le_rfl ?_⟩
  have h := congrArg (sres M (le_top : sD g ≤ ⊤)) hq
  rw [sres_smul, hv, sres_zero, smul_smul] at h
  show g ^ (q + p) • (f ^ q • z) = g ^ (q + p) • 0
  rw [smul_smul, smul_zero, ← h]
  congr 1
  ring

/-- Hartshorne II Lemma 5.3(b) on a principal open `D(g)`. -/
private lemma qc_local_extend (g f : R) (u : Γ(M, sD (g * f))) :
    ∃ (n : ℕ) (w : Γ(M, sD g)), sres M (sD_mul_le g f) w = f ^ n • u := by
  obtain ⟨n, v, hv⟩ := qc_global_extend M (g * f) u
  obtain ⟨w, hw⟩ := (qc_pow_bijective M g n le_rfl).surjective (sres M le_top v)
  refine ⟨n, w, qc_pow_regular M g n (sD_mul_le g f) ?_⟩
  change g ^ n • sres M (sD_mul_le g f) w = g ^ n • (f ^ n • u)
  rw [← sres_smul]
  change sres M (sD_mul_le g f) ((fun x : Γ(M, sD g) ↦ g ^ n • x) w) = _
  rw [hw, sres_sres, hv, smul_smul, mul_pow]


end QC

section Core

variable (S : ShortComplex (Spec R).Modules)

private lemma app_comp_eq_zero {U : (Spec R).Opens} (a : Γ(S.X₁, U)) :
    S.g.app U (S.f.app U a) = 0 := by
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, S.zero]
  rfl

variable {S} (hS : S.ShortExact)
include hS

private lemma basic_local_lift (t : Γ(S.X₃, ⊤)) (x : Spec R) :
    ∃ g : R, x ∈ sD g ∧ ∃ s : Γ(S.X₂, sD g), S.g.app (sD g) s = sres S.X₃ le_top t := by
  have : Epi S.g := hS.epi_g
  obtain ⟨V, hVU, hxV, s, hs⟩ := modules_exists_local_lift S.g t
    (show x ∈ (⊤ : (Spec R).Opens) from trivial)
  obtain ⟨_, ⟨g, rfl⟩, hxg, hgV⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hxV V.isOpen
  have hgV' : sD g ≤ V := fun y hy ↦ hgV hy
  refine ⟨g, hxg, sres S.X₂ hgV' s, ?_⟩
  rw [app_sres, hs, sres_sres]

private lemma key_step [S.X₁.IsQuasicoherent] (t : Γ(S.X₃, ⊤)) (f : R) (s : Γ(S.X₂, sD f))
    (hs : S.g.app (sD f) s = sres S.X₃ le_top t) :
    ∃ (n : ℕ) (y : Γ(S.X₂, ⊤)), S.g.app ⊤ y = f ^ n • t := by
  have hexact := hS.exact
  have : Mono S.f := hS.mono_f
  choose g hxg s' hs' using basic_local_lift hS t
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ (sD (g x) : Set (Spec R)))
    (fun x ↦ (sD (g x)).isOpen) (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hxg x⟩)
  let Q : Spec R → ℕ → Prop := fun j n ↦ ∃ w : Γ(S.X₂, sD (g j)),
    S.g.app (sD (g j)) w = f ^ n • sres S.X₃ le_top t ∧
      sres S.X₂ (sD_mul_le (g j) f) w =
        f ^ n • sres S.X₂ (sD_mul_le_right (g j) f) s
  have hQ : ∀ j, ∃ n, Q j n := by
    intro j
    have hd : S.g.app _ (sres S.X₂ (sD_mul_le_right (g j) f) s -
        sres S.X₂ (sD_mul_le (g j) f) (s' j)) = 0 := by
      rw [map_sub, app_sres, app_sres, hs, hs' j, sres_sres, sres_sres, sub_self]
    obtain ⟨u, hu⟩ := modules_sections_exact hexact _ hd
    obtain ⟨n, w', hw'⟩ := qc_local_extend S.X₁ (g j) f u
    refine ⟨n, f ^ n • s' j + S.f.app _ w', ?_, ?_⟩
    · rw [map_add, app_smul_Spec, hs' j, app_comp_eq_zero, add_zero]
    · rw [sres_add, sres_smul, ← app_sres, hw', app_smul_Spec, hu, ← smul_add, add_sub_cancel]
  have hQmono : ∀ j n k, Q j n → Q j (n + k) := by
    rintro j n k ⟨w, h1, h2⟩
    refine ⟨f ^ k • w, ?_, ?_⟩
    · rw [app_smul_Spec, h1, smul_smul, ← pow_add, add_comm k]
    · rw [sres_smul, h2, smul_smul, ← pow_add, add_comm k]
  choose nj hnj using hQ
  have hQN : ∀ j ∈ T, Q j (T.sup nj) := fun j hj ↦ by
    have := hQmono j (nj j) (T.sup nj - nj j) (hnj j)
    rwa [Nat.add_sub_cancel' (Finset.le_sup hj)] at this
  choose w hw1 hw2 using fun j : T ↦ hQN j j.2
  have hP : ∀ j k : T, ∃ m : ℕ, f ^ m • (sres S.X₂ (sD_mul_le (g j) (g k)) (w j) -
      sres S.X₂ (sD_mul_le_right (g j) (g k)) (w k)) = 0 := by
    intro j k
    have hd : S.g.app _ (sres S.X₂ (sD_mul_le (g j) (g k)) (w j) -
        sres S.X₂ (sD_mul_le_right (g j) (g k)) (w k)) = 0 := by
      rw [map_sub, app_sres, app_sres, hw1 j, hw1 k, sres_smul, sres_smul, sres_sres, sres_sres,
        sub_self]
    obtain ⟨z, hz⟩ := modules_sections_exact hexact _ hd
    have h1 : sD (g j * g k * f) ≤ sD (g j * f) := by
      simp only [sD, PrimeSpectrum.basicOpen_mul]
      exact inf_le_inf_right _ inf_le_left
    have h2 : sD (g j * g k * f) ≤ sD (g k * f) := by
      simp only [sD, PrimeSpectrum.basicOpen_mul]
      exact inf_le_inf_right _ inf_le_right
    have hz0 : sres S.X₁ (sD_mul_le (g j * g k) f) z = 0 := by
      apply modules_app_injective S.f
      rw [app_sres, hz, map_zero, sres_sub, sres_sres, sres_sres,
        ← sres_sres S.X₂ (sD_mul_le (g j) f) h1, hw2 j,
        ← sres_sres S.X₂ (sD_mul_le (g k) f) h2, hw2 k, sres_smul, sres_smul, sres_sres,
        sres_sres, sub_self]
    obtain ⟨m, hm⟩ := qc_local_kill S.X₁ (g j * g k) f z hz0
    exact ⟨m, by rw [← hz, ← app_smul_Spec, hm, map_zero]⟩
  choose mjk hmjk using hP
  set Mx := (Finset.univ : Finset (T × T)).sup (fun p ↦ mjk p.1 p.2) with hMx
  have hPM : ∀ j k : T, f ^ Mx • (sres S.X₂ (sD_mul_le (g j) (g k)) (w j) -
      sres S.X₂ (sD_mul_le_right (g j) (g k)) (w k)) = 0 := fun j k ↦ by
    have hle : mjk j k ≤ Mx :=
      Finset.le_sup (f := fun p : T × T ↦ mjk p.1 p.2) (Finset.mem_univ (j, k))
    rw [← Nat.add_sub_cancel' hle, pow_add, mul_comm (f ^ mjk j k), ← smul_smul, hmjk j k,
      smul_zero]
  let F₂ : TopCat.Sheaf AddCommGrpCat.{u} (Spec R) := ⟨S.X₂.presheaf, S.X₂.isSheaf⟩
  let F₃ : TopCat.Sheaf AddCommGrpCat.{u} (Spec R) := ⟨S.X₃.presheaf, S.X₃.isSheaf⟩
  let U : T → (Spec R).Opens := fun j ↦ sD (g j)
  have hcover : (⊤ : (Spec R).Opens) ≤ iSup U := by
    intro x _
    have := hT (Set.mem_univ x)
    simp only [Set.mem_iUnion] at this
    obtain ⟨j, hj, hx⟩ := this
    exact Opens.mem_iSup.mpr ⟨⟨j, hj⟩, hx⟩
  obtain ⟨y, hy, -⟩ := F₂.existsUnique_gluing' U ⊤ (fun j ↦ homOfLE le_top) hcover
    (fun j ↦ f ^ Mx • w j) (by
      intro j k
      change sres S.X₂ inf_le_left (f ^ Mx • w j) = sres S.X₂ inf_le_right (f ^ Mx • w k)
      have hle : U j ⊓ U k ≤ sD (g j * g k) := by
        simp only [U, sD, PrimeSpectrum.basicOpen_mul]
        exact le_rfl
      rw [← sres_sres S.X₂ (sD_mul_le (g j) (g k)) hle,
        ← sres_sres S.X₂ (sD_mul_le_right (g j) (g k)) hle]
      congr 1
      rw [sres_smul, sres_smul, ← sub_eq_zero, ← smul_sub]
      exact hPM j k)
  refine ⟨Mx + T.sup nj, y, ?_⟩
  refine F₃.eq_of_locally_eq' U ⊤ (fun j ↦ homOfLE le_top) hcover _ _ (fun j ↦ ?_)
  change sres S.X₃ le_top (S.g.app ⊤ y) = sres S.X₃ le_top (f ^ (Mx + T.sup nj) • t)
  rw [← app_sres]
  have hyj := hy j
  change sres S.X₂ le_top y = _ at hyj
  rw [hyj, app_smul_Spec, hw1 j, sres_smul, smul_smul, ← pow_add]

private lemma spec_surj [S.X₁.IsQuasicoherent] (t : Γ(S.X₃, ⊤)) :
    ∃ y : Γ(S.X₂, ⊤), S.g.app ⊤ y = t := by
  let I : Ideal R :=
    { carrier := {r | ∃ y : Γ(S.X₂, ⊤), S.g.app ⊤ y = r • t}
      add_mem' := by
        rintro a b ⟨y, hy⟩ ⟨z, hz⟩
        exact ⟨y + z, by rw [map_add, hy, hz, add_smul]⟩
      zero_mem' := ⟨0, by rw [map_zero, zero_smul]⟩
      smul_mem' := by
        rintro c a ⟨y, hy⟩
        exact ⟨c • y, by rw [app_smul_Spec, hy, smul_smul, smul_eq_mul]⟩ }
  have hI : I = ⊤ := by
    by_contra h
    obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I h
    obtain ⟨g, hxg, s, hs⟩ := basic_local_lift hS t (⟨m, hm.isPrime⟩ : PrimeSpectrum R)
    obtain ⟨n, y, hy⟩ := key_step hS t g s hs
    exact hxg (hm.isPrime.mem_of_pow_mem n (hIm ⟨y, hy⟩))
  obtain ⟨y, hy⟩ : (1 : R) ∈ I := hI ▸ Submodule.mem_top
  exact ⟨y, hy.trans (one_smul _ _)⟩

end Core

/-- Restriction along an isomorphism of schemes is an equivalence of module categories. -/
private noncomputable def restrictEquivOfIso {X Y : Scheme.{u}} (e : X ≅ Y) :
    Y.Modules ≌ X.Modules :=
  CategoryTheory.Equivalence.mk (Scheme.Modules.restrictFunctor e.hom)
    (Scheme.Modules.restrictFunctor e.inv)
    (Scheme.Modules.restrictFunctorId.symm ≪≫
      Scheme.Modules.restrictFunctorCongr e.inv_hom_id.symm ≪≫
      Scheme.Modules.restrictFunctorComp e.inv e.hom)
    ((Scheme.Modules.restrictFunctorComp e.hom e.inv).symm ≪≫
      Scheme.Modules.restrictFunctorCongr e.hom_inv_id ≪≫ Scheme.Modules.restrictFunctorId)

private lemma affine_surj {X : Scheme.{u}} [IsAffine X] (S : ShortComplex X.Modules)
    (hS : S.ShortExact) [S.X₁.IsQuasicoherent] (t : Γ(S.X₃, ⊤)) :
    ∃ y : Γ(S.X₂, ⊤), S.g.app ⊤ y = t := by
  let e : Spec Γ(X, ⊤) ≅ X := X.isoSpec.symm
  let Φ : X.Modules ⥤ (Spec Γ(X, ⊤)).Modules := Scheme.Modules.restrictFunctor e.hom
  have : Φ.IsEquivalence := (restrictEquivOfIso e).isEquivalence_functor
  have hS' : (S.map Φ).ShortExact := hS.map_of_exact Φ
  have : (S.map Φ).X₁.IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor e.hom S.X₁
  have htop : e.hom ''ᵁ ⊤ = ⊤ := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_of_isIso]
  obtain ⟨y', hy'⟩ := spec_surj hS'
    (S.X₃.presheaf.map (homOfLE (le_top : e.hom ''ᵁ ⊤ ≤ ⊤)).op t)
  refine ⟨S.X₂.presheaf.map (homOfLE (htop.symm.le : ⊤ ≤ e.hom ''ᵁ ⊤)).op y', ?_⟩
  have h := ConcreteCategory.congr_hom
    (S.g.mapPresheaf.naturality (homOfLE (htop.symm.le : ⊤ ≤ e.hom ''ᵁ ⊤)).op) y'
  simp only [Scheme.Modules.mapPresheaf_app] at h
  refine h.trans ((ConcreteCategory.comp_apply _ _ y').trans ?_)
  refine (congrArg (fun z ↦ S.X₃.presheaf.map (homOfLE (htop.symm.le : ⊤ ≤ e.hom ''ᵁ ⊤)).op z)
    hy').trans ?_
  dsimp only
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  exact (ConcreteCategory.congr_hom (S.X₃.presheaf.map_id _) t)

/-- The global sections functor on `𝒪_X`-modules, valued in `Γ(X, 𝒪_X)`-modules. -/
noncomputable def modulesGlobalSections (X : Scheme.{u}) : X.Modules ⥤ ModuleCat.{u} Γ(X, ⊤) :=
  SheafOfModules.evaluation X.ringCatSheaf (op ⊤)

/-- The global sections functor on `𝒪_X`-modules is additive. -/
instance modulesGlobalSections_additive (X : Scheme.{u}) :
    (modulesGlobalSections X).Additive where
  map_add := rfl

/-- **Hartshorne II, Proposition 5.6.** On an affine scheme, global sections of a short exact
sequence of `𝒪_X`-modules whose first term is quasi-coherent form a short exact sequence. -/
theorem affine_globalSections_shortExact {X : Scheme.{u}} [IsAffine X]
    (S : ShortComplex X.Modules) (hS : S.ShortExact) [S.X₁.IsQuasicoherent] :
    (S.map (modulesGlobalSections X)).ShortExact := by
  have : Mono S.f := hS.mono_f
  refine
    { exact := (ShortComplex.moduleCat_exact_iff _).mpr fun s hs ↦
        modules_sections_exact hS.exact (U := ⊤) s hs
      mono_f := (ModuleCat.mono_iff_injective _).mpr (modules_app_injective S.f ⊤)
      epi_g := (ModuleCat.epi_iff_surjective _).mpr fun t ↦ affine_surj S hS t }

end Hartshorne

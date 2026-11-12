/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ProjGammaStarReconstruction
import Hartshorne.Scheme.ProjectiveSpaceSectionRing
import Hartshorne.Scheme.ProjClosedSubschemeTruncation
import Hartshorne.Scheme.ModuleIdealSheafData

/-!
# Closed subschemes of projective space are defined by homogeneous ideals

Hartshorne, *Algebraic Geometry*, II, Corollary 5.16(a) (pp. 119–120).

Let `S = R[x₀, …, xᵣ]` and `X = ℙʳ_R = Proj S`. For a quasi-coherent ideal sheaf
`ℐ ⊆ 𝒪_X` (`QuasicoherentIdealSubsheaf`), the inclusion `ℐ ⟶ 𝒪_X` (`idealι`) induces an
`S`-linear map `Γ_*(ℐ) ⟶ Γ_*(𝒪_X)` (`gammaStarLinear`), and `Γ_*(𝒪_X) = S` (Proposition 5.13,
`ProjectiveSpaceSectionRing.sectionRingMap`). The homogeneous ideal `Γ_*(ℐ) ∩ S` is
`gammaStarIdeal R r ℐ`: the elements of `S` whose image in `Γ_*(𝒪_X)` comes from `Γ_*(ℐ)`.

* `ker_projQuotientι_gammaStarIdeal`: the closed subscheme `Proj (S/I) ⟶ X` defined by
  `I = Γ_*(ℐ) ∩ S` (`projQuotientι`, Exercise II.3.12) has ideal sheaf `ℐ`.
* `ker_projQuotientι_gammaStarIdeal_eq_ker`: for `f : Y ⟶ X` with ideal sheaf `I_Y = ker f`,
  `Proj (S/I) ⟶ X` with `I = Γ_*(I_Y) ∩ S` has ideal sheaf `ker f`.
* `exists_iso_projQuotientι_gammaStarIdeal`: hence every closed subscheme `Y ⟶ X` is, up to
  isomorphism over `X`, the closed subscheme defined by `Γ_*(I_Y) ∩ S`.

## Proof

Following Hartshorne, by Proposition 5.15 (`GammaStarReconstruction.isIso_gammaStarEval`) the
evaluation `Γ_*(ℐ)~ ⟶ ℐ` is an isomorphism, so near every point a section of `ℐ` is a fraction
`m / s` with `m ∈ Γ(X, ℐ(n))`, `s ∈ S_n` (`stalkEval_surjective_of_isIso`). Its image in `𝒪_X` is
`b / s`, where `b ∈ S_n` corresponds to the image of `m` in `Γ(X, 𝒪_X(n))` (`app_frac`,
`frac_sectionRingMap`), and `b ∈ Γ_*(ℐ) ∩ S` by definition. Conversely `c / h` with
`c ∈ Γ_*(ℐ) ∩ S` is a section of `ℐ` (`ringFrac_mem_ideal`). On `D₊(h)` the ideal of
`Proj (S/I)` consists of the fractions mapping to zero in `(S/I)_(h)`
(`awayToSection_mem_ker_iff`), that is, of the `a / hⁿ` with `hᵏ a ∈ I`. Comparing the two
descriptions gives `ℐ ⊆ ker` locally (`le_ker_projQuotientι`) and `ker ⊆ ℐ` on the charts
`D₊(xᵢ)` (`ker_projQuotientι_le`).
-/
universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Hartshorne

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace
  HomogeneousLocalization GradedGlobalSections ProjGradedModuleSheaf Ringed

namespace ProjectiveClosedSubscheme

section General

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜]

/-- Multiplication by `s ∈ S_d` on twists is natural in the module. -/
theorem whiskerRight_mulMap {F G : (Proj 𝒜).Modules} (φ : F ⟶ G) (n : ℤ) (d : ℕ) (s : 𝒜 d) :
    (φ ▷ projTwistingSheaf 𝒜 n) ≫ mulMap G n d s =
      mulMap F n d s ≫ (φ ▷ projTwistingSheaf 𝒜 (n + d)) := by
  simp only [mulMap, Category.assoc]
  rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc,
    associator_naturality_left_assoc, ← whisker_exchange]

/-- The map `Γ(X, F(n)) → Γ(X, G(n))` induced by `φ : F ⟶ G`. -/
def twistGlobalMap {F G : (Proj 𝒜).Modules} (φ : F ⟶ G) (n : ℤ) :
    twistGlobal F n →+ twistGlobal G n :=
  ((φ ▷ projTwistingSheaf 𝒜 n).val.app (op ⊤)).hom.toAddMonoidHom

theorem twistGlobalMap_mulGlobal {F G : (Proj 𝒜).Modules} (φ : F ⟶ G) (n : ℤ) (d : ℕ)
    (s : 𝒜 d) (x : twistGlobal F n) :
    twistGlobalMap φ (n + d) (mulGlobal F n d s x) =
      mulGlobal G n d s (twistGlobalMap φ n x) := by
  have h := congrArg (fun f => f.val.app (op ⊤) x) (whiskerRight_mulMap φ n d s)
  exact h.symm

/-- The map `Γ_*(F) → Γ_*(G)` induced by `φ : F ⟶ G`, degreewise. -/
def gammaStarMap {F G : (Proj 𝒜).Modules} (φ : F ⟶ G) : GammaStar F →+ GammaStar G :=
  DirectSum.map (twistGlobalMap φ)

attribute [local instance] gammaStarModule

/-- **`Γ_*` of a morphism is `S`-linear.** -/
def gammaStarLinear {F G : (Proj 𝒜).Modules} (φ : F ⟶ G) : GammaStar F →ₗ[A] GammaStar G where
  toFun := gammaStarMap φ
  map_add' := map_add _
  map_smul' c y := by
    induction c using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp only [zero_smul, map_zero]
    | add c c' hc hc' =>
      simp only [RingHom.id_apply] at hc hc' ⊢
      rw [add_smul, map_add, hc, hc', add_smul]
    | homogeneous c =>
      simp only [RingHom.id_apply]
      induction y using DirectSum.induction_on with
      | zero => simp only [smul_zero, map_zero]
      | add y y' hy hy' => rw [smul_add, map_add, hy, hy', map_add, smul_add]
      | of n x =>
        rw [smul_of _ c.2, gammaStarMap, DirectSum.map_of, DirectSum.map_of, smul_of _ c.2]
        exact congrArg _ (twistGlobalMap_mulGlobal φ n _ c x)

/-- Multiplication by `g / 1` is natural in the module. -/
theorem secMap_naturality {F G : (Proj 𝒜).Modules} (φ : F ⟶ G) (d : ℕ) (g : 𝒜 d) :
    φ ≫ GammaStarReconstruction.secMap G d g =
      GammaStarReconstruction.secMap F d g ≫ (φ ▷ projTwistingSheaf 𝒜 d) := by
  simp only [GammaStarReconstruction.secMap, Category.assoc]
  rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange]

/-- **The fractions `m / g` are natural**: `φ (m / g) = φ(m) / g`. -/
theorem app_frac {F G : (Proj 𝒜).Modules} (φ : F ⟶ G) (d : ℕ) (g : 𝒜 d)
    (m : twistGlobal F d) :
    φ.val.app _ (GammaStarReconstruction.frac F d g m) =
      GammaStarReconstruction.frac G d g (twistGlobalMap φ d m) := by
  apply (GammaStarReconstruction.secMap_app_bijective G d g le_rfl).1
  rw [GammaStarReconstruction.secMap_frac]
  have h1 := congrArg (fun f => f.val.app (op (Proj.basicOpen 𝒜 (g : A)))
    (GammaStarReconstruction.frac F d g m)) (secMap_naturality φ d g)
  refine h1.trans ?_
  change (φ ▷ projTwistingSheaf 𝒜 d).val.app _
    ((GammaStarReconstruction.secMap F d g).val.app _ (GammaStarReconstruction.frac F d g m)) = _
  rw [GammaStarReconstruction.secMap_frac]
  exact PresheafOfModules.naturality_apply _ _ _

/-- The section `c / h` of `𝒪_X` over `D₊(h)` is the image of `c / h ∈ S_(h)`. -/
theorem ringFrac_eq_awayToSection (N : ℕ) (c h : 𝒜 N) :
    GammaStarReconstruction.ringFrac N c h =
      Proj.awayToSection 𝒜 (h : A) (HomogeneousLocalization.mk ⟨N, c, h, ⟨1, pow_one _⟩⟩) :=
  rfl

open ProjTruncation in
/-- **The ideal of `Proj (S/I)` over `D₊(h)`.** A section `z ∈ S_(h)` of `𝒪_X` over `D₊(h)`
lies in the ideal of the closed subscheme `Proj (S/I)` exactly when it maps to zero in
`(S/I)_(h)`. -/
theorem awayToSection_mem_ker_iff (I : HomogeneousIdeal 𝒜) {N : ℕ} (hN : 0 < N) {h : A}
    (hh : h ∈ 𝒜 N) (z : Away 𝒜 h) :
    Proj.awayToSection 𝒜 h z ∈ (projQuotientι 𝒜 I).ker.ideal
        ⟨Proj.basicOpen 𝒜 h, Proj.isAffineOpen_basicOpen 𝒜 h hh hN⟩ ↔
      Away.map (gradedQuotientMk 𝒜 I) h z = 0 := by
  have hφ := irrelevant_le_map_of_surjective (gradedQuotientMk_surjective 𝒜 I)
  rw [projQuotientι_eq_map]
  have : QuasiCompact (Proj.map (gradedQuotientMk 𝒜 I) hφ) := by
    rw [← projQuotientι_eq_map]; infer_instance
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker, Scheme.Hom.app_eq_appLE]
  have key := congrArg (fun f => f.hom z)
    (Proj.awayToSection_comp_appLE (gradedQuotientMk 𝒜 I) hφ hh)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom] at key
  erw [key]
  have hinj : Function.Injective (Proj.awayToSection (gradedQuotient 𝒜 I)
      (gradedQuotientMk 𝒜 I h)) := by
    have := (ConcreteCategory.bijective_of_isIso
      (Proj.basicOpenIsoAway (gradedQuotient 𝒜 I) (gradedQuotientMk 𝒜 I h)
        ((gradedQuotientMk 𝒜 I).map_mem hh) hN).hom).1
    rwa [Proj.basicOpenIsoAway_hom] at this
  exact map_eq_zero_iff _ hinj

/-- `(c / h) · (h / 1) = c / 1` in `𝒪_X(N)` over `D₊(h)`. -/
theorem ringFrac_smul_twistSection (N : ℕ) (c h : 𝒜 N) :
    (GammaStarReconstruction.ringFrac N c h •
        (show Γ(projTwistingSheaf 𝒜 N, Proj.basicOpen 𝒜 (h : A)) from
          twistSection N h (op (Proj.basicOpen 𝒜 (h : A)))) :
        Γ(projTwistingSheaf 𝒜 N, Proj.basicOpen 𝒜 (h : A))) =
      twistSection N c (op (Proj.basicOpen 𝒜 (h : A))) := by
  apply section_ext
  intro y
  rw [GammaStarReconstruction.twistingSheaf_smul_apply]
  apply HomogeneousLocalizedModule.ext
  rw [HomogeneousLocalizedModule.val_smul, twistSection_apply, twistSection_apply,
    twistFraction_val, twistFraction_val]
  change (HomogeneousLocalization.mk (𝒜 := 𝒜) ⟨N, c, h, y.2⟩).val •
      LocalizedModule.mk (h : A) 1 = LocalizedModule.mk (c : A) 1
  rw [HomogeneousLocalization.val_mk, LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq]
  exact ⟨1, by simp only [one_smul, mul_one, smul_eq_mul, Submonoid.smul_def]; ring⟩

/-- Sections of `𝒪_X` over an open of `Proj S` are determined by their values. -/
theorem proj_section_ext {W : (Proj 𝒜).Opens} {s t : Γ(Proj 𝒜, W)}
    (h : ∀ y : W, (s.1 y).val = (t.1 y).val) : s = t :=
  Subtype.ext (funext fun y => HomogeneousLocalization.val_injective _ (h y))

/-- From Proposition 5.15: if the evaluation morphism `Γ_*(F)~ ⟶ F` is an isomorphism, then
every germ of `F` is the germ of a fraction `m / s`. -/
theorem stalkEval_surjective_of_isIso (F : (Proj 𝒜).Modules)
    (hF : IsIso (GammaStarReconstruction.gammaStarEval F)) (x : Proj 𝒜) :
    Function.Surjective (GammaStarReconstruction.stalkEval F x) := by
  intro w
  have h0 : IsIso ((SheafOfModules.toSheaf (Proj 𝒜).ringCatSheaf).map
      (GammaStarReconstruction.gammaStarEval F)) :=
    @Functor.map_isIso _ _ _ _ _ _ (SheafOfModules.toSheaf (Proj 𝒜).ringCatSheaf) _ hF
  have h1 := (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso
    ((SheafOfModules.toSheaf (Proj 𝒜).ringCatSheaf).map
      (GammaStarReconstruction.gammaStarEval F))).1 h0 x
  obtain ⟨v, hv⟩ := (@ConcreteCategory.bijective_of_isIso _ _ _ _ _ _ _ _ _ h1).2 w
  exact ⟨_, (GammaStarReconstruction.stalk_gammaStarEval F x v).symm.trans hv⟩

end General

section ProjectiveSpace

open MvPolynomial ProjectiveSpaceSectionRing GammaStarReconstruction

attribute [local instance] MvPolynomial.gradedAlgebra gammaStarModule

variable {R : Type u} [CommRing R] {r : ℕ}

local notation "𝒮" => MvPolynomial.homogeneousSubmodule (Fin (r + 1)) R
local notation "𝒪" =>
  𝟙_ (Scheme.Modules (Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) R)))

/-- The inclusion `ℐ ⟶ 𝒪_X` of a quasi-coherent ideal subsheaf. -/
def idealι {X : Scheme.{u}} (ℐ : QuasicoherentIdealSubsheaf X) : ℐ.toModules ⟶ 𝟙_ X.Modules :=
  ⟨ℐ.carrier.ι⟩

theorem idealι_app {X : Scheme.{u}} (ℐ : QuasicoherentIdealSubsheaf X) {U : X.Opens}
    (t : Γ(ℐ.toModules, U)) : (idealι ℐ).val.app (op U) t = t.1 :=
  rfl

/-- The image in `Γ_*(𝒪_X)` of the degree-`d` part of `s` is the degree-`d` component of the
image of `s`. -/
theorem sectionRingMap_decompose (s : MvPolynomial (Fin (r + 1)) R) (d : ℕ) :
    sectionRingMap R r (DirectSum.decompose 𝒮 s d : MvPolynomial (Fin (r + 1)) R) =
      DirectSum.of (fun m => twistGlobal 𝒪 m) (d : ℤ) (sectionRingMap R r s d) := by
  classical
  apply eq_of_twistValue_component_eq
  intro n x
  rw [twistValue_sectionRingMap, degreePart_of_mem (SetLike.coe_mem _)]
  by_cases hnd : n = d
  · subst hnd
    rw [if_pos rfl, twistValue_of_same, twistValue_sectionRingMap, degreePart_natCast]
  · rw [if_neg hnd, twistValue_of_ne (Ne.symm hnd), LocalizedModule.zero_mk]

variable (R r) in
/-- **The homogeneous ideal `Γ_*(ℐ) ∩ S`** of a quasi-coherent ideal subsheaf `ℐ ⊆ 𝒪_X` on
`X = ℙʳ_R = Proj S`, `S = R[x₀, …, xᵣ]`: the elements of `S` whose image in `Γ_*(𝒪_X)` lies in
the image of `Γ_*(ℐ) → Γ_*(𝒪_X)`. -/
def gammaStarIdeal (ℐ : QuasicoherentIdealSubsheaf (Proj 𝒮)) : HomogeneousIdeal 𝒮 where
  toSubmodule := (LinearMap.range (gammaStarLinear (idealι ℐ))).comap (sectionRingMap R r)
  is_homogeneous' := by
    intro d s hs
    obtain ⟨y, hy⟩ := hs
    refine ⟨DirectSum.of _ (d : ℤ) (y d), ?_⟩
    change gammaStarMap (idealι ℐ) _ = sectionRingMap R r _
    rw [sectionRingMap_decompose, gammaStarMap, DirectSum.map_of, ← DirectSum.map_apply]
    exact congrArg (fun z : GammaStar 𝒪 => DirectSum.of (fun m => twistGlobal 𝒪 m) (d : ℤ) (z d)) hy

/-- A homogeneous `c ∈ S_N` lies in `Γ_*(ℐ) ∩ S` exactly when the section `c / 1` of
`𝒪_X(N)` comes from a global section of `ℐ(N)`. -/
theorem mem_gammaStarIdeal_iff (ℐ : QuasicoherentIdealSubsheaf (Proj 𝒮)) {N : ℕ}
    {c : MvPolynomial (Fin (r + 1)) R} (hc : c ∈ 𝒮 N) :
    c ∈ gammaStarIdeal R r ℐ ↔ ∃ m : twistGlobal ℐ.toModules N,
      twistGlobalMap (idealι ℐ) N m = sectionRingMap R r c N := by
  change sectionRingMap R r c ∈ LinearMap.range (gammaStarLinear (idealι ℐ)) ↔ _
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y N, (DirectSum.map_apply _ _ _).symm.trans (congrArg (fun z => z (N : ℤ)) hy)⟩
  · rintro ⟨m, hm⟩
    refine ⟨DirectSum.of _ (N : ℤ) m, ?_⟩
    change gammaStarMap (idealι ℐ) _ = _
    rw [gammaStarMap, DirectSum.map_of, hm, ← sectionRingMap_decompose,
      DirectSum.decompose_of_mem_same 𝒮 hc]

/-- **`c · 1 / h = c / h`**: for `c, h ∈ S_N`, the fraction of the image of `c` in `Γ(X, 𝒪_X(N))`
by `h` is the section `c / h` of `𝒪_X` over `D₊(h)`. -/
theorem frac_sectionRingMap (N : ℕ) (c h : 𝒮 N) :
    frac 𝒪 N h (sectionRingMap R r (c : MvPolynomial (Fin (r + 1)) R) N) = ringFrac N c h := by
  apply (secMap_app_bijective 𝒪 N h le_rfl).1
  rw [secMap_frac, secMap_app]
  have hinj := (app_bijective_of_iso (λ_ (projTwistingSheaf 𝒮 N))
    (op (Proj.basicOpen 𝒮 (h : MvPolynomial (Fin (r + 1)) R)))).1
  refine hinj ?_
  rw [PresheafOfModules.naturality_apply]
  erw [leftUnitor_hom_tmulSection, ringFrac_smul_twistSection]
  apply section_ext
  intro y
  apply HomogeneousLocalizedModule.ext
  have hv := twistValue_sectionRingMap (R := R) (r := r) (c : MvPolynomial (Fin (r + 1)) R) N y.1
  rw [degreePart_natCast, DirectSum.decompose_of_mem_same 𝒮 c.2] at hv
  exact hv

/-- **`c ∈ Γ_*(ℐ) ∩ S` gives sections of `ℐ`**: for `c ∈ Γ_*(ℐ) ∩ S` and `c, h ∈ S_N`, the
section `c / h` of `𝒪_X` over `D₊(h)` is a section of `ℐ`. -/
theorem ringFrac_mem_ideal (ℐ : QuasicoherentIdealSubsheaf (Proj 𝒮)) {N : ℕ} (c h : 𝒮 N)
    (hc : (c : MvPolynomial (Fin (r + 1)) R) ∈ gammaStarIdeal R r ℐ) :
    ringFrac N c h ∈ ℐ.ideal (Proj.basicOpen 𝒮 (h : MvPolynomial (Fin (r + 1)) R)) := by
  obtain ⟨m, hm⟩ := (mem_gammaStarIdeal_iff ℐ c.2).1 hc
  have e := app_frac (idealι ℐ) N h m
  rw [hm, frac_sectionRingMap] at e
  rw [← e, idealι_app]
  exact (frac ℐ.toModules N h m).2

private theorem X_mem (i : Fin (r + 1)) : (X i : MvPolynomial (Fin (r + 1)) R) ∈ 𝒮 1 :=
  isHomogeneous_X R i

private theorem adjoin_X_eq_top :
    Algebra.adjoin (𝒮 0) (Set.range (X : Fin (r + 1) → MvPolynomial (Fin (r + 1)) R)) = ⊤ := by
  rw [eq_top_iff]
  rintro P -
  induction P using MvPolynomial.induction_on with
  | C a =>
    have ha : (C a : MvPolynomial (Fin (r + 1)) R) ∈ 𝒮 0 := isHomogeneous_C _ a
    exact Subalgebra.algebraMap_mem _ (⟨C a, ha⟩ : 𝒮 0)
  | add p q hp hq => exact add_mem hp hq
  | mul_X p i hp => exact mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩)

private theorem iSup_basicOpen_X :
    ⨆ i : Fin (r + 1), Proj.basicOpen 𝒮 (X i : MvPolynomial (Fin (r + 1)) R) = ⊤ :=
  Proj.iSup_basicOpen_eq_top' 𝒮 (fun i => X i) (fun i => ⟨1, X_mem i⟩) adjoin_X_eq_top

/-- **Global sections of `𝒪_X(n)`, `n ≥ 0`, on `ℙʳ_R`, for every `r`.** Every global section of
`𝒪_X(n)` is `b / 1` for some `b ∈ S_n`. For `r ≥ 1` this is part of Proposition 5.13; for
`r = 0`, `X = D₊(x₀)` and a section is `a / x₀ᵏ` with `a = c x₀^{n+k}`. -/
theorem exists_mem_sectionRingMap_eq (n : ℕ) (z : twistGlobal 𝒪 n) :
    ∃ b ∈ 𝒮 n, sectionRingMap R r b n = z := by
  classical
  rcases Nat.eq_zero_or_pos r with hr | hr
  · have hfin : ∀ i : Fin (r + 1), i = 0 := fun i => Fin.ext (by omega)
    rcases subsingleton_or_nontrivial R with hR | hR
    · have hsub : ∀ p : MvPolynomial (Fin (r + 1)) R, p = 0 := fun p =>
        MvPolynomial.ext _ _ fun _ => Subsingleton.elim _ _
      refine ⟨0, zero_mem _, eq_of_twistValue_eq fun x => ?_⟩
      generalize twistValue (n : ℤ) (sectionRingMap R r 0 n) x = y
      generalize twistValue (n : ℤ) z x = y'
      induction y using LocalizedModule.induction_on with
      | h p t =>
        induction y' using LocalizedModule.induction_on with
        | h p' t' => rw [hsub p, hsub p', LocalizedModule.zero_mk, LocalizedModule.zero_mk]
    obtain ⟨m, hm⟩ := exists_globalValue_eq_mapOfLE 𝒮 (gradedTwist 𝒮 n)
      (X_mem 0) one_pos (unitorGlobal n z)
    obtain ⟨k, a, ha, c, hc, hcx, rfl⟩ := HomogeneousLocalizedModule.mk_surjective m
    obtain ⟨e, rfl⟩ := hcx
    have hke : k = e := DirectSum.degree_eq_of_mem_mem 𝒮 hc (X_pow_mem 0 e)
      (isRegular_X_pow e).ne_zero
    subst hke
    have ha0 : a ∈ 𝒮 ((n : ℤ) + k).toNat ∧ ((n : ℤ) + k < 0 → a = 0) := ha
    have ha' : a ∈ 𝒮 (n + k) := by
      have h1 := ha0.1
      rwa [show ((n : ℤ) + k).toNat = n + k by omega] at h1
    have hdvd : (X 0 : MvPolynomial (Fin (r + 1)) R) ^ k ∣ a := by
      rw [MvPolynomialDvd.X_pow_dvd_iff]
      intro d hd
      apply ((mem_homogeneousSubmodule _ _).1 ha').coeff_eq_zero
      rw [Finsupp.degree_eq_sum, Finset.sum_eq_single (0 : Fin (r + 1))
        (fun i _ hi => absurd (hfin i) hi) (by simp)]
      omega
    obtain ⟨b₀, hb₀⟩ := hdvd
    have hab : a = X 0 ^ k * (DirectSum.decompose 𝒮 b₀ n : MvPolynomial (Fin (r + 1)) R) := by
      have hdec : a = (DirectSum.decompose 𝒮 (X 0 ^ k * b₀) (n + k) :
          MvPolynomial (Fin (r + 1)) R) := by
        rw [← hb₀, DirectSum.decompose_of_mem_same 𝒮 ha']
      rw [hdec, DirectSum.coe_decompose_mul_of_left_mem_of_le 𝒮 (X_pow_mem 0 k) (by omega),
        Nat.add_sub_cancel]
    refine ⟨_, SetLike.coe_mem (DirectSum.decompose 𝒮 b₀ n), eq_of_twistValue_eq fun x => ?_⟩
    have hxtop : x ∈ (⨆ i : Fin (r + 1),
        Proj.basicOpen 𝒮 (X i : MvPolynomial (Fin (r + 1)) R)) := by
      rw [iSup_basicOpen_X]
      trivial
    obtain ⟨j, hj⟩ := Opens.mem_iSup.1 hxtop
    obtain rfl := hfin j
    rw [twistValue_sectionRingMap, degreePart_natCast, DirectSum.decompose_of_mem_same 𝒮
      (SetLike.coe_mem _)]
    change _ = (globalValue 𝒮 (gradedTwist 𝒮 n) (unitorGlobal n z) x).val
    rw [hm x hj, HomogeneousLocalizedModule.mapOfLE_mk, HomogeneousLocalizedModule.val_mk]
    refine LocalizedModule.mk_eq.2 ⟨1, ?_⟩
    simp only [Submonoid.smul_def, smul_eq_mul, OneMemClass.coe_one, one_mul, hab]
  · obtain ⟨b', hb'⟩ := (sectionRingMap_bijective (R := R) hr).2
      (DirectSum.of (fun k => twistGlobal 𝒪 k) (n : ℤ) z)
    refine ⟨_, SetLike.coe_mem (DirectSum.decompose 𝒮 b' n), ?_⟩
    rw [sectionRingMap_decompose, hb', DirectSum.of_eq_same, DirectSum.of_eq_same]

-- Instance search for the sheaf-theoretic instances in `IsQuasicoherent` on `ℙʳ_R` exceeds the
-- default `synthInstance` budget.
set_option synthInstance.maxHeartbeats 200000 in
private theorem isIso_gammaStarEval_projectiveSpace (F : (Proj 𝒮).Modules) [F.IsQuasicoherent] :
    IsIso (gammaStarEval F) := by
  classical
  refine isIso_gammaStarEval (s := Finset.univ.image (X : Fin (r + 1) → _)) ?_ ?_ F
  · intro a ha
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ha
    exact X_mem i
  · rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    exact adjoin_X_eq_top

/-- The ideal of `Proj (S/I)`, `I = Γ_*(ℐ) ∩ S`, is contained in `ℐ`: checked on the charts
`D₊(xᵢ)`, where a section `a / xᵢⁿ` in the ideal of `Proj (S/I)` has `xᵢᵏ a ∈ I`. -/
theorem ker_projQuotientι_le (ℐ : QuasicoherentIdealSubsheaf (Proj 𝒮)) :
    (projQuotientι 𝒮 (gammaStarIdeal R r ℐ)).ker ≤ quasicoherentIdealSubsheafEquiv ℐ := by
  refine Scheme.IdealSheafData.le_of_iSup_eq_top
    (fun i : Fin (r + 1) => ⟨Proj.basicOpen 𝒮 (X i : MvPolynomial (Fin (r + 1)) R),
      Proj.isAffineOpen_basicOpen 𝒮 _ (X_mem i) one_pos⟩) iSup_basicOpen_X ?_
  intro i t ht
  rw [quasicoherentIdealSubsheafEquiv_ideal]
  obtain ⟨z, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (Proj.basicOpenIsoAway 𝒮 (X i : MvPolynomial (Fin (r + 1)) R) (X_mem i) one_pos).hom).2 t
  rw [Proj.basicOpenIsoAway_hom] at ht ⊢
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒮 (X_mem i) z
  rw [awayToSection_mem_ker_iff _ one_pos (X_mem i), Away.map_mk] at ht
  have hv := congrArg HomogeneousLocalization.val ht
  rw [Away.val_mk, HomogeneousLocalization.val_zero, Localization.mk_eq_mk',
    IsLocalization.mk'_eq_zero_iff] at hv
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := hv
  have hk' : (X i : MvPolynomial (Fin (r + 1)) R) ^ (k + 1) * a ∈ gammaStarIdeal R r ℐ := by
    have h0 : (X i : MvPolynomial (Fin (r + 1)) R) ^ k * a ∈ (gammaStarIdeal R r ℐ).toIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simpa only [map_pow, map_mul, gradedQuotientMk_apply] using hk
    rw [pow_succ', mul_assoc]
    exact (gammaStarIdeal R r ℐ).toIdeal.mul_mem_left _ h0
  have ha' : a ∈ 𝒮 n := by simpa only [smul_eq_mul, mul_one] using ha
  have hc : (X i : MvPolynomial (Fin (r + 1)) R) ^ (k + 1) * a ∈ 𝒮 ((k + 1) + n) :=
    SetLike.GradedMul.mul_mem (X_pow_mem i (k + 1)) ha'
  have hmem := ringFrac_mem_ideal ℐ ⟨_, hc⟩ ⟨_, X_pow_mem i ((k + 1) + n)⟩ hk'
  have hle : Proj.basicOpen 𝒮 (X i : MvPolynomial (Fin (r + 1)) R) ≤
      Proj.basicOpen 𝒮 ((X i : MvPolynomial (Fin (r + 1)) R) ^ ((k + 1) + n)) :=
    (Proj.basicOpen_pow 𝒮 _ _ (by omega)).ge
  have hres := ArtinReesKernelSheaf.res_mem ℐ.carrier hle hmem
  rw [ArtinReesKernelSheaf.res_apply] at hres
  have key : Proj.awayToSection 𝒮 (X i : MvPolynomial (Fin (r + 1)) R)
      (Away.mk 𝒮 (X_mem i) n a ha) = (Proj 𝒮).presheaf.map (homOfLE hle).op
        (ringFrac ((k + 1) + n) ⟨_, hc⟩ ⟨_, X_pow_mem i ((k + 1) + n)⟩) := by
    apply proj_section_ext
    intro y
    change HomogeneousLocalization.val (HomogeneousLocalization.mk _) =
      HomogeneousLocalization.val (HomogeneousLocalization.mk _)
    rw [HomogeneousLocalization.val_mk, HomogeneousLocalization.val_mk,
      Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by simp only [OneMemClass.coe_one, one_mul, GradedRingHom.id_apply]; ring⟩
  rw [key]
  exact hres

/-- `ℐ` is contained in the ideal of `Proj (S/I)`, `I = Γ_*(ℐ) ∩ S`. By Proposition 5.15 a section
of `ℐ` is, near each point, a fraction `m / s` with `m ∈ Γ(X, ℐ(n))`; by Proposition 5.13 its
image in `𝒪_X` is `b / s` with `b ∈ S_n`, and then `b ∈ I`, so `b / s` lies in the ideal of
`Proj (S/I)`. -/
theorem le_ker_projQuotientι (ℐ : QuasicoherentIdealSubsheaf (Proj 𝒮)) :
    quasicoherentIdealSubsheafEquiv ℐ ≤ (projQuotientι 𝒮 (gammaStarIdeal R r ℐ)).ker := by
  have hqc := ℐ.isQuasicoherent
  have hiso := isIso_gammaStarEval_projectiveSpace ℐ.toModules
  intro V t ht
  rw [quasicoherentIdealSubsheafEquiv_ideal] at ht
  rw [← ideal_idealSheafDataToSubsheaf (projQuotientι 𝒮 (gammaStarIdeal R r ℐ)).ker V]
  apply (idealSheafDataToSubsheaf (projQuotientι 𝒮 (gammaStarIdeal R r ℐ)).ker).isLocal
  intro x hx
  let t' : ℐ.toModules.presheaf.obj (op (V : (Proj 𝒮).Opens)) :=
    show ℐ.carrier.obj (op (V : (Proj 𝒮).Opens)) from ⟨t, ht⟩
  obtain ⟨w, hw⟩ := stalkEval_surjective_of_isIso ℐ.toModules hiso x
    (ℐ.toModules.presheaf.germ _ x hx t')
  obtain ⟨n, m, hm, s, hs, hsx, rfl⟩ := HomogeneousLocalizedModule.mk_surjective w
  rw [stalkEval_mk] at hw
  obtain ⟨W, hxW, iU, iV, hWeq⟩ := TopCat.Presheaf.germ_eq ℐ.toModules.presheaf x hsx hx _ _ hw
  -- the numerator `b ∈ S_n`, from Proposition 5.13
  obtain ⟨b, hbmem, hbN⟩ := exists_mem_sectionRingMap_eq (R := R) n
    (twistGlobalMap (idealι ℐ) n (m n))
  have hbI := (mem_gammaStarIdeal_iff ℐ hbmem).2 ⟨m n, hbN.symm⟩
  have hfr : (idealι ℐ).val.app _ (fracM ℐ.toModules n ⟨s, hs⟩ m) =
      ringFrac n ⟨_, hbmem⟩ ⟨s, hs⟩ := by
    rw [fracM, app_frac, ← hbN]
    exact frac_sectionRingMap n ⟨_, hbmem⟩ ⟨s, hs⟩
  -- a chart `D₊(x_j)` containing `x`
  have hxtop : x ∈ (⨆ i : Fin (r + 1), Proj.basicOpen 𝒮 (X i : MvPolynomial (Fin (r + 1)) R)) := by
    rw [iSup_basicOpen_X]
    trivial
  obtain ⟨j, hxj⟩ := Opens.mem_iSup.1 hxtop
  have hc := SetLike.GradedMul.mul_mem (X_mem (R := R) j) hbmem
  have hd := SetLike.GradedMul.mul_mem (X_mem (R := R) j) hs
  have hcI : (X j : MvPolynomial (Fin (r + 1)) R) *
      b ∈ gammaStarIdeal R r ℐ :=
    (gammaStarIdeal R r ℐ).toIdeal.mul_mem_left _ hbI
  have hmemK : ringFrac (1 + n) ⟨_, hc⟩ ⟨_, hd⟩ ∈
      (idealSheafDataToSubsheaf (projQuotientι 𝒮 (gammaStarIdeal R r ℐ)).ker).ideal
        (Proj.basicOpen 𝒮 ((X j : MvPolynomial (Fin (r + 1)) R) * s)) := by
    rw [ideal_idealSheafDataToSubsheaf _
      ⟨_, Proj.isAffineOpen_basicOpen 𝒮 _ hd (by omega)⟩, ringFrac_eq_awayToSection,
      awayToSection_mem_ker_iff _ (by omega) hd]
    apply HomogeneousLocalization.mk_eq_zero_of_num
    apply Subtype.ext
    change gradedQuotientMk 𝒮 _ _ = 0
    rw [gradedQuotientMk_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact hcI
  have hW'V : W ⊓ Proj.basicOpen 𝒮 (X j : MvPolynomial (Fin (r + 1)) R) ≤ V :=
    inf_le_left.trans iV.le
  have hW'D : W ⊓ Proj.basicOpen 𝒮 (X j : MvPolynomial (Fin (r + 1)) R) ≤
      Proj.basicOpen 𝒮 ((X j : MvPolynomial (Fin (r + 1)) R) * s) := by
    rw [Proj.basicOpen_mul]
    exact le_inf inf_le_right (inf_le_left.trans iU.le)
  have hres := ArtinReesKernelSheaf.res_mem _ hW'D hmemK
  refine ⟨_, hW'V, ⟨hxW, hxj⟩, ?_⟩
  have key : ArtinReesKernelSheaf.res (SheafOfModules.unit (Proj 𝒮).ringCatSheaf) hW'V t =
      ArtinReesKernelSheaf.res (SheafOfModules.unit (Proj 𝒮).ringCatSheaf) hW'D
        (ringFrac (1 + n) ⟨_, hc⟩ ⟨_, hd⟩) := by
    refine proj_section_ext (W := W ⊓ Proj.basicOpen 𝒮 (X j : MvPolynomial (Fin (r + 1)) R))
      (s := (Proj 𝒮).presheaf.map (homOfLE hW'V).op t)
      (t := (Proj 𝒮).presheaf.map (homOfLE hW'D).op (ringFrac (1 + n) ⟨_, hc⟩ ⟨_, hd⟩))
      fun y => ?_
    have hyW : y.1 ∈ W := y.2.1
    have h1 : ((ringFrac n ⟨_, hbmem⟩ ⟨s, hs⟩).1 ⟨y.1, iU.le hyW⟩).val =
        (t.1 ⟨y.1, iV.le hyW⟩).val := by
      have := congrArg (fun u : ℐ.toModules.presheaf.obj (op W) =>
        (((show ℐ.carrier.obj (op W) from u).1 : Γ(Proj 𝒮, W)).1 ⟨y.1, hyW⟩).val) hWeq
      rw [← hfr]
      exact this
    change (t.1 ⟨y.1, iV.le hyW⟩).val = (HomogeneousLocalization.mk _).val
    rw [← h1]
    change (HomogeneousLocalization.mk _).val = (HomogeneousLocalization.mk _).val
    rw [HomogeneousLocalization.val_mk, HomogeneousLocalization.val_mk,
      Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by simp only [OneMemClass.coe_one, one_mul]; ring⟩
  rw [key]
  exact hres

/-- **Hartshorne II, Corollary 5.16(a), ideal-sheaf form.** Let `X = ℙʳ_R = Proj S`,
`S = R[x₀, …, xᵣ]`, and let `ℐ ⊆ 𝒪_X` be a quasi-coherent ideal sheaf. Then the closed
subscheme `Proj (S/I) ⊆ X` defined by the homogeneous ideal `I = Γ_*(ℐ) ∩ S` has ideal sheaf
`ℐ`. -/
theorem ker_projQuotientι_gammaStarIdeal (ℐ : QuasicoherentIdealSubsheaf (Proj 𝒮)) :
    (projQuotientι 𝒮 (gammaStarIdeal R r ℐ)).ker = quasicoherentIdealSubsheafEquiv ℐ :=
  le_antisymm (ker_projQuotientι_le ℐ) (le_ker_projQuotientι ℐ)

/-- **Hartshorne II, Corollary 5.16(a), kernel form.** Let `S = R[x₀, …, xᵣ]` and
let `f : Y ⟶ ℙʳ_R = Proj S` be a morphism with ideal sheaf `I_Y = ker f` (for a closed immersion,
the module ideal sheaf of the closed subscheme `Y`). Then the closed immersion
`Proj (S/I) ⟶ ℙʳ_R` defined by the homogeneous ideal `I = Γ_*(I_Y) ∩ S` has the same ideal sheaf
as `f`. -/
theorem ker_projQuotientι_gammaStarIdeal_eq_ker {Y : Scheme.{u}} (f : Y ⟶ Proj 𝒮) :
    (projQuotientι 𝒮 (gammaStarIdeal R r (quasicoherentIdealSubsheafEquiv.symm f.ker))).ker =
      f.ker := by
  rw [ker_projQuotientι_gammaStarIdeal, Equiv.apply_symm_apply]

/-- **Hartshorne II, Corollary 5.16(a).** Let `S = R[x₀, …, xᵣ]`. Every closed
subscheme `f : Y ⟶ ℙʳ_R = Proj S` is the closed subscheme defined by the homogeneous ideal
`I = Γ_*(I_Y) ∩ S`, where `I_Y` is its module ideal sheaf: `Y` is isomorphic over `ℙʳ_R` to
`Proj (S/I) ⟶ ℙʳ_R`. -/
theorem exists_iso_projQuotientι_gammaStarIdeal {Y : Scheme.{u}} (f : Y ⟶ Proj 𝒮)
    [IsClosedImmersion f] :
    ∃ e : Y ≅ Proj (gradedQuotient 𝒮
        (gammaStarIdeal R r (quasicoherentIdealSubsheafEquiv.symm f.ker))),
      e.hom ≫ projQuotientι 𝒮
        (gammaStarIdeal R r (quasicoherentIdealSubsheafEquiv.symm f.ker)) = f := by
  have h := ker_projQuotientι_gammaStarIdeal_eq_ker f
  have := IsClosedImmersion.isIso_lift _ _ h
  exact ⟨asIso (IsClosedImmersion.lift _ f h.le), IsClosedImmersion.lift_fac _ _ _⟩

end ProjectiveSpace

end ProjectiveClosedSubscheme

end Hartshorne

/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ProjectiveClosedSubschemeHomogeneousIdeal

/-!
# Saturation of homogeneous ideals of `R[x₀, …, xᵣ]`

Hartshorne, *Algebraic Geometry*, II, Exercise 5.10(a–c) (p. 125).

Let `S = R[x₀, …, xᵣ]` and `X = ℙʳ_R = Proj S`. The saturation of an ideal `I ⊆ S` is
`I^sat = {s ∈ S | ∀ i, ∃ n, xᵢⁿ s ∈ I}` (`saturation`).

* `saturation_isHomogeneous`, `le_saturation`: (a) for homogeneous `I`, `I^sat` is a homogeneous
  ideal containing `I`.
* `ker_projQuotientι_eq_iff`: (b) two homogeneous ideals `I, J` define the same closed subscheme
  `Proj (S/I) = Proj (S/J)` of `X` (equal ideal sheaves of `projQuotientι`) iff
  `I^sat = J^sat`. More precisely `ker_projQuotientι_le_iff`: the ideal sheaf of `Proj (S/I)` is
  contained in that of `Proj (S/J)` iff `I^sat ⊆ J^sat`.
* `saturation_gammaStarIdeal`, `le_gammaStarIdeal_of_ker_eq`, `isGreatest_gammaStarIdeal`: (c)
  for a quasi-coherent ideal sheaf `ℐ` (the ideal sheaf `I_Y` of a closed subscheme `Y`),
  `Γ_*(ℐ) ∩ S` is saturated and is the largest homogeneous ideal defining `ℐ`.
* `gammaStarIdeal_ker_projQuotientι`: `Γ_*` of the ideal sheaf of `Proj (S/I)` is `I^sat`.

## Proof

On a chart `D₊(xᵢ)` a section of `𝒪_X` is `a / xᵢⁿ` with `a ∈ S_n`, and it lies in the ideal of
`Proj (S/I)` iff `xᵢᵏ a ∈ I` for some `k` (`chart_mem_ker_iff`, from `awayToSection_mem_ker_iff`).
Comparing these localized ideals on every chart gives (b). For (c), if `s ∈ S_d` has
`xᵢⁿ s ∈ Γ_*(ℐ)` for all `i`, the sections `s / xᵢᵈ ∈ ℐ(D₊(xᵢ))` give sections
`s / xᵢᵈ ⊗ xᵢᵈ` of `ℐ(d)` over `D₊(xᵢ)` all mapping to `s ∈ Γ(X, 𝒪_X(d))`; since
`ℐ(d) ⟶ 𝒪_X(d)` is injective on sections over each `D₊(xᵢ)`, they glue to a global section of
`ℐ(d)` mapping to `s`, so `s ∈ Γ_*(ℐ)`.
-/
universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Hartshorne

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace
  HomogeneousLocalization GradedGlobalSections ProjGradedModuleSheaf Ringed

namespace ProjectiveClosedSubscheme

open MvPolynomial ProjectiveSpaceSectionRing GammaStarReconstruction ProjTruncation

attribute [local instance] MvPolynomial.gradedAlgebra gammaStarModule

variable {R : Type u} [CommRing R] {r : ℕ}

local notation "𝒮" => MvPolynomial.homogeneousSubmodule (Fin (r + 1)) R
local notation "𝒪" =>
  𝟙_ (Scheme.Modules (Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) R)))

/-- **The saturation of an ideal** `I ⊆ S = R[x₀, …, xᵣ]`:
`I^sat = {s ∈ S | ∀ i, ∃ n, xᵢⁿ s ∈ I}` (Hartshorne II, Exercise 5.10). -/
def saturation (I : Ideal (MvPolynomial (Fin (r + 1)) R)) :
    Ideal (MvPolynomial (Fin (r + 1)) R) where
  carrier := {s | ∀ i : Fin (r + 1), ∃ n : ℕ, X i ^ n * s ∈ I}
  add_mem' {a b} ha hb i := by
    obtain ⟨n, hn⟩ := ha i
    obtain ⟨m, hm⟩ := hb i
    refine ⟨n + m, ?_⟩
    have e : (X i : MvPolynomial (Fin (r + 1)) R) ^ (n + m) * (a + b) =
        X i ^ m * (X i ^ n * a) + X i ^ n * (X i ^ m * b) := by ring
    rw [e]
    exact I.add_mem (I.mul_mem_left _ hn) (I.mul_mem_left _ hm)
  zero_mem' i := ⟨0, by simp⟩
  smul_mem' c s hs i := by
    obtain ⟨n, hn⟩ := hs i
    refine ⟨n, ?_⟩
    rw [smul_eq_mul, mul_left_comm]
    exact I.mul_mem_left c hn

theorem mem_saturation {I : Ideal (MvPolynomial (Fin (r + 1)) R)}
    {s : MvPolynomial (Fin (r + 1)) R} :
    s ∈ saturation I ↔ ∀ i : Fin (r + 1), ∃ n : ℕ, X i ^ n * s ∈ I :=
  Iff.rfl

/-- `I ⊆ I^sat`. -/
theorem le_saturation (I : Ideal (MvPolynomial (Fin (r + 1)) R)) : I ≤ saturation I :=
  fun s hs _ => ⟨0, by simpa using hs⟩

/-- **Hartshorne II, Exercise 5.10(a).** The saturation of a homogeneous ideal of
`R[x₀, …, xᵣ]` is a homogeneous ideal. -/
theorem saturation_isHomogeneous {I : Ideal (MvPolynomial (Fin (r + 1)) R)}
    (hI : I.IsHomogeneous 𝒮) : (saturation I).IsHomogeneous 𝒮 := by
  intro d s hs i
  obtain ⟨n, hn⟩ := hs i
  refine ⟨n, ?_⟩
  have h := hI (n + d) hn
  rwa [DirectSum.coe_decompose_mul_add_of_left_mem 𝒮 (X_pow_mem i n)] at h

private theorem X_mem_one (i : Fin (r + 1)) : (X i : MvPolynomial (Fin (r + 1)) R) ∈ 𝒮 1 :=
  isHomogeneous_X R i

private theorem iSup_basicOpen_X_eq_top :
    ⨆ i : Fin (r + 1), Proj.basicOpen 𝒮 (X i : MvPolynomial (Fin (r + 1)) R) = ⊤ := by
  refine Proj.iSup_basicOpen_eq_top' 𝒮 (fun i => X i) (fun i => ⟨1, X_mem_one i⟩) ?_
  rw [eq_top_iff]
  rintro P -
  induction P using MvPolynomial.induction_on with
  | C a =>
    have ha : (C a : MvPolynomial (Fin (r + 1)) R) ∈ 𝒮 0 := isHomogeneous_C _ a
    exact Subalgebra.algebraMap_mem _ (⟨C a, ha⟩ : 𝒮 0)
  | add p q hp hq => exact add_mem hp hq
  | mul_X p i hp => exact mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩)

/-- The standard chart `D₊(xᵢ)` as an affine open of `ℙʳ_R`. -/
private def chart (i : Fin (r + 1)) : (Proj 𝒮).affineOpens :=
  ⟨Proj.basicOpen 𝒮 (X i : MvPolynomial (Fin (r + 1)) R),
    Proj.isAffineOpen_basicOpen 𝒮 _ (X_mem_one i) one_pos⟩

/-- **The ideal of `Proj (S/I)` on the chart `D₊(xᵢ)`.** The section `a / xᵢⁿ`, `a ∈ S_n`, lies in
the ideal of `Proj (S/I)` iff `xᵢᵏ a ∈ I` for some `k`. -/
private theorem chart_mem_ker_iff (I : HomogeneousIdeal 𝒮) (i : Fin (r + 1)) (n : ℕ)
    (a : MvPolynomial (Fin (r + 1)) R) (ha : a ∈ 𝒮 (n • 1)) :
    Proj.awayToSection 𝒮 (X i : MvPolynomial (Fin (r + 1)) R)
        (Away.mk 𝒮 (X_mem_one i) n a ha) ∈ (projQuotientι 𝒮 I).ker.ideal (chart i) ↔
      ∃ k : ℕ, (X i : MvPolynomial (Fin (r + 1)) R) ^ k * a ∈ I.toIdeal := by
  change _ ∈ (projQuotientι 𝒮 I).ker.ideal ⟨Proj.basicOpen 𝒮 _, _⟩ ↔ _
  rw [awayToSection_mem_ker_iff _ one_pos (X_mem_one i), Away.map_mk,
    ← (HomogeneousLocalization.val_injective _).eq_iff, Away.val_mk,
    HomogeneousLocalization.val_zero, Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff]
  constructor
  · rintro ⟨⟨_, k, rfl⟩, hk⟩
    refine ⟨k, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa only [map_pow, map_mul, gradedQuotientMk_apply] using hk
  · rintro ⟨k, hk⟩
    refine ⟨⟨_, k, rfl⟩, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem] at hk
    simpa only [map_pow, map_mul, gradedQuotientMk_apply] using hk

/-- Every section of `𝒪_X` over `D₊(xᵢ)` is `a / xᵢⁿ` with `a ∈ S_n`. -/
private theorem exists_eq_awayToSection (i : Fin (r + 1))
    (t : Γ(Proj 𝒮, Proj.basicOpen 𝒮 (X i : MvPolynomial (Fin (r + 1)) R))) :
    ∃ (n : ℕ) (a : MvPolynomial (Fin (r + 1)) R) (ha : a ∈ 𝒮 (n • 1)),
      t = Proj.awayToSection 𝒮 (X i : MvPolynomial (Fin (r + 1)) R)
        (Away.mk 𝒮 (X_mem_one i) n a ha) := by
  obtain ⟨z, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (Proj.basicOpenIsoAway 𝒮 (X i : MvPolynomial (Fin (r + 1)) R) (X_mem_one i) one_pos).hom).2 t
  rw [Proj.basicOpenIsoAway_hom]
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒮 (X_mem_one i) z
  exact ⟨n, a, ha, rfl⟩

/-- The ideal sheaf of `Proj (S/I)` is contained in that of `Proj (S/J)` exactly when
`I^sat ⊆ J^sat` (supplementing Hartshorne II, Exercise 5.10(b)). -/
theorem ker_projQuotientι_le_iff (I J : HomogeneousIdeal 𝒮) :
    (projQuotientι 𝒮 I).ker ≤ (projQuotientι 𝒮 J).ker ↔
      saturation I.toIdeal ≤ saturation J.toIdeal := by
  constructor
  · intro h s hs
    rw [(saturation_isHomogeneous J.isHomogeneous).mem_iff]
    intro d
    have hc := saturation_isHomogeneous I.isHomogeneous d hs
    have hd : (DirectSum.decompose 𝒮 s d : MvPolynomial (Fin (r + 1)) R) ∈ 𝒮 (d • 1) := by
      rw [smul_eq_mul, mul_one]
      exact SetLike.coe_mem _
    intro i
    have hmem := (chart_mem_ker_iff I i d _ hd).2 (hc i)
    exact (chart_mem_ker_iff J i d _ hd).1 (h _ hmem)
  · intro h
    refine Scheme.IdealSheafData.le_of_iSup_eq_top chart iSup_basicOpen_X_eq_top ?_
    intro i t ht
    obtain ⟨n, a, ha, rfl⟩ := exists_eq_awayToSection i t
    obtain ⟨k, hk⟩ := (chart_mem_ker_iff I i n a ha).1 ht
    obtain ⟨m, hm⟩ := h (le_saturation _ hk) i
    refine (chart_mem_ker_iff J i n a ha).2 ⟨m + k, ?_⟩
    rw [pow_add, mul_assoc]
    exact hm

/-- **Hartshorne II, Exercise 5.10(b).** Two homogeneous ideals `I, J ⊆ R[x₀, …, xᵣ]` define the
same closed subscheme of `ℙʳ_R` (the closed immersions `Proj (S/I) ⟶ ℙʳ_R` and
`Proj (S/J) ⟶ ℙʳ_R` have the same ideal sheaf) iff `I^sat = J^sat`. -/
theorem ker_projQuotientι_eq_iff (I J : HomogeneousIdeal 𝒮) :
    (projQuotientι 𝒮 I).ker = (projQuotientι 𝒮 J).ker ↔
      saturation I.toIdeal = saturation J.toIdeal := by
  rw [le_antisymm_iff, le_antisymm_iff, ker_projQuotientι_le_iff, ker_projQuotientι_le_iff]

/-! ### Gluing sections of `ℐ(d)` -/

/-- `D₊(f) ⊆ D₊(fᵈ)`. -/
private theorem basicOpen_le_basicOpen_pow (f : MvPolynomial (Fin (r + 1)) R) (d : ℕ) :
    Proj.basicOpen 𝒮 f ≤ Proj.basicOpen 𝒮 (f ^ d) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [pow_zero, Proj.basicOpen_one]
    exact le_top
  · rw [Proj.basicOpen_pow 𝒮 f d hd]

/-- On opens inside `D₊(g)`, `g ∈ S_d`, the map `ℐ(d) ⟶ 𝒪_X(d)` is injective on sections. -/
private theorem whiskerRight_idealι_injective (ℐ : QuasicoherentIdealSubsheaf (Proj 𝒮)) (d : ℕ)
    (g : 𝒮 d) {V : (Proj 𝒮).Opens}
    (hV : V ≤ Proj.basicOpen 𝒮 (g : MvPolynomial (Fin (r + 1)) R)) :
    Function.Injective ((idealι ℐ ▷ projTwistingSheaf 𝒮 d).val.app (op V)) := by
  intro u v huv
  obtain ⟨a, rfl⟩ := (secMap_app_bijective ℐ.toModules d g hV).2 u
  obtain ⟨b, rfl⟩ := (secMap_app_bijective ℐ.toModules d g hV).2 v
  have nat : ∀ c, (secMap 𝒪 d g).val.app (op V) ((idealι ℐ).val.app (op V) c) =
      (idealι ℐ ▷ projTwistingSheaf 𝒮 d).val.app (op V)
        ((secMap ℐ.toModules d g).val.app (op V) c) := fun c =>
    congrArg (fun f => f.val.app (op V) c) (secMap_naturality (idealι ℐ) d g)
  have ha := nat a
  have hb := nat b
  rw [← ha, ← hb] at huv
  have hab := (secMap_app_bijective 𝒪 d g hV).1 huv
  rw [idealι_app, idealι_app] at hab
  rw [Subtype.ext hab]

/-- Compatible sections of a sheaf of modules on a cover of `X` glue to a global section. -/
private theorem modules_glue {Y : Scheme.{u}} (M : Y.Modules) {ι : Type*} (W : ι → Y.Opens)
    (hcov : (⊤ : Y.Opens) ≤ iSup W) (sf : ∀ k, M.val.obj (op (W k)))
    (hc : ∀ k l, M.val.map (homOfLE (inf_le_left : W k ⊓ W l ≤ W k)).op (sf k) =
      M.val.map (homOfLE (inf_le_right : W k ⊓ W l ≤ W l)).op (sf l)) :
    ∃ s : M.val.obj (op ⊤), ∀ k, M.val.map (homOfLE le_top).op s = sf k := by
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' (⟨M.val.presheaf, M.isSheaf⟩ :
    TopCat.Sheaf AddCommGrpCat.{u} Y) W ⊤ (fun _ => homOfLE le_top) hcov sf
    (by intro k l; exact hc k l)
  exact ⟨s, hs⟩

/-- Global sections of a sheaf of modules agreeing on a cover of `X` are equal. -/
private theorem modules_ext {Y : Scheme.{u}} (M : Y.Modules) {ι : Type*} (W : ι → Y.Opens)
    (hcov : (⊤ : Y.Opens) ≤ iSup W) (s t : M.val.obj (op ⊤))
    (h : ∀ k, M.val.map (homOfLE (le_top : W k ≤ ⊤)).op s =
      M.val.map (homOfLE (le_top : W k ≤ ⊤)).op t) : s = t :=
  TopCat.Sheaf.eq_of_locally_eq' (⟨M.val.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} Y)
    W ⊤ (fun _ => homOfLE le_top) hcov s t h

/-- **Gluing sections of `ℐ(d)`.** Local sections of `ℐ(d)` over a cover by opens `Vᵢ ⊆ D₊(gᵢ)`,
`gᵢ ∈ S_d`, all mapping to restrictions of one global section `M` of `𝒪_X(d)`, glue to a global
section of `ℐ(d)` mapping to `M`. -/
private theorem glue_twistGlobalMap_idealι (ℐ : QuasicoherentIdealSubsheaf (Proj 𝒮)) (d : ℕ)
    (M : twistGlobal 𝒪 d) (V : Fin (r + 1) → (Proj 𝒮).Opens)
    (hcover : (⊤ : (Proj 𝒮).Opens) ≤ iSup V)
    (g : Fin (r + 1) → 𝒮 d) (hVg : ∀ i, V i ≤ Proj.basicOpen 𝒮 (g i : MvPolynomial (Fin (r + 1)) R))
    (t : ∀ i, (ℐ.toModules ⊗ projTwistingSheaf 𝒮 d).val.obj (op (V i)))
    (ht : ∀ i, (idealι ℐ ▷ projTwistingSheaf 𝒮 d).val.app (op (V i)) (t i) =
      (𝒪 ⊗ projTwistingSheaf 𝒮 d).val.map (homOfLE le_top).op M) :
    ∃ T : twistGlobal ℐ.toModules d, twistGlobalMap (idealι ℐ) d T = M := by
  have hres_t : ∀ i (W : (Proj 𝒮).Opens) (hW : W ≤ V i),
      (idealι ℐ ▷ projTwistingSheaf 𝒮 d).val.app (op W)
          ((ℐ.toModules ⊗ projTwistingSheaf 𝒮 d).val.map (homOfLE hW).op (t i)) =
        (𝒪 ⊗ projTwistingSheaf 𝒮 d).val.map (homOfLE le_top).op M := by
    intro i W hW
    rw [PresheafOfModules.naturality_apply, ht i, ← PresheafOfModules.map_comp_apply]
    rfl
  obtain ⟨T, hT⟩ := modules_glue (ℐ.toModules ⊗ projTwistingSheaf 𝒮 d) V hcover t fun i k =>
    whiskerRight_idealι_injective ℐ d (g i) ((inf_le_left : V i ⊓ V k ≤ V i).trans (hVg i))
      ((hres_t i (V i ⊓ V k) inf_le_left).trans (hres_t k (V i ⊓ V k) inf_le_right).symm)
  refine ⟨T, ?_⟩
  change (idealι ℐ ▷ projTwistingSheaf 𝒮 d).val.app (op ⊤) T = M
  refine modules_ext (𝒪 ⊗ projTwistingSheaf 𝒮 d) V hcover _ _ fun i => ?_
  have h1 : (idealι ℐ ▷ projTwistingSheaf 𝒮 d).val.app (op (V i))
      ((ℐ.toModules ⊗ projTwistingSheaf 𝒮 d).val.map (homOfLE (le_top : V i ≤ ⊤)).op T) =
      (𝒪 ⊗ projTwistingSheaf 𝒮 d).val.map (homOfLE (le_top : V i ≤ ⊤)).op
        ((idealι ℐ ▷ projTwistingSheaf 𝒮 d).val.app (op ⊤) T) :=
    PresheafOfModules.naturality_apply (idealι ℐ ▷ projTwistingSheaf 𝒮 d).val _ T
  have h2 : (idealι ℐ ▷ projTwistingSheaf 𝒮 d).val.app (op (V i))
      ((ℐ.toModules ⊗ projTwistingSheaf 𝒮 d).val.map (homOfLE (le_top : V i ≤ ⊤)).op T) =
      (idealι ℐ ▷ projTwistingSheaf 𝒮 d).val.app (op (V i)) (t i) :=
    congrArg (fun x => (idealι ℐ ▷ projTwistingSheaf 𝒮 d).val.app (op (V i)) x) (hT i)
  exact h1.symm.trans (h2.trans (ht i))

/-- **Saturated elements of `Γ_*(ℐ) ∩ S`.** If `s ∈ S_d` and `xᵢⁿ s ∈ Γ_*(ℐ) ∩ S` for every `i`,
then `s ∈ Γ_*(ℐ) ∩ S`: the sections `s / xᵢᵈ ⊗ xᵢᵈ` of `ℐ(d)` over `D₊(xᵢ)` glue to a global
section of `ℐ(d)` mapping to `s`. -/
private theorem mem_gammaStarIdeal_of_pow_mul_mem (ℐ : QuasicoherentIdealSubsheaf (Proj 𝒮))
    {d : ℕ} {s : MvPolynomial (Fin (r + 1)) R} (hs : s ∈ 𝒮 d)
    (hsat : ∀ i : Fin (r + 1), ∃ n : ℕ, X i ^ n * s ∈ gammaStarIdeal R r ℐ) :
    s ∈ gammaStarIdeal R r ℐ := by
  rw [mem_gammaStarIdeal_iff ℐ hs]
  set M := sectionRingMap R r s d with hM
  let V : Fin (r + 1) → (Proj 𝒮).Opens := fun i =>
    Proj.basicOpen 𝒮 (X i : MvPolynomial (Fin (r + 1)) R)
  let g : Fin (r + 1) → 𝒮 d := fun i => ⟨X i ^ d, X_pow_mem i d⟩
  have hVg : ∀ i, V i ≤ Proj.basicOpen 𝒮 (g i : MvPolynomial (Fin (r + 1)) R) := fun i =>
    basicOpen_le_basicOpen_pow _ d
  -- the section `s / xᵢᵈ` of `𝒪_X` over `D₊(xᵢ)` lies in `ℐ`
  let a : ∀ i, Γ(Proj 𝒮, V i) := fun i =>
    (Proj 𝒮).presheaf.map (homOfLE (hVg i)).op (ringFrac d ⟨s, hs⟩ (g i))
  have ha : ∀ i, a i ∈ ℐ.ideal (V i) := by
    intro i
    obtain ⟨n, hn⟩ := hsat i
    have hc : (X i : MvPolynomial (Fin (r + 1)) R) ^ n * s ∈ 𝒮 (n + d) :=
      SetLike.GradedMul.mul_mem (X_pow_mem i n) hs
    have hmem := ringFrac_mem_ideal ℐ ⟨_, hc⟩ ⟨_, X_pow_mem i (n + d)⟩ hn
    have hle : V i ≤ Proj.basicOpen 𝒮 ((X i : MvPolynomial (Fin (r + 1)) R) ^ (n + d)) :=
      basicOpen_le_basicOpen_pow _ _
    have hres := ArtinReesKernelSheaf.res_mem ℐ.carrier hle hmem
    rw [ArtinReesKernelSheaf.res_apply] at hres
    have key : a i = (Proj 𝒮).presheaf.map (homOfLE hle).op
        (ringFrac (n + d) ⟨_, hc⟩ ⟨_, X_pow_mem i (n + d)⟩) := by
      apply proj_section_ext
      intro y
      change HomogeneousLocalization.val (HomogeneousLocalization.mk _) =
        HomogeneousLocalization.val (HomogeneousLocalization.mk _)
      rw [HomogeneousLocalization.val_mk, HomogeneousLocalization.val_mk,
        Localization.mk_eq_mk_iff, Localization.r_iff_exists]
      exact ⟨1, by simp only [OneMemClass.coe_one, one_mul]; ring⟩
    rw [key]
    exact hres
  -- the local sections `s / xᵢᵈ ⊗ xᵢᵈ` of `ℐ(d)`
  let u : ∀ i, ℐ.toModules.val.obj (op (V i)) := fun i =>
    (show ℐ.carrier.obj (op (V i)) from ⟨a i, ha i⟩)
  let t : ∀ i, (ℐ.toModules ⊗ projTwistingSheaf 𝒮 d).val.obj (op (V i)) := fun i =>
    (secMap ℐ.toModules d (g i)).val.app (op (V i)) (u i)
  have ht : ∀ i, (idealι ℐ ▷ projTwistingSheaf 𝒮 d).val.app (op (V i)) (t i) =
      (𝒪 ⊗ projTwistingSheaf 𝒮 d).val.map (homOfLE le_top).op M := by
    intro i
    have nat : (secMap 𝒪 d (g i)).val.app (op (V i)) ((idealι ℐ).val.app (op (V i)) (u i)) =
        (idealι ℐ ▷ projTwistingSheaf 𝒮 d).val.app (op (V i)) (t i) :=
      congrArg (fun f => f.val.app (op (V i)) (u i)) (secMap_naturality (idealι ℐ) d (g i))
    rw [← nat, idealι_app]
    have hfr := frac_sectionRingMap (R := R) (r := r) d ⟨s, hs⟩ (g i)
    have e : (u i).1 = (𝒪).val.map (homOfLE (hVg i)).op (frac 𝒪 d (g i) M) := by
      rw [hM, hfr]
      rfl
    rw [e]
    exact secMap_frac_res 𝒪 d (g i) M (hVg i)
  exact glue_twistGlobalMap_idealι ℐ d M V iSup_basicOpen_X_eq_top.ge g hVg t ht

/-- **Hartshorne II, Exercise 5.10(c), saturation.** For a quasi-coherent ideal sheaf `ℐ` on
`ℙʳ_R = Proj S`, the homogeneous ideal `Γ_*(ℐ) ∩ S` is saturated. -/
theorem saturation_gammaStarIdeal (ℐ : QuasicoherentIdealSubsheaf (Proj 𝒮)) :
    saturation (gammaStarIdeal R r ℐ).toIdeal = (gammaStarIdeal R r ℐ).toIdeal := by
  refine le_antisymm (fun s hs => ?_) (le_saturation _)
  rw [(gammaStarIdeal R r ℐ).isHomogeneous.mem_iff]
  intro d
  exact mem_gammaStarIdeal_of_pow_mul_mem ℐ (SetLike.coe_mem _)
    (saturation_isHomogeneous (gammaStarIdeal R r ℐ).isHomogeneous d hs)

/-- **Hartshorne II, Exercise 5.10(c), maximality.** Every homogeneous ideal `I` whose closed
subscheme `Proj (S/I)` has ideal sheaf `ℐ` is contained in `Γ_*(ℐ) ∩ S`. -/
theorem le_gammaStarIdeal_of_ker_eq (ℐ : QuasicoherentIdealSubsheaf (Proj 𝒮))
    (I : HomogeneousIdeal 𝒮) (h : (projQuotientι 𝒮 I).ker = quasicoherentIdealSubsheafEquiv ℐ) :
    I ≤ gammaStarIdeal R r ℐ := by
  have h' := (ker_projQuotientι_eq_iff I (gammaStarIdeal R r ℐ)).1
    (h.trans (ker_projQuotientι_gammaStarIdeal ℐ).symm)
  intro s hs
  have hs' := le_saturation I.toIdeal hs
  rw [h', saturation_gammaStarIdeal] at hs'
  exact hs'

/-- **`Γ_*(Ĩ) ∩ S = I^sat`**: the homogeneous ideal `Γ_*(ℐ) ∩ S` of the ideal sheaf `ℐ` of the
closed subscheme `Proj (S/I)` defined by a homogeneous ideal `I` is the saturation of `I`
(supplementing Hartshorne II, Exercise 5.10). -/
theorem gammaStarIdeal_ker_projQuotientι (I : HomogeneousIdeal 𝒮) :
    (gammaStarIdeal R r (quasicoherentIdealSubsheafEquiv.symm (projQuotientι 𝒮 I).ker)).toIdeal =
      saturation I.toIdeal := by
  rw [← saturation_gammaStarIdeal, ← ker_projQuotientι_eq_iff, ker_projQuotientι_gammaStarIdeal,
    Equiv.apply_symm_apply]

/-- **Hartshorne II, Exercise 5.10(c).** For a closed subscheme `f : Y ⟶ ℙʳ_R = Proj S` with ideal
sheaf `I_Y = ker f`, the homogeneous ideal `Γ_*(I_Y) ∩ S` is the largest homogeneous ideal `I`
whose closed subscheme `Proj (S/I) ⟶ ℙʳ_R` has ideal sheaf `I_Y` (it is saturated by
`saturation_gammaStarIdeal`). Stated for any morphism `f`, with `I_Y` its ideal sheaf. -/
theorem isGreatest_gammaStarIdeal {Y : Scheme.{u}} (f : Y ⟶ Proj 𝒮) :
    IsGreatest {I : HomogeneousIdeal 𝒮 | (projQuotientι 𝒮 I).ker = f.ker}
      (gammaStarIdeal R r (quasicoherentIdealSubsheafEquiv.symm f.ker)) :=
  ⟨ker_projQuotientι_gammaStarIdeal_eq_ker f, fun I hI =>
    le_gammaStarIdeal_of_ker_eq _ I (hI.trans (Equiv.apply_symm_apply _ _).symm)⟩

end ProjectiveClosedSubscheme

end Hartshorne

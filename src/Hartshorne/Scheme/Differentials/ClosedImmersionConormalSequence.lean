/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.Differentials.ImmersionConormalSheaf
import Hartshorne.Scheme.Differentials.RelativeDifferentialsTransitivity
import Hartshorne.Scheme.EffectiveCartierIdealSheaf

/-!
# The conormal sequence of a closed immersion

Hartshorne, *Algebraic Geometry*, II, Proposition 8.12 (p. 176).

Let `i : Z ⟶ X` be a closed immersion with ideal sheaf `I` and let `f : X ⟶ Y` be a morphism.
The sequence of `𝒪_Z`-modules

`i^* I ⟶ i^* Ω_{X/Y} ⟶ Ω_{Z/Y} ⟶ 0`

is exact (`Hartshorne.ClosedConormal.closedImmersion_conormal_exact`). The left term is the
conormal sheaf `i^* I` of `i`; its pushforward `i_* i^* I` is `I/I²`
(`Hartshorne.isIso_idealSheafSqQuotientToPushforward`). The first map is adjoint to the
`𝒪_X`-linear map `I ⟶ i_* i^* Ω_{X/Y}`, `a ↦ 1 ⊗ d a`, and the second map is the first map of the
transitivity sequence (`pullbackRelativeDifferentialsToComp`). Injectivity of the first map is not
claimed.

## Proof

We show that the second map is a cokernel of the first. A map `τ : i^* Ω_{X/Y} ⟶ M` killing the
image of `i^* I` gives, by adjunction, a derivation `a ↦ τ(1 ⊗ d a)` of `𝒪_X` into `i_* M` over
`Y` that kills `I`. Such a derivation descends to a derivation of `𝒪_Z` into `M` over `Y`
(section `Descent`). Every section of `𝒪_Z` lifts locally to `𝒪_X`, because the stalk maps of
`i` are surjective. Two local lifts differ, near each point, by a section of `I`, which the
derivation kills. The values on local lifts therefore glue in the sheaf `M`. The universal
property of `Ω_{Z/Y}` then gives the factorization, and the same local description gives its
uniqueness.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

namespace Hartshorne.ClosedConormal

variable {Z X : Scheme.{u}}

section Restriction

private theorem modules_res_res (M : Z.Modules) {A B C : Z.Opens} (h₁ : A ≤ B) (h₂ : B ≤ C)
    (m : Γ(M, C)) :
    M.presheaf.map (homOfLE h₁).op (M.presheaf.map (homOfLE h₂).op m) =
      M.presheaf.map (homOfLE (h₁.trans h₂)).op m := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

private theorem ring_res_res (Z : Scheme.{u}) {A B C : Z.Opens} (h₁ : A ≤ B) (h₂ : B ≤ C)
    (s : Γ(Z, C)) :
    Z.presheaf.map (homOfLE h₁).op (Z.presheaf.map (homOfLE h₂).op s) =
      Z.presheaf.map (homOfLE (h₁.trans h₂)).op s := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

private theorem app_res (i : Z ⟶ X) {U U' : X.Opens} (h : U' ≤ U) (t : Γ(X, U)) :
    i.app U' (X.presheaf.map (homOfLE h).op t) =
      Z.presheaf.map (homOfLE (fun _ hx => h hx : i ⁻¹ᵁ U' ≤ i ⁻¹ᵁ U)).op (i.app U t) := by
  have := congr(ConcreteCategory.hom $(i.naturality (homOfLE h).op) t)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at this
  exact this

end Restriction

section Descent

variable (i : Z ⟶ X) [IsClosedImmersion i] {M : Z.Modules}
  (δ : ∀ U : X.Opens, Γ(X, U) →+ Γ(M, i ⁻¹ᵁ U))

/-- `t ∈ Γ(X, U)` lifts `s ∈ Γ(Z, V)` on `W ⊆ i⁻¹ U ∩ V`. -/
private def IsLift {V : Z.Opens} (s : Γ(Z, V)) {U : X.Opens} (t : Γ(X, U)) {W : Z.Opens}
    (hWU : W ≤ i ⁻¹ᵁ U) (hWV : W ≤ V) : Prop :=
  Z.presheaf.map (homOfLE hWU).op (i.app U t) = Z.presheaf.map (homOfLE hWV).op s

/-- `m` restricts to `δ t` on every `W` on which `t` lifts `s`. -/
private def Good {V : Z.Opens} (s : Γ(Z, V)) (m : Γ(M, V)) : Prop :=
  ∀ (U : X.Opens) (t : Γ(X, U)) (W : Z.Opens) (hWU : W ≤ i ⁻¹ᵁ U) (hWV : W ≤ V),
    IsLift i s t hWU hWV →
      M.presheaf.map (homOfLE hWV).op m = M.presheaf.map (homOfLE hWU).op (δ U t)

/-- Every section of `𝒪_Z` lifts locally to `𝒪_X`. -/
theorem exists_lift {V : Z.Opens} (s : Γ(Z, V)) (z : Z) (hz : z ∈ V) :
    ∃ (U : X.Opens) (t : Γ(X, U)) (W : Z.Opens) (hWU : W ≤ i ⁻¹ᵁ U) (hWV : W ≤ V),
      z ∈ W ∧ IsLift i s t hWU hWV := by
  obtain ⟨a, ha⟩ := i.stalkMap_surjective z (Z.presheaf.germ V z hz s)
  obtain ⟨U, hU, t, rfl⟩ := X.presheaf.exists_germ_eq a
  erw [Scheme.Hom.germ_stalkMap_apply i U z hU] at ha
  obtain ⟨W, hzW, j₁, j₂, hW⟩ := Z.presheaf.germ_eq z (U := i ⁻¹ᵁ U) (V := V) hU hz _ _ ha
  exact ⟨U, t, W, j₁.le, j₂.le, hzW, hW⟩

omit [IsClosedImmersion i] in
theorem lift_restrict {V : Z.Opens} {s : Γ(Z, V)} {U : X.Opens} {t : Γ(X, U)} {W : Z.Opens}
    {hWU : W ≤ i ⁻¹ᵁ U} {hWV : W ≤ V} (hl : IsLift i s t hWU hWV) {U' : X.Opens} (hU' : U' ≤ U)
    {W' : Z.Opens} (hW' : W' ≤ W) (hW'U' : W' ≤ i ⁻¹ᵁ U') :
    IsLift i s (X.presheaf.map (homOfLE hU').op t) hW'U' (hW'.trans hWV) := by
  unfold IsLift at hl ⊢
  erw [app_res, ring_res_res, ← ring_res_res Z hW' hWV, ← hl, ring_res_res]

variable (hδmap : ∀ {U U' : X.Opens} (h : U' ≤ U) (t : Γ(X, U)),
    δ U' (X.presheaf.map (homOfLE h).op t) =
      M.presheaf.map (homOfLE (fun _ hx => h hx : i ⁻¹ᵁ U' ≤ i ⁻¹ᵁ U)).op (δ U t))
  (hδker : ∀ (U : X.Opens) (t : Γ(X, U)), i.app U t = 0 → δ U t = 0)

include hδmap hδker in
/-- `δ t` vanishes wherever `t` vanishes on `Z`. -/
theorem res_δ_eq_zero {U : X.Opens} (t : Γ(X, U)) {W : Z.Opens} (hWU : W ≤ i ⁻¹ᵁ U)
    (h0 : Z.presheaf.map (homOfLE hWU).op (i.app U t) = 0) :
    M.presheaf.map (homOfLE hWU).op (δ U t) = 0 := by
  obtain ⟨O, hO, hOW⟩ := i.isClosedEmbedding.isInducing.isOpen_iff.mp W.2
  let U'' : X.Opens := U ⊓ ⟨O, hO⟩
  have h1 : i ⁻¹ᵁ U'' ≤ W := fun z hz => by
    have : z ∈ i ⁻¹' O := hz.2
    rw [hOW] at this
    exact this
  have h2 : W ≤ i ⁻¹ᵁ U'' := fun z hz => ⟨hWU hz, by
    show z ∈ i ⁻¹' O
    rw [hOW]
    exact hz⟩
  have h3 : i.app U'' (X.presheaf.map (homOfLE (inf_le_left : U'' ≤ U)).op t) = 0 := by
    refine (app_res i (inf_le_left : U'' ≤ U) t).trans ?_
    refine (ring_res_res Z h1 hWU (i.app U t)).symm.trans ?_
    rw [h0, map_zero]
  refine (modules_res_res M h2 (fun _ hx => (inf_le_left : U'' ≤ U) hx) (δ U t)).symm.trans ?_
  rw [← hδmap, hδker _ _ h3, map_zero]

include hδmap hδker in
/-- Two lifts of the same section give the same `δ` on a common open. -/
theorem lift_compat {V : Z.Opens} {s : Γ(Z, V)} {U₁ U₂ : X.Opens} {t₁ : Γ(X, U₁)}
    {t₂ : Γ(X, U₂)} {W₁ W₂ : Z.Opens} {h₁U : W₁ ≤ i ⁻¹ᵁ U₁} {h₁V : W₁ ≤ V}
    {h₂U : W₂ ≤ i ⁻¹ᵁ U₂} {h₂V : W₂ ≤ V} (hl₁ : IsLift i s t₁ h₁U h₁V)
    (hl₂ : IsLift i s t₂ h₂U h₂V) {W : Z.Opens} (hW₁ : W ≤ W₁) (hW₂ : W ≤ W₂) :
    M.presheaf.map (homOfLE (hW₁.trans h₁U)).op (δ U₁ t₁) =
      M.presheaf.map (homOfLE (hW₂.trans h₂U)).op (δ U₂ t₂) := by
  let U₀ : X.Opens := U₁ ⊓ U₂
  have hW₀ : W ≤ i ⁻¹ᵁ U₀ := fun z hz => ⟨h₁U (hW₁ hz), h₂U (hW₂ hz)⟩
  let t : Γ(X, U₀) := X.presheaf.map (homOfLE (inf_le_left : U₀ ≤ U₁)).op t₁ -
    X.presheaf.map (homOfLE (inf_le_right : U₀ ≤ U₂)).op t₂
  have h0 : Z.presheaf.map (homOfLE hW₀).op (i.app U₀ t) = 0 := by
    have e₁ := lift_restrict i hl₁ (inf_le_left : U₀ ≤ U₁) hW₁ hW₀
    have e₂ := lift_restrict i hl₂ (inf_le_right : U₀ ≤ U₂) hW₂ hW₀
    unfold IsLift at e₁ e₂
    rw [map_sub, map_sub, e₁, e₂, sub_self]
  have := res_δ_eq_zero i δ hδmap hδker t hW₀ h0
  rw [map_sub, map_sub, hδmap, hδmap] at this
  erw [modules_res_res, modules_res_res, sub_eq_zero] at this
  exact this

include hδmap hδker in
/-- A section that restricts to `δ` of local lifts near every point is good. -/
theorem good_of_local {V : Z.Opens} (s : Γ(Z, V)) (m : Γ(M, V))
    (h : ∀ z ∈ V, ∃ (U : X.Opens) (t : Γ(X, U)) (W : Z.Opens) (hWU : W ≤ i ⁻¹ᵁ U) (hWV : W ≤ V),
      z ∈ W ∧ IsLift i s t hWU hWV ∧
        M.presheaf.map (homOfLE hWV).op m = M.presheaf.map (homOfLE hWU).op (δ U t)) :
    Good i δ s m := by
  intro U' t' W' hW'U hW'V hl'
  rw [← sub_eq_zero]
  refine Scheme.Modules.section_eq_zero_of_locally _ fun w hw => ?_
  obtain ⟨U, t, W, hWU, hWV, hwW, hl, hm⟩ := h w (hW'V hw)
  refine ⟨W' ⊓ W, inf_le_left, ⟨hw, hwW⟩, ?_⟩
  rw [map_sub, sub_eq_zero]
  erw [modules_res_res, modules_res_res,
    ← modules_res_res M (inf_le_right : W' ⊓ W ≤ W) hWV, hm, modules_res_res]
  exact lift_compat i δ hδmap hδker hl hl' inf_le_right inf_le_left

/-- Good sections are unique, given local lifts. -/
theorem good_unique {V : Z.Opens} {s : Γ(Z, V)} {m m' : Γ(M, V)}
    (hm : Good i δ s m) (hm' : Good i δ s m') : m = m' := by
  rw [← sub_eq_zero]
  refine Scheme.Modules.section_eq_zero_of_locally _ fun z hz => ?_
  obtain ⟨U, t, W, hWU, hWV, hzW, hl⟩ := exists_lift i s z hz
  exact ⟨W, hWV, hzW, by rw [map_sub, hm _ _ _ _ _ hl, hm' _ _ _ _ _ hl, sub_self]⟩

include hδmap hδker in
/-- Every section of `𝒪_Z` has a good section of `M`, glued from `δ` of local lifts. -/
theorem exists_good {V : Z.Opens} (s : Γ(Z, V)) : ∃ m : Γ(M, V), Good i δ s m := by
  choose U t W hWU hWV hzW hl using fun z : V => exists_lift i s z.1 z.2
  let F : TopCat.Sheaf Ab.{u} Z := ⟨M.presheaf, M.isSheaf⟩
  have hcomp : TopCat.Presheaf.IsCompatible F.1 W
      (fun z => M.presheaf.map (homOfLE (hWU z)).op (δ (U z) (t z))) := by
    intro a b
    change M.presheaf.map (homOfLE inf_le_left).op (M.presheaf.map (homOfLE (hWU a)).op _) =
      M.presheaf.map (homOfLE inf_le_right).op (M.presheaf.map (homOfLE (hWU b)).op _)
    erw [modules_res_res, modules_res_res]
    exact lift_compat i δ hδmap hδker (hl a) (hl b) inf_le_left inf_le_right
  obtain ⟨m, hm, -⟩ := F.existsUnique_gluing' W V (fun z => homOfLE (hWV z))
    (fun z hz => Opens.mem_iSup.mpr ⟨⟨z, hz⟩, hzW ⟨z, hz⟩⟩) _ hcomp
  exact ⟨m, good_of_local i δ hδmap hδker s m fun z hz =>
    ⟨U ⟨z, hz⟩, t ⟨z, hz⟩, W ⟨z, hz⟩, hWU _, hWV _, hzW _, hl _, hm ⟨z, hz⟩⟩⟩

/-- The descended map `Γ(Z, V) → Γ(M, V)`. -/
private noncomputable def descD {V : Z.Opens} (s : Γ(Z, V)) : Γ(M, V) :=
  (exists_good i δ hδmap hδker s).choose

theorem good_descD {V : Z.Opens} (s : Γ(Z, V)) : Good i δ s (descD i δ hδmap hδker s) :=
  (exists_good i δ hδmap hδker s).choose_spec

theorem descD_app (U : X.Opens) (t : Γ(X, U)) :
    descD i δ hδmap hδker (i.app U t) = δ U t := by
  refine good_unique i δ (good_descD i δ hδmap hδker _) fun U' t' W hWU hWV hl => ?_
  have hl₀ : IsLift i (i.app U t) t hWV hWV := rfl
  exact lift_compat i δ hδmap hδker hl₀ hl le_rfl le_rfl

/-- Restricting a good section along a restricted lift. -/
theorem descD_res_lift {V : Z.Opens} {s : Γ(Z, V)} {U : X.Opens} {t : Γ(X, U)} {W : Z.Opens}
    {hWU : W ≤ i ⁻¹ᵁ U} {hWV : W ≤ V} (hl : IsLift i s t hWU hWV) {U' : X.Opens} (hU' : U' ≤ U)
    {W' : Z.Opens} (hW' : W' ≤ W) (hW'U' : W' ≤ i ⁻¹ᵁ U') :
    M.presheaf.map (homOfLE (hW'.trans hWV)).op (descD i δ hδmap hδker s) =
      M.presheaf.map (homOfLE hW'U').op (δ U' (X.presheaf.map (homOfLE hU').op t)) :=
  good_descD i δ hδmap hδker s _ _ _ _ _ (lift_restrict i hl hU' hW' hW'U')

theorem descD_add {V : Z.Opens} (s s' : Γ(Z, V)) :
    descD i δ hδmap hδker (s + s') = descD i δ hδmap hδker s + descD i δ hδmap hδker s' := by
  refine good_unique i δ (good_descD i δ hδmap hδker _)
    (good_of_local i δ hδmap hδker _ _ fun z hz => ?_)
  obtain ⟨U₁, t₁, W₁, h₁U, h₁V, hz₁, hl₁⟩ := exists_lift i s z hz
  obtain ⟨U₂, t₂, W₂, h₂U, h₂V, hz₂, hl₂⟩ := exists_lift i s' z hz
  let U₀ : X.Opens := U₁ ⊓ U₂
  let W₀ : Z.Opens := W₁ ⊓ W₂
  have hW₀ : W₀ ≤ i ⁻¹ᵁ U₀ := fun w hw => ⟨h₁U hw.1, h₂U hw.2⟩
  have e₁ := lift_restrict i hl₁ (inf_le_left : U₀ ≤ U₁) (inf_le_left : W₀ ≤ W₁) hW₀
  have e₂ := lift_restrict i hl₂ (inf_le_right : U₀ ≤ U₂) (inf_le_right : W₀ ≤ W₂) hW₀
  refine ⟨U₀, X.presheaf.map (homOfLE (inf_le_left : U₀ ≤ U₁)).op t₁ +
    X.presheaf.map (homOfLE (inf_le_right : U₀ ≤ U₂)).op t₂, W₀, hW₀,
    (inf_le_left : W₀ ≤ W₁).trans h₁V, ⟨hz₁, hz₂⟩, ?_, ?_⟩
  · unfold IsLift at e₁ e₂ ⊢
    rw [map_add, map_add, e₁, e₂, map_add]
  · rw [map_add, map_add, map_add]
    have d₁ := descD_res_lift i δ hδmap hδker hl₁ (inf_le_left : U₀ ≤ U₁)
      (inf_le_left : W₀ ≤ W₁) hW₀
    have d₂ := descD_res_lift i δ hδmap hδker hl₂ (inf_le_right : U₀ ≤ U₂)
      (inf_le_right : W₀ ≤ W₂) hW₀
    rw [← d₁, ← d₂]

theorem descD_res {V V' : Z.Opens} (h : V' ≤ V) (s : Γ(Z, V)) :
    descD i δ hδmap hδker (Z.presheaf.map (homOfLE h).op s) =
      M.presheaf.map (homOfLE h).op (descD i δ hδmap hδker s) := by
  refine good_unique i δ (good_descD i δ hδmap hδker _) fun U t W hWU hWV hl => ?_
  have hl' : IsLift i s t hWU (hWV.trans h) := by
    unfold IsLift at hl ⊢
    erw [hl, ring_res_res]
  erw [modules_res_res]
  exact good_descD i δ hδmap hδker s _ _ _ _ _ hl'

variable (hδmul : ∀ (U : X.Opens) (a b : Γ(X, U)),
    δ U (a * b) = i.app U a • δ U b + i.app U b • δ U a)

include hδmul in
theorem descD_mul {V : Z.Opens} (s s' : Γ(Z, V)) :
    descD i δ hδmap hδker (s * s') =
      s • descD i δ hδmap hδker s' + s' • descD i δ hδmap hδker s := by
  refine good_unique i δ (good_descD i δ hδmap hδker _)
    (good_of_local i δ hδmap hδker _ _ fun z hz => ?_)
  obtain ⟨U₁, t₁, W₁, h₁U, h₁V, hz₁, hl₁⟩ := exists_lift i s z hz
  obtain ⟨U₂, t₂, W₂, h₂U, h₂V, hz₂, hl₂⟩ := exists_lift i s' z hz
  let U₀ : X.Opens := U₁ ⊓ U₂
  let W₀ : Z.Opens := W₁ ⊓ W₂
  have hW₀ : W₀ ≤ i ⁻¹ᵁ U₀ := fun w hw => ⟨h₁U hw.1, h₂U hw.2⟩
  have e₁ := lift_restrict i hl₁ (inf_le_left : U₀ ≤ U₁) (inf_le_left : W₀ ≤ W₁) hW₀
  have e₂ := lift_restrict i hl₂ (inf_le_right : U₀ ≤ U₂) (inf_le_right : W₀ ≤ W₂) hW₀
  refine ⟨U₀, X.presheaf.map (homOfLE (inf_le_left : U₀ ≤ U₁)).op t₁ *
    X.presheaf.map (homOfLE (inf_le_right : U₀ ≤ U₂)).op t₂, W₀, hW₀,
    (inf_le_left : W₀ ≤ W₁).trans h₁V, ⟨hz₁, hz₂⟩, ?_, ?_⟩
  · unfold IsLift at e₁ e₂ ⊢
    rw [map_mul, map_mul, e₁, e₂, map_mul]
  · have d₁ := descD_res_lift i δ hδmap hδker hl₁ (inf_le_left : U₀ ≤ U₁)
      (inf_le_left : W₀ ≤ W₁) hW₀
    have d₂ := descD_res_lift i δ hδmap hδker hl₂ (inf_le_right : U₀ ≤ U₂)
      (inf_le_right : W₀ ≤ W₂) hW₀
    unfold IsLift at e₁ e₂
    rw [hδmul, map_add, map_add, Scheme.Modules.map_smul, Scheme.Modules.map_smul,
      Scheme.Modules.map_smul, Scheme.Modules.map_smul, ← d₁, ← d₂, ← e₁, ← e₂]

end Descent

end Hartshorne.ClosedConormal

namespace Hartshorne.ClosedConormal

open Scheme

variable {Z X Y : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (f : X ⟶ Y)

/-- The unit `Ω_{X/Y} ⟶ i_* i^* Ω_{X/Y}`. -/
noncomputable abbrev unitΩ :
    relativeDifferentials f ⟶
      (Modules.pushforward i).obj ((Modules.pullback i).obj (relativeDifferentials f)) :=
  (Modules.pullbackPushforwardAdjunction i).unit.app (relativeDifferentials f)

omit [IsClosedImmersion i] in
/-- The sections of `I` vanish on `Z`. -/
theorem app_idealSheafι (U : X.Opens) (a : Γ(closedImmersionIdealSheaf i, U)) :
    i.app U ((closedImmersionIdealSheafι i).app U a) = 0 :=
  congrArg (fun φ => Scheme.Modules.Hom.app φ U a)
    (kernel.condition (structureSheafToPushforward i))

/-- The `𝒪_X`-linear map `I ⟶ i_* i^* Ω_{X/Y}`, `a ↦ 1 ⊗ d a`. -/
noncomputable def idealToPushforward :
    closedImmersionIdealSheaf i ⟶
      (Modules.pushforward i).obj ((Modules.pullback i).obj (relativeDifferentials f)) where
  val := PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom (((unitΩ i f).val.app U).hom.toAddMonoidHom.comp
        (((relativeDifferentialsDerivation f).d (X := U)).comp
          ((closedImmersionIdealSheafι i).val.app U).hom.toAddMonoidHom))
      naturality U V j := by
        ext a
        change (unitΩ i f).val.app V ((relativeDifferentialsDerivation f).d
            ((closedImmersionIdealSheafι i).val.app V
              ((closedImmersionIdealSheaf i).val.map j a))) =
          ((Modules.pushforward i).obj ((Modules.pullback i).obj
            (relativeDifferentials f))).val.map j ((unitΩ i f).val.app U
              ((relativeDifferentialsDerivation f).d ((closedImmersionIdealSheafι i).val.app U a)))
        rw [PresheafOfModules.naturality_apply (closedImmersionIdealSheafι i).val j a]
        erw [(relativeDifferentialsDerivation f).d_map j]
        exact PresheafOfModules.naturality_apply (unitΩ i f).val j _ }
    (fun U r a => by
      change (unitΩ i f).val.app U ((relativeDifferentialsDerivation f).d
          ((closedImmersionIdealSheafι i).val.app U (r • a))) =
        r • (unitΩ i f).val.app U ((relativeDifferentialsDerivation f).d
          ((closedImmersionIdealSheafι i).val.app U a))
      rw [((closedImmersionIdealSheafι i).val.app U).hom.map_smul]
      erw [(relativeDifferentialsDerivation f).d_mul]
      rw [map_add]
      erw [((unitΩ i f).val.app U).hom.map_smul, ((unitΩ i f).val.app U).hom.map_smul]
      have h0 : i.app U.unop ((closedImmersionIdealSheafι i).app U.unop a) = 0 :=
        app_idealSheafι i U.unop a
      refine add_eq_left.mpr ?_
      have hz : ∀ m : Γ((Modules.pullback i).obj (relativeDifferentials f), i ⁻¹ᵁ U.unop),
          i.app U.unop ((closedImmersionIdealSheafι i).app U.unop a) • m = 0 := fun m => by
        rw [h0, zero_smul]
      exact hz _)

/-- The conormal map `i^* I ⟶ i^* Ω_{X/Y}`, adjoint to `a ↦ 1 ⊗ d a`. -/
noncomputable def conormalToPullback :
    (Modules.pullback i).obj (closedImmersionIdealSheaf i) ⟶
      (Modules.pullback i).obj (relativeDifferentials f) :=
  ((Modules.pullbackPushforwardAdjunction i).homEquiv _ _).symm (idealToPushforward i f)

omit [IsClosedImmersion i] in
theorem homEquiv_conormalToPullback :
    (Modules.pullbackPushforwardAdjunction i).homEquiv _ _ (conormalToPullback i f) =
      idealToPushforward i f :=
  Equiv.apply_symm_apply _ _

omit [IsClosedImmersion i] in
/-- The adjoint of `i^*Ω_{X/Y} ⟶ Ω_{Z/Y}` is `Ω_{X/Y} ⟶ i_*Ω_{Z/Y}`, `d a ↦ d (i^♯ a)`. -/
theorem unit_comp_pushforward_map :
    (Modules.pullbackPushforwardAdjunction i).unit.app (relativeDifferentials f) ≫
      (Modules.pushforward i).map (pullbackRelativeDifferentialsToComp i f) =
        relativeDifferentialsToPushforwardComp i f := by
  exact ((Modules.pullbackPushforwardAdjunction i).homEquiv_unit _ _ _).symm.trans
    (pullbackRelativeDifferentialsToComp_homEquiv i f)

omit [IsClosedImmersion i] in
theorem conormalToPullback_comp :
    conormalToPullback i f ≫ pullbackRelativeDifferentialsToComp i f = 0 := by
  apply ((Modules.pullbackPushforwardAdjunction i).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, homEquiv_conormalToPullback,
    Adjunction.homEquiv_unit, Functor.map_zero, comp_zero]
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  ext a
  have h1 := congr(($(unit_comp_pushforward_map i f)).val.app (op V)
    ((relativeDifferentialsDerivation f).d ((closedImmersionIdealSheafι i).val.app (op V) a)))
  have h2 : (relativeDifferentialsToPushforwardComp i f).val.app (op V)
      ((relativeDifferentialsDerivation f).d ((closedImmersionIdealSheafι i).val.app (op V) a)) =
        0 := by
    refine (relativeDifferentialsToPushforwardComp_d i f (op V)
      ((closedImmersionIdealSheafι i).val.app (op V) a)).trans ?_
    have h0 := app_idealSheafι i V a
    change (relativeDifferentialsDerivation (i ≫ f)).d
      (i.app V ((closedImmersionIdealSheafι i).app V a)) = 0
    rw [h0]
    exact map_zero _
  exact (h1.trans h2).trans rfl

section Desc

variable {i f} {M : Z.Modules} (τ : (Modules.pullback i).obj (relativeDifferentials f) ⟶ M)
  (hτ : conormalToPullback i f ≫ τ = 0)

/-- The adjoint `Ω_{X/Y} ⟶ i_* M` of `τ`. -/
noncomputable abbrev τAdj : relativeDifferentials f ⟶ (Modules.pushforward i).obj M :=
  (Modules.pullbackPushforwardAdjunction i).homEquiv _ _ τ

/-- `a ↦ τ(1 ⊗ d a)`, as a family of additive maps `Γ(X, U) → Γ(M, i⁻¹ U)`. -/
noncomputable def descδ (U : X.Opens) : Γ(X, U) →+ Γ(M, i ⁻¹ᵁ U) :=
  ((τAdj τ).val.app (op U)).hom.toAddMonoidHom.comp
    ((relativeDifferentialsDerivation f).d (X := op U))

omit [IsClosedImmersion i] in
theorem descδ_map {U U' : X.Opens} (h : U' ≤ U) (t : Γ(X, U)) :
    descδ τ U' (X.presheaf.map (homOfLE h).op t) =
      M.presheaf.map (homOfLE (fun _ hx => h hx : i ⁻¹ᵁ U' ≤ i ⁻¹ᵁ U)).op (descδ τ U t) := by
  change (τAdj τ).val.app (op U') ((relativeDifferentialsDerivation f).d
    (X.presheaf.map (homOfLE h).op t)) = _
  erw [(relativeDifferentialsDerivation f).d_map]
  exact PresheafOfModules.naturality_apply (τAdj τ).val (homOfLE h).op _

omit [IsClosedImmersion i] in
include hτ in
theorem descδ_ker (U : X.Opens) (t : Γ(X, U)) (ht : i.app U t = 0) : descδ τ U t = 0 := by
  let S : ShortComplex X.Modules := ShortComplex.mk (kernel.ι (structureSheafToPushforward i))
    (structureSheafToPushforward i) (kernel.condition (structureSheafToPushforward i))
  have : Mono S.f := by change Mono (closedImmersionIdealSheafι i); infer_instance
  obtain ⟨a, rfl⟩ := modules_sections_exact (S := S)
    (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)) (U := U) t ht
  have h0 : idealToPushforward i f ≫ (Modules.pushforward i).map τ = 0 := by
    rw [← homEquiv_conormalToPullback, ← Adjunction.homEquiv_naturality_right, hτ,
      Adjunction.homEquiv_unit, Functor.map_zero, comp_zero]
  have h1 := congr(Scheme.Modules.Hom.app $h0 U a)
  have h2 : τAdj τ = (Modules.pullbackPushforwardAdjunction i).unit.app _ ≫
      (Modules.pushforward i).map τ := Adjunction.homEquiv_unit _ _ _ _
  change (τAdj τ).val.app (op U) ((relativeDifferentialsDerivation f).d
    ((closedImmersionIdealSheafι i).val.app (op U) a)) = 0
  rw [h2]
  exact h1.trans rfl

omit [IsClosedImmersion i] in
theorem descδ_mul (U : X.Opens) (a b : Γ(X, U)) :
    descδ τ U (a * b) = i.app U a • descδ τ U b + i.app U b • descδ τ U a := by
  change (τAdj τ).val.app (op U) ((relativeDifferentialsDerivation f).d (a * b)) = _
  erw [(relativeDifferentialsDerivation f).d_mul, map_add,
    ((τAdj τ).val.app (op U)).hom.map_smul, ((τAdj τ).val.app (op U)).hom.map_smul]
  rfl

omit [IsClosedImmersion i] in
theorem descδ_app (V : Y.Opens) (b : Γ(Y, V)) : descδ τ (f ⁻¹ᵁ V) (f.app V b) = 0 := by
  change (τAdj τ).val.app (op (f ⁻¹ᵁ V)) ((relativeDifferentialsDerivation f).d
    (f.c.app (op V) b)) = 0
  have h := (derivationOfInverseImage f (relativeDifferentialsDerivation f)).d_app (X := op V) b
  exact (congrArg (fun x => ((τAdj τ).val.app (op (f ⁻¹ᵁ V))).hom x) h).trans (map_zero _)

/-- The derivation `𝒪_Z ⟶ M` over `Y` descended from `a ↦ τ(1 ⊗ d a)`. -/
noncomputable def descDerivation :
    M.val.Derivation (F := Opens.map (i ≫ f).base) (i ≫ f).c where
  d {V} := AddMonoidHom.mk' (descD i (descδ τ) (descδ_map τ) (descδ_ker τ hτ) (V := V.unop))
    (descD_add i (descδ τ) (descδ_map τ) (descδ_ker τ hτ))
  d_mul {V} a b := descD_mul i (descδ τ) (descδ_map τ) (descδ_ker τ hτ) (descδ_mul τ) a b
  d_map {V W} j a := descD_res i (descδ τ) (descδ_map τ) (descδ_ker τ hτ) j.unop.le a
  d_app {V} b := by
    change descD i (descδ τ) (descδ_map τ) (descδ_ker τ hτ)
      (i.app (f ⁻¹ᵁ V.unop) (f.app V.unop b)) = 0
    rw [descD_app]
    exact descδ_app τ V.unop b

theorem descDerivation_d_app (U : X.Opens) (t : Γ(X, U)) :
    (descDerivation τ hτ).d (i.app U t) = descδ τ U t :=
  descD_app i (descδ τ) (descδ_map τ) (descδ_ker τ hτ) U t

/-- The descended map `Ω_{Z/Y} ⟶ M`. -/
noncomputable def descHom : relativeDifferentials (i ≫ f) ⟶ M :=
  (relativeDifferentialsHomEquiv (i ≫ f) M).symm
    (derivationToInverseImage (i ≫ f) (descDerivation τ hτ))

theorem descHom_d {V : Z.Opens} (s : Γ(Z, V)) :
    (descHom τ hτ).val.app (op V) ((relativeDifferentialsDerivation (i ≫ f)).d s) =
      (descDerivation τ hτ).d s := by
  have h : (relativeDifferentialsDerivation (i ≫ f)).postcomp (descHom τ hτ).val =
      derivationToInverseImage (i ≫ f) (descDerivation τ hτ) := by
    rw [← relativeDifferentialsHomEquiv_apply]
    exact Equiv.apply_symm_apply _ _
  exact PresheafOfModules.Derivation.congr_d h s

end Desc

/-- `i^*Ω_{X/Y} ⟶ Ω_{Z/Y}` is a cokernel of the conormal map `i^* I ⟶ i^*Ω_{X/Y}`. -/
noncomputable def conormalIsColimit :
    IsColimit (CokernelCofork.ofπ (pullbackRelativeDifferentialsToComp i f)
      (conormalToPullback_comp i f)) :=
  CokernelCofork.IsColimit.ofπ _ _ (fun {M} τ hτ => descHom τ hτ)
    (fun {M} τ hτ => by
      apply ((Modules.pullbackPushforwardAdjunction i).homEquiv _ _).injective
      rw [Adjunction.homEquiv_naturality_right, pullbackRelativeDifferentialsToComp_homEquiv]
      apply (relativeDifferentialsHomEquiv f _).injective
      rw [relativeDifferentialsHomEquiv_apply, relativeDifferentialsHomEquiv_apply]
      ext U a
      change (descHom τ hτ).val.app (op (i ⁻¹ᵁ U.unop))
        ((relativeDifferentialsToPushforwardComp i f).val.app U
          ((relativeDifferentialsDerivation f).d a)) = descδ τ U.unop a
      refine (congrArg (fun x => ((descHom τ hτ).val.app (op (i ⁻¹ᵁ U.unop))).hom x)
        (relativeDifferentialsToPushforwardComp_d i f U a)).trans ?_
      exact (descHom_d τ hτ _).trans (descDerivation_d_app τ hτ U.unop a))
    (fun {M} τ hτ m hm => by
      apply (relativeDifferentialsHomEquiv (i ≫ f) M).injective
      rw [relativeDifferentialsHomEquiv_apply, relativeDifferentialsHomEquiv_apply]
      ext V s
      change m.val.app V ((relativeDifferentialsDerivation (i ≫ f)).d s) =
        (descHom τ hτ).val.app V ((relativeDifferentialsDerivation (i ≫ f)).d s)
      refine Eq.trans ?_ (descHom_d τ hτ (V := V.unop) s).symm
      refine good_unique i (descδ τ) ?_ (good_descD i (descδ τ) (descδ_map τ) (descδ_ker τ hτ) s)
      intro U t W hWU hWV hl
      have hm' : relativeDifferentialsToPushforwardComp i f ≫ (Modules.pushforward i).map m =
          τAdj τ := by
        rw [← hm]
        show _ = (Modules.pullbackPushforwardAdjunction i).homEquiv _ _ _
        rw [Adjunction.homEquiv_naturality_right, pullbackRelativeDifferentialsToComp_homEquiv]
      have e₁ : m.val.app (op (i ⁻¹ᵁ U)) ((relativeDifferentialsDerivation (i ≫ f)).d
          (i.app U t)) = descδ τ U t := by
        have h := congr(($hm').val.app (op U) ((relativeDifferentialsDerivation f).d t))
        refine Eq.trans ?_ h
        exact congrArg (fun x => (m.val.app (op (i ⁻¹ᵁ U))).hom x)
          (relativeDifferentialsToPushforwardComp_d i f (op U) t).symm
      unfold IsLift at hl
      show M.val.map (homOfLE hWV).op _ = M.val.map (homOfLE hWU).op _
      refine (PresheafOfModules.naturality_apply m.val (homOfLE hWV).op _).symm.trans ?_
      rw [← e₁]
      refine Eq.trans ?_ (PresheafOfModules.naturality_apply m.val (homOfLE hWU).op _)
      refine congrArg (fun x => (m.val.app (op W)).hom x) ?_
      erw [← (relativeDifferentialsDerivation (i ≫ f)).d_map,
        ← (relativeDifferentialsDerivation (i ≫ f)).d_map, hl]
      rfl)

/-- **The conormal sequence of a closed immersion** (Hartshorne II, Proposition 8.12). For a
closed immersion `i : Z ⟶ X` with ideal sheaf `I` and a morphism `f : X ⟶ Y`, the sequence
`i^* I ⟶ i^* Ω_{X/Y} ⟶ Ω_{Z/Y} ⟶ 0` of `𝒪_Z`-modules is exact. Here `i^* I` is the conormal sheaf
of `i`, whose pushforward `i_* i^* I` is `I/I²` (`isIso_idealSheafSqQuotientToPushforward`). -/
theorem closedImmersion_conormal_exact :
    (ShortComplex.mk (conormalToPullback i f) (pullbackRelativeDifferentialsToComp i f)
      (conormalToPullback_comp i f)).Exact ∧ Epi (pullbackRelativeDifferentialsToComp i f) :=
  (ShortComplex.exact_and_epi_g_iff_g_is_cokernel _).2 ⟨conormalIsColimit i f⟩

end Hartshorne.ClosedConormal

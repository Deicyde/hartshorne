/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.IdealOfDefinition
import Mathlib.RingTheory.Noetherian.Nilpotent

/-!
# Ideals of definition are cofinal

Hartshorne, *Algebraic Geometry*, II.9, Proposition 9.5(a) (pp. 196–197).

* `Hartshorne.IsIdealOfDefinition.exists_pow_le_and_pow_le`: if `J₁` and `J₂` are ideals of
  definition on a Noetherian formal scheme `X`, there are positive integers `a`, `b` with
  `J₂ ^ a ⊆ J₁` and `J₁ ^ b ⊆ J₂`.
* `Hartshorne.IsIdealOfDefinition.exists_pow_le`: one direction, `J₂ ^ a ⊆ J₁` for some `a > 0`,
  which only uses that `J₁` is an ideal of definition and that `Supp (𝒪_X / J₂) = X`.

Proof outline. On the Noetherian scheme `Y = (X, 𝒪_X / J₁)`, the image of a section
`g` of `J₂` has empty principal open: if its germ at `x` were a unit, then near `x` some
`g t - 1` would lie in `J₁`; as `Supp (𝒪_X / J₁) = X` the germ of `g t - 1` is not a unit of the
local ring `𝒪_{X,x}`, so the germ of `g t` is a unit and `J₂` would contain `1` near `x`,
contradicting `Supp (𝒪_X / J₂) = X`. On an affine open `Spec B` of `Y`, an element with empty
principal open is nilpotent (Hartshorne II, Exercise 2.18(a)), so the image of `J₂` is a nil ideal.
Cover `Y` by finitely many affine opens `Spec Bᵢ`, `Bᵢ` Noetherian, with `(nil Bᵢ) ^ N = 0`; then
the nilradical of every stalk of `Y` (a localization of some `Bᵢ`) has vanishing `N`-th power,
so every section of `J₂ ^ N` maps to zero in every stalk of `Y`, i.e. lies in `J₁`.
-/

noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace Hartshorne

universe u

namespace IdealSubsheaf

variable {T : TopCat.{u}} {R : TopCat.Sheaf CommRingCat.{u} T} (J : IdealSubsheaf R)

private lemma quotientπ_hom_eq :
    J.quotientπ.hom = J.quotientPresheafπ ≫ toSheafify (Opens.grothendieckTopology T)
        (idealQuotientPresheaf R J.ideal J.ideal_le_comap) := by
  rw [toSheafify_naturality]
  rfl

private lemma quotientπ_app_apply (U : Opens T) (s : R.presheaf.obj (op U)) :
    J.quotientπ.hom.app (op U) s = (toSheafify (Opens.grothendieckTopology T)
        (idealQuotientPresheaf R J.ideal J.ideal_le_comap)).app (op U)
        (Ideal.Quotient.mk (J.ideal U) s) := by
  rw [quotientπ_hom_eq]
  rfl

/-- The kernel of `R(U) → (R / J)(U)` is `J(U)`. -/
private lemma quotientπ_app_eq_zero_iff (U : Opens T) (s : R.presheaf.obj (op U)) :
    J.quotientπ.hom.app (op U) s = 0 ↔ s ∈ J.ideal U := by
  constructor
  · intro hs
    rw [quotientπ_app_apply] at hs
    have hmem := Presheaf.equalizerSieve_mem (Opens.grothendieckTopology T)
      (toSheafify (Opens.grothendieckTopology T)
        (idealQuotientPresheaf R J.ideal J.ideal_le_comap)) (X := op U)
        (Ideal.Quotient.mk (J.ideal U) s) 0 (hs.trans (map_zero _).symm)
    refine J.mem_ideal_of_locally s fun x hx => ?_
    obtain ⟨V, f, hf, hxV⟩ := hmem x hx
    refine ⟨V, leOfHom f, hxV, ?_⟩
    have hf' : (idealQuotientPresheaf R J.ideal J.ideal_le_comap).map f.op
        (Ideal.Quotient.mk (J.ideal U) s) =
        (idealQuotientPresheaf R J.ideal J.ideal_le_comap).map f.op 0 := hf
    rw [map_zero] at hf'
    exact Ideal.Quotient.eq_zero_iff_mem.mp hf'
  · intro hs
    rw [quotientπ_app_apply, Ideal.Quotient.eq_zero_iff_mem.mpr hs]
    exact map_zero _

/-- The projection `R ⟶ R / J` is locally surjective. -/
private lemma exists_quotientπ_app_eq (U : Opens T) (t : J.quotient.presheaf.obj (op U)) (x : T)
    (hx : x ∈ U) :
    ∃ (V : Opens T) (hVU : V ≤ U) (s : R.presheaf.obj (op V)), x ∈ V ∧
      J.quotientπ.hom.app (op V) s = J.quotient.presheaf.map (homOfLE hVU).op t := by
  obtain ⟨V, hVU, ⟨q, hq⟩, hxV⟩ := (TopCat.Presheaf.isLocallySurjective_iff
    (toSheafify (Opens.grothendieckTopology T)
      (idealQuotientPresheaf R J.ideal J.ideal_le_comap))).mp
    (inferInstanceAs (Presheaf.IsLocallySurjective (Opens.grothendieckTopology T) _)) U t x hx
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact ⟨V, hVU, s, hxV, by rw [quotientπ_app_apply]; exact hq⟩

/-- The projection `R ⟶ R / J` commutes with restriction. -/
private lemma quotientπ_app_res {U V : Opens T} (h : V ≤ U) (s : R.presheaf.obj (op U)) :
    J.quotientπ.hom.app (op V) (R.presheaf.map (homOfLE h).op s) =
      J.quotient.presheaf.map (homOfLE h).op (J.quotientπ.hom.app (op U) s) :=
  NatTrans.naturality_apply J.quotientπ.hom _ s

/-- If `1 ∈ J(V)` then `R / J` vanishes near every point of `V`. -/
private lemma notMem_sheafSupport_of_one_mem {V : Opens T} {x : T} (hx : x ∈ V)
    (h1 : (1 : R.presheaf.obj (op V)) ∈ J.ideal V) :
    x ∉ sheafSupport J.quotientAb := by
  intro hsupp
  have hsub : ∀ (W : Opens T) (_ : W ≤ V), Subsingleton (J.quotient.presheaf.obj (op W)) := by
    intro W hWV
    have h0 := (J.quotientπ_app_eq_zero_iff W (R.presheaf.map (homOfLE hWV).op 1)).mpr
      (J.ideal_le_comap hWV h1)
    rw [map_one, map_one] at h0
    exact subsingleton_of_zero_eq_one h0.symm
  obtain ⟨a, b, hab⟩ := hsupp
  apply hab
  obtain ⟨W₁, h₁, hx₁, s₁, rfl⟩ := J.quotientAb.presheaf.exists_le_germ_eq a hx
  obtain ⟨W₂, h₂, hx₂, s₂, rfl⟩ := J.quotientAb.presheaf.exists_le_germ_eq b hx
  have e₁ : s₁ = 0 := @Subsingleton.elim _ (hsub W₁ h₁) _ _
  have e₂ : s₂ = 0 := @Subsingleton.elim _ (hsub W₂ h₂) _ _
  rw [e₁, e₂, map_zero, map_zero]

end IdealSubsheaf

namespace IsIdealOfDefinition

variable {X : NoetherianFormalScheme.{u}}

private lemma not_isUnit_germ_of_mem_ideal (J : IdealSubsheaf X.toLocallyRingedSpace.sheaf)
    {x : X.toLocallyRingedSpace} (hsupp : x ∈ sheafSupport J.quotientAb)
    {V : Opens X.toLocallyRingedSpace} (hx : x ∈ V)
    {g : X.toLocallyRingedSpace.sheaf.presheaf.obj (op V)}
    (hg : g ∈ J.ideal V) :
    ¬ IsUnit (X.toLocallyRingedSpace.sheaf.presheaf.germ V x hx g) := by
  intro hu
  obtain ⟨W, i, hxW, hW⟩ := X.toRingedSpace.isUnit_res_of_isUnit_germ V g x hx hu
  obtain ⟨v, hv⟩ := hW.exists_right_inv
  have hv' : X.toLocallyRingedSpace.sheaf.presheaf.map i.op g *
      (show X.toLocallyRingedSpace.sheaf.presheaf.obj (op W) from v) = 1 := hv
  have key := Ideal.mul_mem_right (show X.toLocallyRingedSpace.sheaf.presheaf.obj (op W) from v)
    _ (J.ideal_le_comap (leOfHom i) hg)
  rw [show (homOfLE (leOfHom i)).op = i.op from rfl, hv'] at key
  exact J.notMem_sheafSupport_of_one_mem hxW key hsupp

variable {J₁ J₂ : IdealSubsheaf X.toLocallyRingedSpace.sheaf}

private lemma not_isUnit_germ_quotientπ (h₁ : IsIdealOfDefinition X J₁)
    (h₂ : sheafSupport J₂.quotientAb = Set.univ) {V : Opens X.toLocallyRingedSpace}
    {g : X.toLocallyRingedSpace.sheaf.presheaf.obj (op V)} (hg : g ∈ J₂.ideal V)
    (x : X.toLocallyRingedSpace)
    (hx : x ∈ V) :
    ¬ IsUnit (h₁.quotientScheme.presheaf.germ V x hx (J₁.quotientπ.hom.app (op V) g)) := by
  intro hu
  obtain ⟨W, hWV, hxW, hW⟩ : ∃ (W : Opens X.toLocallyRingedSpace) (hWV : W ≤ V), x ∈ W ∧
      IsUnit (J₁.quotient.presheaf.map (homOfLE hWV).op (J₁.quotientπ.hom.app (op V) g)) := by
    obtain ⟨W, i, hxW, hW⟩ :=
      h₁.quotientScheme.toRingedSpace.isUnit_res_of_isUnit_germ V _ x hx hu
    exact ⟨W, leOfHom i, hxW, hW⟩
  obtain ⟨t, ht⟩ : ∃ t : J₁.quotient.presheaf.obj (op W),
      J₁.quotient.presheaf.map (homOfLE hWV).op (J₁.quotientπ.hom.app (op V) g) * t = 1 :=
    hW.exists_right_inv
  obtain ⟨W', hW'W, t', hxW', ht'⟩ := J₁.exists_quotientπ_app_eq W t x hxW
  set g' := X.toLocallyRingedSpace.sheaf.presheaf.map (homOfLE hW'W).op
    (X.toLocallyRingedSpace.sheaf.presheaf.map (homOfLE hWV).op g) with hg'
  have hj : g' * t' - 1 ∈ J₁.ideal W' := by
    rw [← J₁.quotientπ_app_eq_zero_iff, map_sub, map_mul, map_one, ht', hg',
      J₁.quotientπ_app_res, J₁.quotientπ_app_res, sub_eq_zero, ← map_mul, ht, map_one]
  have hj' := not_isUnit_germ_of_mem_ideal J₁ (h₁.support_eq_univ ▸ Set.mem_univ x) hxW' hj
  have hgt : g' * t' ∈ J₂.ideal W' :=
    Ideal.mul_mem_right _ _ (J₂.ideal_le_comap hW'W (J₂.ideal_le_comap hWV hg))
  refine not_isUnit_germ_of_mem_ideal J₂ (h₂ ▸ Set.mem_univ x) hxW' hgt ?_
  have : IsLocalRing (X.toLocallyRingedSpace.sheaf.presheaf.stalk x) :=
    inferInstanceAs (IsLocalRing (X.presheaf.stalk x))
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self
      (X.toLocallyRingedSpace.sheaf.presheaf.germ W' x hxW' (g' * t')) with
    h | h
  · exact h
  · refine absurd ?_ hj'
    rw [map_sub, map_one, ← neg_sub]
    exact h.neg

/-- **Ideals of definition are cofinal**, one direction (supplements Hartshorne II,
Proposition 9.5(a), pp. 196–197). If `J₁` is an ideal of definition on the Noetherian formal
scheme `X` and `J₂` is an ideal subsheaf with `Supp (𝒪_X / J₂) = X`, then `J₂ ^ a ⊆ J₁` for some
positive integer `a`. -/
theorem exists_pow_le (h₁ : IsIdealOfDefinition X J₁)
    (h₂ : sheafSupport J₂.quotientAb = Set.univ) : ∃ a : ℕ, 0 < a ∧ J₂ ^ a ≤ J₁ := by
  set Y := h₁.quotientScheme
  have hN : ∀ U : Y.affineOpens, ∃ n : ℕ, nilradical Γ(Y, U) ^ n = ⊥ := fun U => by
    have := IsLocallyNoetherian.component_noetherian U
    obtain ⟨n, hn⟩ := IsNoetherianRing.isNilpotent_nilradical Γ(Y, U)
    exact ⟨n, hn⟩
  choose N hN using hN
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun U : Y.affineOpens => ((U : Y.Opens) : Set Y)) (fun U => U.1.isOpen) (by
      intro x _
      obtain ⟨U, hU, hxU, -⟩ := Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
        (show x ∈ (⊤ : Y.Opens) from trivial)
      exact Set.mem_iUnion.mpr ⟨⟨U, hU⟩, hxU⟩)
  have hstalk : ∀ x : Y, nilradical (Y.presheaf.stalk x) ^ (t.sup N + 1) = ⊥ := by
    intro x
    obtain ⟨U, hUt, hxU⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    let := Y.presheaf.algebra_section_stalk ⟨x, hxU⟩
    have := U.2.isLocalization_stalk ⟨x, hxU⟩
    have hmap : (nilradical Γ(Y, U)).map (algebraMap Γ(Y, U) (Y.presheaf.stalk x)) =
        nilradical (Y.presheaf.stalk x) := by
      have := IsLocalization.map_radical (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
        (Y.presheaf.stalk x) (⊥ : Ideal Γ(Y, U))
      simpa [nilradical, Ideal.map_bot] using this
    rw [eq_bot_iff, ← hmap, ← Ideal.map_pow]
    calc _ ≤ Ideal.map (algebraMap Γ(Y, U) (Y.presheaf.stalk x)) (nilradical Γ(Y, U) ^ N U) :=
          Ideal.map_mono (Ideal.pow_le_pow_right
            ((Finset.le_sup hUt).trans (Nat.le_succ _)))
      _ = ⊥ := by rw [hN, Ideal.map_bot]
  have hnil : ∀ (W : Opens X.toLocallyRingedSpace) (g : X.presheaf.obj (op W))
      (_ : g ∈ J₂.ideal W) (x : X.toLocallyRingedSpace) (hx : x ∈ W),
      IsNilpotent (Y.presheaf.germ W x hx (J₁.quotientπ.hom.app (op W) g)) := by
    intro W g hg x hx
    obtain ⟨W', hW'aff, hxW', hW'W⟩ := Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
      (show x ∈ (W : Y.Opens) from hx)
    have hres : ∀ (y : Y) (hy : y ∈ W'), Y.presheaf.germ W' y hy
        (Y.presheaf.map (homOfLE hW'W).op (J₁.quotientπ.hom.app (op W) g)) =
        Y.presheaf.germ W y (hW'W hy) (J₁.quotientπ.hom.app (op W) g) := fun y hy =>
      Y.presheaf.germ_res_apply (homOfLE hW'W) y hy _
    have hf : Y.basicOpen
        (Y.presheaf.map (homOfLE hW'W).op (J₁.quotientπ.hom.app (op W) g)) = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      have hyW' : y ∈ W' := Y.basicOpen_le _ hy
      rw [Scheme.mem_basicOpen _ _ _ hyW', hres y hyW'] at hy
      exact absurd hy (not_isUnit_germ_quotientπ h₁ h₂ hg y (hW'W hyW'))
    have hfnil :
        IsNilpotent (Y.presheaf.map (homOfLE hW'W).op (J₁.quotientπ.hom.app (op W) g)) := by
      have e := IsAffineOpen.fromSpec_preimage_basicOpen hW'aff
        (Y.presheaf.map (homOfLE hW'W).op (J₁.quotientπ.hom.app (op W) g))
      rw [hf] at e
      refine (PrimeSpectrum.basicOpen_eq_bot_iff _).mp ?_
      rw [← e]
      rfl
    rw [← hres x hxW']
    exact hfnil.map _
  refine ⟨t.sup N + 1, Nat.succ_pos _, ?_⟩
  rw [IdealSubsheaf.le_iff]
  intro U s hs
  rw [IdealSubsheaf.ideal_pow] at hs
  rw [← J₁.quotientπ_app_eq_zero_iff]
  refine TopCat.Presheaf.section_ext J₁.quotient U _ 0 fun x hx => ?_
  obtain ⟨W, hWU, hxW, hsW⟩ := hs x hx
  refine Eq.trans ?_ (map_zero _).symm
  rw [← J₁.quotient.presheaf.germ_res_apply (homOfLE hWU) x hxW, ← J₁.quotientπ_app_res]
  let φ : X.toLocallyRingedSpace.sheaf.presheaf.obj (op W) →+* Y.presheaf.stalk x :=
    (Y.presheaf.germ W x hxW).hom.comp (J₁.quotientπ.hom.app (op W)).hom
  have hle : (J₂.ideal W).map φ ≤ nilradical _ :=
    Ideal.map_le_iff_le_comap.mpr fun g hg => hnil W g hg x hxW
  have hmem : φ (X.toLocallyRingedSpace.sheaf.presheaf.map (homOfLE hWU).op s) ∈
      nilradical (Y.presheaf.stalk x) ^ (t.sup N + 1) :=
    Ideal.pow_right_mono hle _ (Ideal.map_pow φ (J₂.ideal W) _ ▸ Ideal.mem_map_of_mem φ hsW)
  rw [hstalk x] at hmem
  exact Ideal.mem_bot.mp hmem

/-- **Ideals of definition are cofinal** (Hartshorne II, Proposition 9.5(a), pp. 196–197). If
`J₁` and `J₂` are ideals of definition on a Noetherian formal scheme `X`, then there are positive
integers `a`, `b` such that `J₁ ⊇ J₂ ^ a` and `J₂ ⊇ J₁ ^ b`. -/
theorem exists_pow_le_and_pow_le (h₁ : IsIdealOfDefinition X J₁)
    (h₂ : IsIdealOfDefinition X J₂) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ J₂ ^ a ≤ J₁ ∧ J₁ ^ b ≤ J₂ := by
  obtain ⟨a, ha, hab⟩ := exists_pow_le h₁ h₂.support_eq_univ
  obtain ⟨b, hb, hba⟩ := exists_pow_le h₂ h₁.support_eq_univ
  exact ⟨a, b, ha, hb, hab, hba⟩

end IsIdealOfDefinition

end Hartshorne

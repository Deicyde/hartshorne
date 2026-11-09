/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ProjectiveSpaceClassGroup
import Hartshorne.Scheme.ProjTwistingSheaf
import Hartshorne.Scheme.LocallyFactorialClassPicard
import Hartshorne.Scheme.TotalQuotientIntegral
import Hartshorne.Scheme.RegularLocalFactorial
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# The Picard group of projective space

Hartshorne, *Algebraic Geometry*, II.6, Corollary 6.17 (p. 145): for a field `k` and `n ≥ 1`,
every invertible sheaf on `X = ℙⁿ_k` is isomorphic to `𝒪(l)` for a unique integer `l`
(`Hartshorne.exists_unique_iso_projTwistingSheaf`); equivalently, `Pic X ≅ ℤ` with `𝒪(1) ↦ 1`
(`Hartshorne.projectiveSpacePicardEquiv`,
`Hartshorne.projectiveSpacePicardEquiv_projTwistingSheaf`).

## Proof

`X` is regular, hence locally factorial, so `Cl X ≅ Pic X` (Corollary 6.16), and `Cl X ≅ ℤ` by
the degree (Proposition 6.4). It remains to see that `𝒪(l)` corresponds to `l · H`, `H = V(x₀)`.
Sending a section `s` of `𝒪(l)` to the rational function `s / x₀^l` (evaluated at the generic
point) is an injective morphism of `𝒪_X`-modules `𝒪(l) ⟶ K_X`
(`Hartshorne.ProjectiveSpacePicard.twistToK`); its image is an invertible submodule of `K_X`,
hence `O_X(D_l)` for a Cartier divisor `D_l` (Proposition 6.13). Near a codimension-one point `y`,
with `ℓ` a linear form not vanishing at `y`, a section `m / f` goes to
`(m ℓ^{l⁻} / f ℓ^{l⁺}) · (x₀/ℓ)^{l⁻} (ℓ/x₀)^{l⁺}`, of order at least `-l · [y ∈ H]`, with
equality for `ℓ^l`. Comparing with a local equation `g` of `D_l` (`g⁻¹` is a section of the image,
and `ℓ^l g` is regular) gives `ord_y g = l · [y ∈ H]`, so the Weil divisor of `D_l` is `l · H`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial HomogeneousLocalization
  Opposite TopologicalSpace

namespace Hartshorne

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] {n : ℕ}

local notation "𝒜" => homogeneousSubmodule (Fin (n + 1)) k

local notation "S" => MvPolynomial (Fin (n + 1)) k

namespace ProjectiveSpacePicard

variable (k n) in
/-- The complement of the generic point of `ℙⁿ_k`, i.e. the nonzero polynomials. -/
abbrev genericCompl : Submonoid S :=
  (genericPoint (Proj 𝒜)).asHomogeneousIdeal.toIdeal.primeCompl

theorem mem_genericCompl {h : S} (h0 : h ≠ 0) : h ∈ genericCompl k n :=
  genericPoint_mem_basicOpen h0

/-- The fraction `x₀^{l⁻} / x₀^{l⁺}` of the fraction field, which is `x₀^{-l}`. -/
def twistFactor (l : ℤ) : Localization (genericCompl k n) :=
  Localization.mk ((X 0 : S) ^ (-l).toNat) ⟨(X 0 : S) ^ l.toNat,
    pow_mem (mem_genericCompl (X_ne_zero 0)) _⟩

/-- The identification of the localized module of `S` with the localization of `S`,
`m / s ↦ m / s`. -/
def locEquiv : LocalizedModule (genericCompl k n) S →+ Localization (genericCompl k n) :=
  AddMonoidHom.mk' (fun y => y.liftOn (fun p => Localization.mk p.1 p.2) (by
    rintro ⟨m, s⟩ ⟨m', s'⟩ ⟨u, hu⟩
    refine Localization.mk_eq_mk_iff.2 (Localization.r_iff_exists.2 ⟨u, ?_⟩)
    have hu' : (u : S) * ((s' : S) * m) = u * (s * m') := by
      simpa only [Submonoid.smul_def, smul_eq_mul] using hu
    exact hu')) (by
    intro y z
    induction y using LocalizedModule.induction_on with
    | h m s =>
      induction z using LocalizedModule.induction_on with
      | h m' s' =>
        rw [LocalizedModule.mk_add_mk, LocalizedModule.liftOn_mk, LocalizedModule.liftOn_mk,
          LocalizedModule.liftOn_mk, Localization.add_mk]
        simp only [smul_eq_mul, Submonoid.smul_def]
        congr 1
        ring)

theorem locEquiv_mk (m : S) (s : genericCompl k n) :
    locEquiv (LocalizedModule.mk m s) = Localization.mk m s :=
  rfl

/-- The value `y / x₀^l` in the fraction field of an element `y` of `S(l)_(0)`. -/
def twistVal (l : ℤ) :
    HomogeneousLocalizedModule 𝒜 (gradedTwist 𝒜 l) (genericCompl k n) →+
      Localization (genericCompl k n) where
  toFun y := locEquiv y.val * twistFactor l
  map_zero' := by simp
  map_add' y z := by simp [add_mul]

theorem twistVal_mk (l : ℤ) (j : ℕ) (m : S) (hm : m ∈ gradedTwist 𝒜 l j) (s : S) (hs : s ∈ 𝒜 j)
    (hsx : s ∈ genericCompl k n) :
    twistVal l (HomogeneousLocalizedModule.mk j m hm s hs hsx) =
      Localization.mk (m * (X 0 : S) ^ (-l).toNat) ⟨s * (X 0 : S) ^ l.toNat,
        mul_mem hsx (pow_mem (mem_genericCompl (X_ne_zero 0)) _)⟩ := by
  simp only [twistVal, AddMonoidHom.coe_mk, ZeroHom.coe_mk, HomogeneousLocalizedModule.val_mk,
    locEquiv_mk, twistFactor, Localization.mk_mul]
  rfl

theorem twistVal_smul (l : ℤ) (c : AtPrime 𝒜 (genericPoint (Proj 𝒜)).asHomogeneousIdeal.toIdeal)
    (y : HomogeneousLocalizedModule 𝒜 (gradedTwist 𝒜 l) (genericCompl k n)) :
    twistVal l (c • y) = c.val * twistVal l y := by
  obtain ⟨⟨i, ⟨a, ha⟩, ⟨b, hb⟩, hbx⟩, rfl⟩ := HomogeneousLocalization.mk_surjective c
  obtain ⟨j, m, hm, s, hs, hsx, rfl⟩ := HomogeneousLocalizedModule.mk_surjective y
  have : (HomogeneousLocalization.mk ⟨i, ⟨a, ha⟩, ⟨b, hb⟩, hbx⟩ •
      HomogeneousLocalizedModule.mk j m hm s hs hsx :
        HomogeneousLocalizedModule 𝒜 (gradedTwist 𝒜 l) (genericCompl k n)).val =
      LocalizedModule.mk (a * m) ⟨b * s, mul_mem hbx hsx⟩ := by
    rw [HomogeneousLocalizedModule.val_smul, HomogeneousLocalization.val_mk,
      HomogeneousLocalizedModule.val_mk, LocalizedModule.mk_smul_mk]
    rfl
  simp only [twistVal, AddMonoidHom.coe_mk, ZeroHom.coe_mk, this,
    HomogeneousLocalizedModule.val_mk, locEquiv_mk, HomogeneousLocalization.val_mk, twistFactor,
    Localization.mk_mul, mul_assoc]
  congr 1
  rw [← mul_assoc]
  rfl

theorem twistVal_mem_range (l : ℤ)
    (y : HomogeneousLocalizedModule 𝒜 (gradedTwist 𝒜 l) (genericCompl k n)) :
    ∃ κ : (Proj 𝒜).functionField, functionFieldToLocalization κ = twistVal l y := by
  obtain ⟨j, m, hm, s, hs, hsx, rfl⟩ := HomogeneousLocalizedModule.mk_surjective y
  rw [twistVal_mk]
  by_cases hneg : l + (j : ℤ) < 0
  · refine ⟨0, ?_⟩
    rw [eq_zero_of_mem_gradedTwist hm hneg, zero_mul, Localization.mk_zero, map_zero]
  have hm' : m.IsHomogeneous ((l + j).toNat + (-l).toNat - (-l).toNat) := by
    rw [Nat.add_sub_cancel]
    exact (mem_homogeneousSubmodule _ m).mp (mem_of_mem_gradedTwist hm)
  have hg : (m * (X 0 : S) ^ (-l).toNat).IsHomogeneous (j + l.toNat) := by
    have := (mem_homogeneousSubmodule _ m).mp (mem_of_mem_gradedTwist hm) |>.mul
      (isHomogeneous_pow_of_isHomogeneous_one (isHomogeneous_X k (0 : Fin (n + 1))) (-l).toNat)
    convert this using 1
    omega
  have hh : (s * (X 0 : S) ^ l.toNat).IsHomogeneous (j + l.toNat) :=
    ((mem_homogeneousSubmodule _ s).mp hs).mul
      (isHomogeneous_pow_of_isHomogeneous_one (isHomogeneous_X k (0 : Fin (n + 1))) l.toNat)
  have h0 : s * (X 0 : S) ^ l.toNat ≠ 0 := by
    have hs0 : s ≠ 0 := fun h => hsx (h ▸ zero_mem _)
    exact mul_ne_zero hs0 (pow_ne_zero _ (X_ne_zero 0))
  exact ⟨homogeneousFraction hg hh h0, functionFieldToLocalization_homogeneousFraction hg hh h0⟩

/-- The rational function `y / x₀^l` attached to an element `y` of `S(l)_(0)`. -/
def twistToFunctionField (l : ℤ) :
    HomogeneousLocalizedModule 𝒜 (gradedTwist 𝒜 l) (genericCompl k n) →+
      (Proj 𝒜).functionField :=
  AddMonoidHom.mk' (fun y => Classical.choose (twistVal_mem_range l y)) fun y z => by
    apply functionFieldToLocalization_injective
    have h1 := Classical.choose_spec (twistVal_mem_range l (y + z))
    have h2 := Classical.choose_spec (twistVal_mem_range l y)
    have h3 := Classical.choose_spec (twistVal_mem_range l z)
    rw [h1, map_add functionFieldToLocalization, h2, h3]
    exact map_add _ _ _

theorem functionFieldToLocalization_twistToFunctionField (l : ℤ)
    (y : HomogeneousLocalizedModule 𝒜 (gradedTwist 𝒜 l) (genericCompl k n)) :
    functionFieldToLocalization (twistToFunctionField l y) = twistVal l y :=
  Classical.choose_spec (twistVal_mem_range l y)

theorem functionFieldToLocalization_stalkIso_inv
    (c : AtPrime 𝒜 (genericPoint (Proj 𝒜)).asHomogeneousIdeal.toIdeal) :
    functionFieldToLocalization ((Proj.stalkIso 𝒜 (genericPoint (Proj 𝒜))).inv c) = c.val := by
  simp only [functionFieldToLocalization, RingHom.comp_apply]
  rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id, CategoryTheory.id_apply]
  rfl

theorem twistToFunctionField_smul (l : ℤ)
    (c : AtPrime 𝒜 (genericPoint (Proj 𝒜)).asHomogeneousIdeal.toIdeal)
    (y : HomogeneousLocalizedModule 𝒜 (gradedTwist 𝒜 l) (genericCompl k n)) :
    twistToFunctionField l (c • y) =
      (Proj.stalkIso 𝒜 (genericPoint (Proj 𝒜))).inv c * twistToFunctionField l y := by
  apply functionFieldToLocalization_injective
  rw [map_mul, functionFieldToLocalization_twistToFunctionField,
    functionFieldToLocalization_twistToFunctionField, functionFieldToLocalization_stalkIso_inv,
    twistVal_smul]

local notation "η" => genericPoint (Proj 𝒜)

theorem subsingleton_totalQuotient_of_notMem {U : (Proj 𝒜).Opens} (h : η ∉ U) :
    Subsingleton ((Proj 𝒜).totalQuotientSheaf.obj.obj (op U)) :=
  CommRingCat.subsingleton_of_isTerminal
    ((Proj 𝒜).totalQuotientSheaf.isTerminalOfEqEmpty (Scheme.opens_eq_bot_of_genericPoint_notMem h))

open Classical in
/-- The map on sections over `U` of `𝒪(l) ⟶ K_X`: a section `s` goes to the rational function
`s(η) / x₀^l`, where `η` is the generic point (and to `0` if `U` is empty). -/
def twistToKSections (l : ℤ) (U : (Proj 𝒜).Opens) :
    (ProjGradedModuleSheaf.sheafInType 𝒜 (gradedTwist 𝒜 l)).1.obj (op U) →+
      (Proj 𝒜).totalQuotientSheaf.obj.obj (op U) :=
  if h : η ∈ U then
    ((Scheme.totalQuotientSheafEquivFunctionField U h).symm.toAddEquiv.toAddMonoidHom.comp
      ((twistToFunctionField l).comp
        { toFun := fun s => s.1 ⟨η, h⟩
          map_zero' := rfl
          map_add' := fun _ _ => rfl }))
  else 0

theorem twistToKSections_apply (l : ℤ) {U : (Proj 𝒜).Opens} (h : η ∈ U)
    (s : (ProjGradedModuleSheaf.sheafInType 𝒜 (gradedTwist 𝒜 l)).1.obj (op U)) :
    Scheme.totalQuotientSheafEquivFunctionField U h (twistToKSections l U s) =
      twistToFunctionField l (s.1 ⟨η, h⟩) := by
  simp [twistToKSections, dif_pos h]

/-- The morphism of abelian presheaves `𝒪(l) ⟶ K_X`, `s ↦ s / x₀^l`. -/
def twistToKPresheafHom (l : ℤ) :
    (projTwistingSheaf 𝒜 l).presheaf ⟶ (Proj 𝒜).totalQuotientModule.presheaf where
  app U := AddCommGrpCat.ofHom (twistToKSections l U.unop)
  naturality U V i := by
    ext s
    by_cases h : η ∈ V.unop
    · apply (Scheme.totalQuotientSheafEquivFunctionField V.unop h).injective
      change Scheme.totalQuotientSheafEquivFunctionField V.unop h (twistToKSections l V.unop _) =
        Scheme.totalQuotientSheafEquivFunctionField V.unop h
          ((Proj 𝒜).totalQuotientSheaf.obj.map (homOfLE (leOfHom i.unop)).op
            (twistToKSections l U.unop s))
      rw [Scheme.totalQuotientSheafEquivFunctionField_map]
      erw [twistToKSections_apply, twistToKSections_apply]
      rfl
    · have := subsingleton_totalQuotient_of_notMem h
      exact Subsingleton.elim (α := (Proj 𝒜).totalQuotientSheaf.obj.obj (op V.unop)) _ _

theorem stalkIso_inv_apply_eq_germ {U : (Proj 𝒜).Opens} (h : η ∈ U) (r : Γ(Proj 𝒜, U)) :
    (Proj.stalkIso 𝒜 η).inv (r.1 ⟨η, h⟩) = (Proj 𝒜).presheaf.germ U η h r := by
  change (Proj.stalkIso' 𝒜 η).symm _ = _
  rw [← Proj.stalkIso'_germ 𝒜 U η h r, RingEquiv.symm_apply_apply]
  rfl

/-- **The embedding `𝒪(l) ⟶ K_X`** of `𝒪_X`-modules on `X = ℙⁿ_k`, `s ↦ s / x₀^l`. -/
def twistToK (l : ℤ) : projTwistingSheaf 𝒜 l ⟶ (Proj 𝒜).totalQuotientModule :=
  ⟨PresheafOfModules.homMk (twistToKPresheafHom l) fun U r m => by
    by_cases h : η ∈ U.unop
    · apply (Scheme.totalQuotientSheafEquivFunctionField U.unop h).injective
      change Scheme.totalQuotientSheafEquivFunctionField U.unop h
          (twistToKSections l U.unop (r • m)) =
        Scheme.totalQuotientSheafEquivFunctionField U.unop h
          ((Proj 𝒜).toK U.unop r * twistToKSections l U.unop m)
      rw [map_mul]
      erw [twistToKSections_apply, twistToKSections_apply]
      erw [Scheme.totalQuotientSheafEquivFunctionField_toTotalQuotientSheaf]
      have key := twistToFunctionField_smul l (r.1 ⟨η, h⟩)
        ((m : (ProjGradedModuleSheaf.sheafInType 𝒜 (gradedTwist 𝒜 l)).1.obj U).1 ⟨η, h⟩)
      rw [stalkIso_inv_apply_eq_germ h r] at key
      exact key
    · have := subsingleton_totalQuotient_of_notMem h
      exact Subsingleton.elim (α := (Proj 𝒜).totalQuotientSheaf.obj.obj (op U.unop)) _ _⟩

theorem twistToK_app_apply (l : ℤ) {U : (Proj 𝒜).Opens} (h : η ∈ U)
    (s : (projTwistingSheaf 𝒜 l).val.obj (op U)) :
    Scheme.totalQuotientSheafEquivFunctionField U h ((twistToK l).val.app (op U) s) =
      twistToFunctionField l
        ((s : (ProjGradedModuleSheaf.sheafInType 𝒜 (gradedTwist 𝒜 l)).1.obj (op U)).1 ⟨η, h⟩) :=
  twistToKSections_apply l h s

theorem eq_zero_of_twistVal_mk_eq_zero (l : ℤ) {j : ℕ} {m : S} (hm : m ∈ gradedTwist 𝒜 l j)
    {s : S} (hs : s ∈ 𝒜 j) (hsx : s ∈ genericCompl k n)
    (h : twistVal l (HomogeneousLocalizedModule.mk j m hm s hs hsx) = 0) : m = 0 := by
  rw [twistVal_mk, Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff] at h
  obtain ⟨⟨c, hc⟩, hcm⟩ := h
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hc (zero_mem _)
  have := (mul_eq_zero.mp hcm).resolve_left hc0
  exact (mul_eq_zero.mp this).resolve_right (pow_ne_zero _ (X_ne_zero 0))

theorem twistVal_injective (l : ℤ) :
    Function.Injective (twistVal (k := k) (n := n) l) := by
  refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
  obtain ⟨j, m, hm, s, hs, hsx, rfl⟩ := HomogeneousLocalizedModule.mk_surjective y
  have hm0 := eq_zero_of_twistVal_mk_eq_zero l hm hs hsx hy
  subst hm0
  ext
  rw [HomogeneousLocalizedModule.val_mk, HomogeneousLocalizedModule.val_zero,
    LocalizedModule.zero_mk]

theorem twistToFunctionField_injective (l : ℤ) :
    Function.Injective (twistToFunctionField (k := k) (n := n) l) := by
  intro y z h
  apply twistVal_injective l
  rw [← functionFieldToLocalization_twistToFunctionField,
    ← functionFieldToLocalization_twistToFunctionField, h]

/-- A section of `𝒪(l)` vanishing at the generic point vanishes. -/
theorem section_eq_zero_of_apply_genericPoint (l : ℤ) {U : (Proj 𝒜).Opens} (h : η ∈ U)
    (s : (ProjGradedModuleSheaf.sheafInType 𝒜 (gradedTwist 𝒜 l)).1.obj (op U))
    (hs : s.1 ⟨η, h⟩ = 0) : s = 0 := by
  apply Subtype.ext
  funext x
  obtain ⟨W, hxW, iWU, j, m, hm, f, hf, f_nin, w⟩ := s.2 x
  have hηW : η ∈ W := Scheme.genericPoint_mem_opens_of_mem (X := Proj 𝒜) hxW
  have hη := w ⟨η, hηW⟩
  have hη' : s.1 ⟨η, h⟩ = HomogeneousLocalizedModule.mk j m hm f hf (f_nin ⟨η, hηW⟩) := hη
  rw [hs] at hη'
  have hm0 : m = 0 := by
    apply eq_zero_of_twistVal_mk_eq_zero l hm hf (f_nin ⟨η, hηW⟩)
    rw [← hη', map_zero]
  have hx := w ⟨x.1, hxW⟩
  change s.1 x = _ at hx
  rw [hx]
  subst hm0
  ext
  exact LocalizedModule.zero_mk _

theorem twistToK_app_injective (l : ℤ) (U : (Proj 𝒜).Opensᵒᵖ) :
    Function.Injective ((twistToK l).val.app U) := by
  refine (injective_iff_map_eq_zero _).2 fun s hs => ?_
  by_cases h : η ∈ U.unop
  · have h1 := twistToK_app_apply l h s
    have h1' : twistToFunctionField l
        ((s : (ProjGradedModuleSheaf.sheafInType 𝒜 (gradedTwist 𝒜 l)).1.obj (op U.unop)).1
          ⟨η, h⟩) = twistToFunctionField l 0 := by
      rw [← h1, map_zero]
      erw [hs]
      exact map_zero _
    exact section_eq_zero_of_apply_genericPoint l h s (twistToFunctionField_injective l h1')
  · apply Subtype.ext
    funext x
    exact absurd (Scheme.genericPoint_mem_opens_of_mem (X := Proj 𝒜) x.2) h

variable (k n) in
/-- `k[x₀, …, xₙ]` is generated by its degree-one part over its degree-zero part. -/
theorem adjoin_one_eq_top : Algebra.adjoin (𝒜 0) (𝒜 1 : Set S) = ⊤ := by
  refine Algebra.eq_top_iff.2 fun p => ?_
  induction p using MvPolynomial.induction_on with
  | C a =>
    have ha : (C a : S) ∈ 𝒜 0 := (mem_homogeneousSubmodule 0 _).2 (isHomogeneous_C _ a)
    exact (Algebra.adjoin (𝒜 0) (𝒜 1 : Set S)).algebraMap_mem ⟨C a, ha⟩
  | add p q hp hq => exact add_mem hp hq
  | mul_X p i hp =>
    exact mul_mem hp
      (Algebra.subset_adjoin ((mem_homogeneousSubmodule 1 _).2 (isHomogeneous_X k i)))

/-- An `𝒪_X`-module isomorphic to an invertible one is invertible. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible.of_iso {X : Scheme.{u}}
    {F G : X.Modules} (e : F ≅ G) (hF : F.IsInvertible) : G.IsInvertible := fun x => by
  obtain ⟨U, hx, ⟨e'⟩⟩ := hF x
  exact ⟨U, hx, ⟨((Scheme.Modules.restrictFunctor U.ι).mapIso e).symm ≪≫ e'⟩⟩

/-- The image of `𝒪(l) ⟶ K_X`, as a family of submodules of the sections of `K_X`. -/
def imageSubmodule (l : ℤ) : (Proj 𝒜).totalQuotientModule.val.Submodule where
  obj U := LinearMap.range ((twistToK l).val.app U).hom
  map i := by
    rintro _ ⟨s, rfl⟩
    exact ⟨(projTwistingSheaf 𝒜 l).val.map i s, PresheafOfModules.naturality_apply _ _ _⟩

/-- `𝒪(l) ⟶ K_X` corestricted to its image. -/
def toImage (l : ℤ) : (projTwistingSheaf 𝒜 l).val ⟶ (imageSubmodule l).toPresheafOfModules :=
  PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom
        { toFun s := ⟨(twistToK l).val.app U s, s, rfl⟩
          map_zero' := Subtype.ext ((twistToK l).val.app U).hom.map_zero
          map_add' a b := Subtype.ext (((twistToK l).val.app U).hom.map_add a b) }
      naturality U V i := by
        ext s
        exact Subtype.ext (PresheafOfModules.naturality_apply (twistToK l).val i s) }
    fun U r m => Subtype.ext (((twistToK l).val.app U).hom.map_smul r m)

theorem toImage_app_val (l : ℤ) (U : (Proj 𝒜).Opensᵒᵖ) (s : (projTwistingSheaf 𝒜 l).val.obj U) :
    ((toImage l).app U s).1 = (twistToK l).val.app U s :=
  rfl

instance (l : ℤ) : IsIso (toImage (k := k) (n := n) l) := by
  have : Mono (toImage (k := k) (n := n) l) := PresheafOfModules.mono_of_injective fun U a b h =>
    twistToK_app_injective l U (congrArg Subtype.val h)
  have : Epi (toImage (k := k) (n := n) l) := PresheafOfModules.epi_of_surjective fun U t => by
    obtain ⟨_, s, rfl⟩ := t
    exact ⟨s, rfl⟩
  exact isIso_of_mono_of_epi _

theorem isSheaf_imageSubmodule (l : ℤ) :
    Presheaf.IsSheaf (Opens.grothendieckTopology (Proj 𝒜))
      (imageSubmodule (k := k) (n := n) l).toPresheafOfModules.presheaf :=
  (Presheaf.isSheaf_of_iso_iff
    ((PresheafOfModules.toPresheaf _).mapIso (asIso (toImage (k := k) (n := n) l)))).1
      (projTwistingSheaf 𝒜 l).isSheaf

/-- The image of `𝒪(l) ⟶ K_X` as an `𝒪_X`-module, isomorphic to `𝒪(l)`. -/
def imageIso (l : ℤ) :
    projTwistingSheaf 𝒜 l ≅ ⟨(imageSubmodule l).toPresheafOfModules, isSheaf_imageSubmodule l⟩ :=
  let e : (projTwistingSheaf 𝒜 l).val ≅ (imageSubmodule (k := k) (n := n) l).toPresheafOfModules :=
    asIso (toImage (k := k) (n := n) l)
  (SheafOfModules.fullyFaithfulForget _).preimageIso e

/-- The image of `𝒪(l)` in `K_X`, an invertible submodule of `K_X`. -/
def imageInvertibleSubmodule (l : ℤ) : (Proj 𝒜).InvertibleTotalQuotientSubmodule where
  submodule := imageSubmodule l
  isSheaf := isSheaf_imageSubmodule l
  isInvertible := (ProjTwistingSheaf.isInvertible (adjoin_one_eq_top k n) l).of_iso (imageIso l)

/-! ### Orders of the image of a section -/

theorem ord_one (y : Proj 𝒜) : (Proj 𝒜).ord (1 : (Proj 𝒜).functionField) y = 0 := by
  have h := (Proj 𝒜).ord_mul (x := y) (one_ne_zero (α := (Proj 𝒜).functionField)) one_ne_zero
  rw [mul_one] at h
  omega

theorem ord_pow {κ : (Proj 𝒜).functionField} (hκ : κ ≠ 0) (y : Proj 𝒜) (m : ℕ) :
    (Proj 𝒜).ord (κ ^ m) y = m * (Proj 𝒜).ord κ y := by
  induction m with
  | zero => rw [pow_zero, ord_one, Nat.cast_zero, zero_mul]
  | succ m ih =>
    rw [pow_succ, Scheme.ord_mul (pow_ne_zero m hκ) hκ, ih]
    push_cast
    ring

theorem homogeneousFraction_eq_zero {g h : S} {d : ℕ} (hg : g.IsHomogeneous d)
    (hh : h.IsHomogeneous d) (h0 : h ≠ 0) (hg0 : g = 0) : homogeneousFraction hg hh h0 = 0 := by
  apply functionFieldToLocalization_injective
  rw [functionFieldToLocalization_homogeneousFraction, map_zero, hg0, Localization.mk_zero]

/-- A homogeneous fraction `g / h` has nonnegative order at the points of `D₊(h)`. -/
theorem ord_homogeneousFraction_nonneg {g h : S} {d : ℕ} (hg : g.IsHomogeneous d)
    (hh : h.IsHomogeneous d) (h0 : h ≠ 0) (y : Proj 𝒜) (hy : y ∈ Proj.basicOpen 𝒜 h) :
    0 ≤ (Proj 𝒜).ord (homogeneousFraction hg hh h0) y := by
  by_cases hg0 : g = 0
  · rw [homogeneousFraction_eq_zero hg hh h0 hg0, Scheme.ord_zero]
    rfl
  have : Nonempty (Proj.basicOpen 𝒜 h) := ⟨⟨y, hy⟩⟩
  have ha0 : hypersurfaceChartEquation g h hg hh ≠ 0 := by
    intro ha
    apply homogeneousFraction_ne_zero hg hh h0 hg0
    rw [homogeneousFraction, ha, map_zero]
  have := (Proj 𝒜).ord_le_smul hy ha0 1
  rw [ord_one] at this
  convert this using 2
  rw [Algebra.smul_def, mul_one]
  rfl

variable (hn : 0 < n)

/-- The hyperplane `H = V(x₀)` of `ℙⁿ_k`. -/
abbrev hyperplaneX0 : (Proj 𝒜).PrimeDivisor :=
  projectiveHyperplanePrimeDivisor hn (isHomogeneous_X k (0 : Fin (n + 1))) (X_ne_zero 0)

include hn in
/-- The order of `x₀ / ℓ` at a codimension-one point `y` outside `V(ℓ)` is `1` along `H = V(x₀)`
and `0` elsewhere. -/
theorem ord_X0_div {ℓ : S} (hℓ : ℓ.IsHomogeneous 1) (hℓ0 : ℓ ≠ 0) (y : Proj 𝒜)
    (hy1 : Order.coheight y = 1) (hy : y ∈ Proj.basicOpen 𝒜 ℓ) :
    (Proj 𝒜).ord (homogeneousFraction (isHomogeneous_X k (0 : Fin (n + 1))) hℓ hℓ0) y =
      (hyperplaneX0 hn).toWeilDivisor.1 y := by
  rw [show y = (⟨y, hy1⟩ : (Proj 𝒜).PrimeDivisor).1 from rfl, toWeilDivisor_apply_primeDivisor]
  split_ifs with hP
  · have hyH : y = (hyperplaneX0 hn).1 := congrArg Subtype.val hP
    refine ord_homogeneousFraction_eq_one _ hℓ hℓ0 y hy1 hy ?_ (X_ne_zero 0)
    rw [hyH]
    exact projectiveHypersurfacePrimeDivisor_asHomogeneousIdeal hn _ _
  · refine ord_homogeneousFraction_eq_zero _ hℓ hℓ0 y hy fun hX0 => hP (Subtype.ext ?_)
    refine (projectiveSpace_eq_of_coheight_eq_one (hyperplaneX0 hn).2 hy1 ?_).symm
    intro a ha
    have ha' : a ∈ Ideal.span {(X 0 : S)} := by
      rw [← projectiveHypersurfacePrimeDivisor_asHomogeneousIdeal hn
        (isHomogeneous_X k (0 : Fin (n + 1)))
        (irreducible_of_isHomogeneous_one (isHomogeneous_X k (0 : Fin (n + 1))) (X_ne_zero 0))]
      exact ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha'
    exact y.asHomogeneousIdeal.toIdeal.mul_mem_left c hX0

omit hn in
theorem homogeneousFraction_self {g : S} {d : ℕ} (hg : g.IsHomogeneous d) (h0 : g ≠ 0) :
    homogeneousFraction hg hg h0 = 1 := by
  apply functionFieldToLocalization_injective
  rw [functionFieldToLocalization_homogeneousFraction, map_one]
  exact Localization.mk_self (⟨g, genericPoint_mem_basicOpen h0⟩ : genericCompl k n)

omit hn in
/-- The value of `y / x₀^l` for `y = m / f`, split as `(m ℓ^{l⁻} / f ℓ^{l⁺}) · (x₀/ℓ)^{l⁻} ·
(ℓ/x₀)^{l⁺}`, for a nonzero linear form `ℓ`. -/
theorem twistToFunctionField_mk_eq (l : ℤ) {j : ℕ} {m : S} (hm : m ∈ gradedTwist 𝒜 l j) {f : S}
    (hf : f ∈ 𝒜 j) (hfx : f ∈ genericCompl k n) {ℓ : S} (hℓ : ℓ.IsHomogeneous 1) (hℓ0 : ℓ ≠ 0)
    (hlj : 0 ≤ l + j) :
    twistToFunctionField l (HomogeneousLocalizedModule.mk j m hm f hf hfx) =
      homogeneousFraction (g := m * ℓ ^ (-l).toNat) (h := f * ℓ ^ l.toNat) (d := j + l.toNat)
          (by
            have := (mem_homogeneousSubmodule _ m).mp (mem_of_mem_gradedTwist hm) |>.mul
              (isHomogeneous_pow_of_isHomogeneous_one hℓ (-l).toNat)
            convert this using 1
            omega)
          (((mem_homogeneousSubmodule _ f).mp hf).mul
            (isHomogeneous_pow_of_isHomogeneous_one hℓ l.toNat))
          (mul_ne_zero (fun h => hfx (h ▸ zero_mem _)) (pow_ne_zero _ hℓ0)) *
        homogeneousFraction (isHomogeneous_X k (0 : Fin (n + 1))) hℓ hℓ0 ^ (-l).toNat *
        homogeneousFraction hℓ (isHomogeneous_X k (0 : Fin (n + 1))) (X_ne_zero 0) ^ l.toNat := by
  apply functionFieldToLocalization_injective
  rw [functionFieldToLocalization_twistToFunctionField, twistVal_mk, map_mul, map_mul, map_pow,
    map_pow, functionFieldToLocalization_homogeneousFraction,
    functionFieldToLocalization_homogeneousFraction,
    functionFieldToLocalization_homogeneousFraction, Localization.mk_pow, Localization.mk_pow,
    Localization.mk_mul, Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul, SubmonoidClass.coe_pow]
  ring

include hn in
/-- The order formula for `y / x₀^l` with `y = m / f`. -/
theorem ord_twistToFunctionField_mk (l : ℤ) {j : ℕ} {m : S} (hm : m ∈ gradedTwist 𝒜 l j)
    {f : S} (hf : f ∈ 𝒜 j) (hfx : f ∈ genericCompl k n) {ℓ : S} (hℓ : ℓ.IsHomogeneous 1)
    (hℓ0 : ℓ ≠ 0) (hlj : 0 ≤ l + j) (hm0 : m ≠ 0) (y : Proj 𝒜) (hy1 : Order.coheight y = 1)
    (hy : y ∈ Proj.basicOpen 𝒜 ℓ) :
    (Proj 𝒜).ord (twistToFunctionField l (HomogeneousLocalizedModule.mk j m hm f hf hfx)) y =
      (Proj 𝒜).ord (homogeneousFraction (g := m * ℓ ^ (-l).toNat) (h := f * ℓ ^ l.toNat)
          (d := j + l.toNat)
          (by
            have := (mem_homogeneousSubmodule _ m).mp (mem_of_mem_gradedTwist hm) |>.mul
              (isHomogeneous_pow_of_isHomogeneous_one hℓ (-l).toNat)
            convert this using 1
            omega)
          (((mem_homogeneousSubmodule _ f).mp hf).mul
            (isHomogeneous_pow_of_isHomogeneous_one hℓ l.toNat))
          (mul_ne_zero (fun h => hfx (h ▸ zero_mem _)) (pow_ne_zero _ hℓ0))) y -
        l * (hyperplaneX0 hn).toWeilDivisor.1 y := by
  rw [twistToFunctionField_mk_eq l hm hf hfx hℓ hℓ0 hlj]
  have hu0 := homogeneousFraction_ne_zero (isHomogeneous_X k (0 : Fin (n + 1))) hℓ hℓ0
    (X_ne_zero 0)
  have hv0 := homogeneousFraction_ne_zero hℓ (isHomogeneous_X k (0 : Fin (n + 1)))
    (X_ne_zero 0) hℓ0
  have huv : homogeneousFraction (isHomogeneous_X k (0 : Fin (n + 1))) hℓ hℓ0 *
      homogeneousFraction hℓ (isHomogeneous_X k (0 : Fin (n + 1))) (X_ne_zero 0) = 1 := by
    rw [homogeneousFraction_mul, ← homogeneousFraction_self ((isHomogeneous_X k
      (0 : Fin (n + 1))).mul hℓ) (mul_ne_zero (X_ne_zero 0) hℓ0)]
    apply homogeneousFraction_eq_of_mul_eq
    ring
  have hord : (Proj 𝒜).ord (homogeneousFraction hℓ (isHomogeneous_X k (0 : Fin (n + 1)))
      (X_ne_zero 0)) y = -(Proj 𝒜).ord (homogeneousFraction (isHomogeneous_X k
        (0 : Fin (n + 1))) hℓ hℓ0) y := by
    have := (Proj 𝒜).ord_mul (x := y) hu0 hv0
    rw [huv, ord_one] at this
    omega
  have hg0 : m * ℓ ^ (-l).toNat ≠ 0 := mul_ne_zero hm0 (pow_ne_zero _ hℓ0)
  have h1 := homogeneousFraction_ne_zero (g := m * ℓ ^ (-l).toNat) (h := f * ℓ ^ l.toNat)
    (d := j + l.toNat) (by
      have := (mem_homogeneousSubmodule _ m).mp (mem_of_mem_gradedTwist hm) |>.mul
        (isHomogeneous_pow_of_isHomogeneous_one hℓ (-l).toNat)
      convert this using 1
      omega)
    (((mem_homogeneousSubmodule _ f).mp hf).mul
      (isHomogeneous_pow_of_isHomogeneous_one hℓ l.toNat))
    (mul_ne_zero (fun h => hfx (h ▸ zero_mem _)) (pow_ne_zero _ hℓ0)) hg0
  rw [Scheme.ord_mul (mul_ne_zero h1 (pow_ne_zero _ hu0)) (pow_ne_zero _ hv0),
    Scheme.ord_mul h1 (pow_ne_zero _ hu0), ord_pow hu0, ord_pow hv0, hord,
    ord_X0_div hn hℓ hℓ0 y hy1 hy]
  have : ((-l).toNat : ℤ) - l.toNat = -l := by omega
  linear_combination (hyperplaneX0 hn).toWeilDivisor.1 y * this

omit hn in
theorem exists_linear_notMem (y : Proj 𝒜) :
    ∃ ℓ : S, ℓ.IsHomogeneous 1 ∧ ℓ ≠ 0 ∧ y ∈ Proj.basicOpen 𝒜 ℓ := by
  obtain ⟨ℓ, hℓ1, hℓy⟩ := ProjTwistingSheaf.exists_mem_one_notMem (adjoin_one_eq_top k n) y
  refine ⟨ℓ, (mem_homogeneousSubmodule 1 ℓ).mp hℓ1, ?_, hℓy⟩
  rintro rfl
  exact hℓy (zero_mem _)

include hn in
/-- **Lower bound for the order of `s / x₀^l`**: for a section `s` of `𝒪(l)` near a
codimension-one point `y`, the rational function `s / x₀^l` has order at least `-l · [y ∈ H]`
at `y`, where `H = V(x₀)`. -/
theorem le_ord_twistToFunctionField (l : ℤ) {V : (Proj 𝒜).Opens}
    (s : (ProjGradedModuleSheaf.sheafInType 𝒜 (gradedTwist 𝒜 l)).1.obj (op V)) (h : η ∈ V)
    (hs0 : twistToFunctionField l (s.1 ⟨η, h⟩) ≠ 0) (y : Proj 𝒜) (hyV : y ∈ V)
    (hy1 : Order.coheight y = 1) :
    -(l * (hyperplaneX0 hn).toWeilDivisor.1 y) ≤
      (Proj 𝒜).ord (twistToFunctionField l (s.1 ⟨η, h⟩)) y := by
  obtain ⟨W, hyW, iWV, j, m, hm, f, hf, f_nin, w⟩ := s.2 ⟨y, hyV⟩
  have hηW : η ∈ W := Scheme.genericPoint_mem_opens_of_mem (X := Proj 𝒜) hyW
  have hsη : s.1 ⟨η, h⟩ = HomogeneousLocalizedModule.mk j m hm f hf (f_nin ⟨η, hηW⟩) :=
    w ⟨η, hηW⟩
  obtain ⟨ℓ, hℓ, hℓ0, hℓy⟩ := exists_linear_notMem y
  have hm0 : m ≠ 0 := by
    rintro rfl
    apply hs0
    rw [hsη]
    convert map_zero (twistToFunctionField (k := k) (n := n) l)
    ext
    exact LocalizedModule.zero_mk _
  have hlj : 0 ≤ l + j := by
    by_contra hneg
    exact hm0 (eq_zero_of_mem_gradedTwist hm (by omega))
  rw [hsη]
  erw [ord_twistToFunctionField_mk hn l hm hf (f_nin ⟨η, hηW⟩) hℓ hℓ0 hlj hm0 y hy1 hℓy]
  have hy' : y ∈ Proj.basicOpen 𝒜 (f * ℓ ^ l.toNat) := by
    rw [Proj.mem_basicOpen]
    intro hmem
    rcases y.isPrime.mem_or_mem hmem with h1 | h1
    · exact f_nin ⟨y, hyW⟩ h1
    · exact hℓy (y.isPrime.mem_of_pow_mem _ h1)
  have := ord_homogeneousFraction_nonneg (g := m * ℓ ^ (-l).toNat) (h := f * ℓ ^ l.toNat)
    (d := j + l.toNat) (by
      have := (mem_homogeneousSubmodule _ m).mp (mem_of_mem_gradedTwist hm) |>.mul
        (isHomogeneous_pow_of_isHomogeneous_one hℓ (-l).toNat)
      convert this using 1
      omega)
    (((mem_homogeneousSubmodule _ f).mp hf).mul
      (isHomogeneous_pow_of_isHomogeneous_one hℓ l.toNat))
    (mul_ne_zero (fun h => f_nin ⟨η, hηW⟩ (h ▸ zero_mem _)) (pow_ne_zero _ hℓ0)) y hy'
  linarith

omit hn in
theorem pow_toNat_mem_gradedTwist (l : ℤ) {ℓ : S} (hℓ : ℓ.IsHomogeneous 1) :
    ℓ ^ l.toNat ∈ gradedTwist 𝒜 l ((-l).toNat : ℕ) :=
  (mem_gradedTwist_of_eq (k := l.toNat) (by omega)).2
    ((mem_homogeneousSubmodule _ _).2 (isHomogeneous_pow_of_isHomogeneous_one hℓ _))

/-- The section `ℓ^l` of `𝒪(l)` over `D₊(ℓ^{l⁻})`: the fraction `ℓ^{l⁺} / ℓ^{l⁻}`. -/
def linearPowSection (l : ℤ) {ℓ : S} (hℓ : ℓ.IsHomogeneous 1) :
    (projTwistingSheaf 𝒜 l).val.obj (op (Proj.basicOpen 𝒜 (ℓ ^ (-l).toNat))) :=
  ProjGradedModuleSheaf.sectionInBasicOpen 𝒜 (gradedTwist 𝒜 l) ((-l).toNat) (ℓ ^ l.toNat)
    (pow_toNat_mem_gradedTwist l hℓ) (ℓ ^ (-l).toNat)
    ((mem_homogeneousSubmodule _ _).2 (isHomogeneous_pow_of_isHomogeneous_one hℓ _))

include hn in
/-- The section `ℓ^l` has order exactly `-l · [y ∈ H]` at a codimension-one point `y ∉ V(ℓ)`. -/
theorem ord_linearPowSection (l : ℤ) {ℓ : S} (hℓ : ℓ.IsHomogeneous 1) (hℓ0 : ℓ ≠ 0)
    (h : η ∈ Proj.basicOpen 𝒜 (ℓ ^ (-l).toNat)) (y : Proj 𝒜) (hy1 : Order.coheight y = 1)
    (hℓy : y ∈ Proj.basicOpen 𝒜 ℓ) :
    (Proj 𝒜).ord (twistToFunctionField l
        ((linearPowSection l hℓ : (ProjGradedModuleSheaf.sheafInType 𝒜 (gradedTwist 𝒜 l)).1.obj
          (op (Proj.basicOpen 𝒜 (ℓ ^ (-l).toNat)))).1 ⟨η, h⟩)) y =
      -(l * (hyperplaneX0 hn).toWeilDivisor.1 y) := by
  have hval : (linearPowSection l hℓ : (ProjGradedModuleSheaf.sheafInType 𝒜
      (gradedTwist 𝒜 l)).1.obj (op (Proj.basicOpen 𝒜 (ℓ ^ (-l).toNat)))).1 ⟨η, h⟩ =
      HomogeneousLocalizedModule.mk ((-l).toNat) (ℓ ^ l.toNat) (pow_toNat_mem_gradedTwist l hℓ)
        (ℓ ^ (-l).toNat) ((mem_homogeneousSubmodule _ _).2
          (isHomogeneous_pow_of_isHomogeneous_one hℓ _)) h := rfl
  rw [hval]
  erw [ord_twistToFunctionField_mk hn l (pow_toNat_mem_gradedTwist l hℓ)
    ((mem_homogeneousSubmodule _ _).2 (isHomogeneous_pow_of_isHomogeneous_one hℓ _)) h hℓ hℓ0
    (by omega) (pow_ne_zero _ hℓ0) y hy1 hℓy]
  rw [ord_homogeneousFraction_eq_zero]
  · ring
  · rw [Proj.mem_basicOpen]
    intro hmem
    rcases y.isPrime.mem_or_mem hmem with h1 | h1 <;>
      exact (Proj.mem_basicOpen _ _ _).1 hℓy (y.isPrime.mem_of_pow_mem _ h1)
  · intro hmem
    rcases y.isPrime.mem_or_mem hmem with h1 | h1 <;>
      exact (Proj.mem_basicOpen _ _ _).1 hℓy (y.isPrime.mem_of_pow_mem _ h1)

/-! ### The Cartier divisor of the image -/

omit hn in
/-- A regular function has nonnegative order at every codimension-one point of its domain. -/
theorem ord_germ_nonneg {U : (Proj 𝒜).Opens} (y : Proj 𝒜) (hyU : y ∈ U) (r : Γ(Proj 𝒜, U)) :
    0 ≤ (Proj 𝒜).ord ((Proj 𝒜).presheaf.germ U η
      (Scheme.genericPoint_mem_opens_of_mem (X := Proj 𝒜) hyU) r) y := by
  have : Nonempty U := ⟨⟨y, hyU⟩⟩
  by_cases hr : r = 0
  · rw [hr, map_zero, Scheme.ord_zero]
    rfl
  have := (Proj 𝒜).ord_le_smul hyU hr 1
  rw [ord_one] at this
  convert this using 2
  rw [Algebra.smul_def, mul_one]
  rfl

/-- A Cartier divisor `D_l` whose sheaf `O_X(D_l)` is the image of `𝒪(l)` in `K_X`. -/
def imageDivisor (l : ℤ) : (Proj 𝒜).CartierDivisor :=
  Classical.choose
    (Scheme.CartierDivisor.toInvertibleSubmodule_surjective (imageInvertibleSubmodule l))

omit hn in
theorem imageDivisor_submodule (l : ℤ) :
    (imageDivisor (k := k) (n := n) l).submodule = imageSubmodule l :=
  congrArg Scheme.InvertibleTotalQuotientSubmodule.submodule (Classical.choose_spec
    (Scheme.CartierDivisor.toInvertibleSubmodule_surjective (imageInvertibleSubmodule l)))

omit hn in
theorem isSection_imageDivisor_iff (l : ℤ) {U : (Proj 𝒜).Opens}
    (t : (Proj 𝒜).totalQuotientModule.val.obj (op U)) :
    (imageDivisor (k := k) (n := n) l).IsSection (U := U) t ↔
      ∃ s, (twistToK l).val.app (op U) s = t := by
  rw [← Scheme.CartierDivisor.mem_submodule_iff, imageDivisor_submodule]
  rfl

include hn in
/-- **The Weil divisor of `D_l` is `l · H`**: its coefficient at a codimension-one point `y` is
`l · [y ∈ H]`, where `H = V(x₀)`. -/
theorem weilCoeff_imageDivisor (l : ℤ) (y : Proj 𝒜) (hy1 : Order.coheight y = 1) :
    (imageDivisor (k := k) (n := n) l).weilCoeff y = l * (hyperplaneX0 hn).toWeilDivisor.1 y := by
  set D := imageDivisor (k := k) (n := n) l
  obtain ⟨V, f, hyV, hf⟩ := D.exists_localEquation y
  have hηV : η ∈ V := Scheme.genericPoint_mem_opens_of_mem (X := Proj 𝒜) hyV
  rw [D.weilCoeff_eq f hf hyV]
  set κ : (Proj 𝒜).functionField :=
    (Scheme.totalQuotientUnitsEquivFunctionField V hηV f : (Proj 𝒜).functionField) with hκ
  have hκ0 : κ ≠ 0 := Units.ne_zero _
  -- upper bound, from the section `f⁻¹` of `O_X(D)`
  obtain ⟨s, hs⟩ := (isSection_imageDivisor_iff l _).1 (D.isSection_inv hf (le_refl V))
  have hsval : twistToFunctionField l
      ((s : (ProjGradedModuleSheaf.sheafInType 𝒜 (gradedTwist 𝒜 l)).1.obj (op V)).1 ⟨η, hηV⟩) =
      κ⁻¹ := by
    rw [← twistToK_app_apply l hηV s, hs, Scheme.CartierDivisor.kMap_id, hκ,
      ← Units.val_inv_eq_inv_val, ← map_inv]
    rfl
  have hup := le_ord_twistToFunctionField hn l s hηV (by rw [hsval]; exact inv_ne_zero hκ0) y
    hyV hy1
  rw [hsval, Scheme.ord_inv_eq_neg hκ0] at hup
  -- lower bound, from the section `ℓ^l` of `𝒪(l)` on `D₊(ℓ^{l⁻})`
  obtain ⟨ℓ, hℓ, hℓ0, hℓy⟩ := exists_linear_notMem y
  have hyB : y ∈ Proj.basicOpen 𝒜 (ℓ ^ (-l).toNat) := by
    rw [Proj.mem_basicOpen]
    exact fun h1 => (Proj.mem_basicOpen _ _ _).1 hℓy (y.isPrime.mem_of_pow_mem _ h1)
  have hyW : y ∈ V ⊓ Proj.basicOpen 𝒜 (ℓ ^ (-l).toNat) := ⟨hyV, hyB⟩
  have hηW := Scheme.genericPoint_mem_opens_of_mem (X := Proj 𝒜) hyW
  have hηB := Scheme.genericPoint_mem_opens_of_mem (X := Proj 𝒜) hyB
  set g := (projTwistingSheaf 𝒜 l).val.map
    (homOfLE (inf_le_right : V ⊓ Proj.basicOpen 𝒜 (ℓ ^ (-l).toNat) ≤ _)).op
    (linearPowSection l hℓ)
  have ht := (isSection_imageDivisor_iff l ((twistToK l).val.app (op _) g)).2 ⟨g, rfl⟩
  obtain ⟨r, hr⟩ := ht _ le_rfl _ (D.restrict_eq_of_le inf_le_left hf)
  have hr' := congrArg (Scheme.totalQuotientSheafEquivFunctionField _ hηW) hr
  rw [map_mul] at hr'
  erw [Scheme.CartierDivisor.kMap_id, twistToK_app_apply l hηW,
    Scheme.totalQuotientSheafEquivFunctionField_toTotalQuotientSheaf] at hr'
  have hgval : twistToFunctionField l
      ((g : (ProjGradedModuleSheaf.sheafInType 𝒜 (gradedTwist 𝒜 l)).1.obj (op _)).1 ⟨η, hηW⟩) =
      twistToFunctionField l ((linearPowSection l hℓ : (ProjGradedModuleSheaf.sheafInType 𝒜
        (gradedTwist 𝒜 l)).1.obj (op (Proj.basicOpen 𝒜 (ℓ ^ (-l).toNat)))).1 ⟨η, hηB⟩) := rfl
  have hfval : Scheme.totalQuotientSheafEquivFunctionField _ hηW
      (Scheme.kUnitVal ((Proj 𝒜).totalQuotientUnitsSheaf.obj.map
        (homOfLE (inf_le_left : V ⊓ Proj.basicOpen 𝒜 (ℓ ^ (-l).toNat) ≤ V)).op f)) = κ := by
    rw [hκ, ← Scheme.totalQuotientUnitsEquivFunctionField_map
      (inf_le_left : V ⊓ Proj.basicOpen 𝒜 (ℓ ^ (-l).toNat) ≤ V) hηW f]
    rfl
  rw [hgval, hfval] at hr'
  have hgen := ord_linearPowSection hn l hℓ hℓ0 hηB y hy1 hℓy
  have hgen0 : twistToFunctionField l ((linearPowSection l hℓ : (ProjGradedModuleSheaf.sheafInType
      𝒜 (gradedTwist 𝒜 l)).1.obj (op (Proj.basicOpen 𝒜 (ℓ ^ (-l).toNat)))).1 ⟨η, hηB⟩) ≠ 0 := by
    intro h0
    have := congrArg functionFieldToLocalization h0
    rw [functionFieldToLocalization_twistToFunctionField, map_zero] at this
    exact pow_ne_zero _ hℓ0 (eq_zero_of_twistVal_mk_eq_zero (j := (-l).toNat) l
      (pow_toNat_mem_gradedTwist l hℓ)
      ((mem_homogeneousSubmodule _ _).2 (isHomogeneous_pow_of_isHomogeneous_one hℓ _)) hηB this)
  have hlow := ord_germ_nonneg y hyW r
  rw [hr', Scheme.ord_mul hgen0 hκ0, hgen] at hlow
  linarith

include hn in
theorem cartierToWeil_imageDivisor (l : ℤ) :
    Scheme.cartierToWeil (imageDivisor (k := k) (n := n) l) =
      l • (hyperplaneX0 hn).toWeilDivisor := by
  apply Scheme.WeilDivisor.ext_apply
  intro x
  change (imageDivisor (k := k) (n := n) l).weilCoeff x = _
  rw [show (l • (hyperplaneX0 hn).toWeilDivisor).1 x = l * (hyperplaneX0 hn).toWeilDivisor.1 x by
    simp]
  by_cases hx : Order.coheight x = 1
  · exact weilCoeff_imageDivisor hn l x hx
  · rw [(hyperplaneX0 hn).toWeilDivisor_apply_of_ne
      fun h => hx (by rw [h]; exact (hyperplaneX0 hn).2), mul_zero]
    exact Scheme.ord_eq_zero_of_coheight_neq_one hx _

omit hn in
theorem projectiveSpace_isLocallyFactorial : (Proj 𝒜).IsLocallyFactorial :=
  (Proj 𝒜).isLocallyFactorial_of_isRegularLocalRing projectiveSpace_isRegular.2

include hn in
theorem weilCartierEquiv_smul_hyperplane (l : ℤ) :
    Scheme.weilCartierEquiv projectiveSpace_isLocallyFactorial
        (l • (hyperplaneX0 (k := k) hn).toWeilDivisor) = imageDivisor l := by
  apply (Scheme.weilCartierEquiv projectiveSpace_isLocallyFactorial).symm.injective
  rw [AddEquiv.symm_apply_apply, Scheme.weilCartierEquiv_symm_apply, cartierToWeil_imageDivisor hn]

omit hn in
theorem projTwistingSheaf_isInvertible (l : ℤ) : (projTwistingSheaf 𝒜 l).IsInvertible :=
  ProjTwistingSheaf.isInvertible (adjoin_one_eq_top k n) l

omit hn in
/-- `𝒪(l) ≅ O_X(D_l)`. -/
def projTwistingSheafIsoImageDivisorSheaf (l : ℤ) :
    projTwistingSheaf 𝒜 l ≅ (imageDivisor (k := k) (n := n) l).sheaf :=
  imageIso l ≪≫ eqToIso (by
    unfold Scheme.CartierDivisor.sheaf
    congr 1
    exact congrArg _ (imageDivisor_submodule l).symm)

end ProjectiveSpacePicard

open ProjectiveSpacePicard Ringed

set_option backward.isDefEq.respectTransparency false

/-- The isomorphism `Pic ℙⁿ_k ≅ ℤ`, the composite of the isomorphism `Pic ≅ Cl` of the locally
factorial scheme `ℙⁿ_k` and the degree `Cl ℙⁿ_k ≅ ℤ`. -/
def projectiveSpacePicardEquiv (hn : 0 < n) : Additive (Pic (Proj 𝒜).sheaf) ≃+ ℤ :=
  (Scheme.weilClassEquivPicard projectiveSpace_isLocallyFactorial).symm.trans
    (projectiveSpaceClassGroupEquiv hn)

/-- The isomorphism `Pic ℙⁿ_k ≅ ℤ` sends the class of `𝒪(l)` to `l`; in particular `𝒪(1)` goes
to the generator `1`. -/
theorem projectiveSpacePicardEquiv_projTwistingSheaf (hn : 0 < n) (l : ℤ) :
    projectiveSpacePicardEquiv hn (Additive.ofMul (Pic.mk (R := (Proj 𝒜).sheaf)
      (projTwistingSheaf 𝒜 l)
      ((Scheme.Modules.isInvertible_iff_ringed _).1 (projTwistingSheaf_isInvertible l)))) = l := by
  have hcls := Scheme.weilClassEquivPicard_weilDivisorClassHom
    (projectiveSpace_isLocallyFactorial (k := k) (n := n)) (l • (hyperplaneX0 hn).toWeilDivisor)
  have hpic : Pic.mk (R := (Proj 𝒜).sheaf) (projTwistingSheaf 𝒜 l)
      ((Scheme.Modules.isInvertible_iff_ringed _).1 (projTwistingSheaf_isInvertible l)) =
      Pic.mk (R := (Proj 𝒜).sheaf)
        (Scheme.weilCartierEquiv projectiveSpace_isLocallyFactorial
          (l • (hyperplaneX0 hn).toWeilDivisor)).sheaf
        ((Scheme.Modules.isInvertible_iff_ringed _).1
          (Scheme.weilCartierEquiv projectiveSpace_isLocallyFactorial
            (l • (hyperplaneX0 hn).toWeilDivisor)).isInvertible_sheaf) := by
    rw [Pic.mk_eq_mk_iff, weilCartierEquiv_smul_hyperplane hn]
    exact ⟨projTwistingSheafIsoImageDivisorSheaf l⟩
  rw [projectiveSpacePicardEquiv, AddEquiv.trans_apply, hpic, ← hcls, AddEquiv.symm_apply_apply,
    map_zsmul, map_zsmul, projectiveSpaceClassGroupEquiv_hyperplane, smul_eq_mul, mul_one]

/-- **Hartshorne II.6, Corollary 6.17.** For a field `k` and `n ≥ 1`, every invertible sheaf on
`ℙⁿ_k` is isomorphic to `𝒪(l)` for a unique integer `l`. -/
theorem exists_unique_iso_projTwistingSheaf (hn : 0 < n) (L : (Proj 𝒜).Modules)
    (hL : L.IsInvertible) : ∃! l : ℤ, Nonempty (L ≅ projTwistingSheaf 𝒜 l) := by
  have hL' := (Scheme.Modules.isInvertible_iff_ringed _).1 hL
  have hT : ∀ l : ℤ, IsInvertible (projTwistingSheaf 𝒜 l) := fun l =>
    (Scheme.Modules.isInvertible_iff_ringed _).1 (projTwistingSheaf_isInvertible l)
  refine ⟨projectiveSpacePicardEquiv hn (Additive.ofMul (Pic.mk (R := (Proj 𝒜).sheaf) L hL')),
    ?_, fun l ⟨e⟩ => ?_⟩
  · dsimp only
    rw [← Pic.mk_eq_mk_iff hL' (hT _)]
    apply Additive.ofMul.injective
    apply (projectiveSpacePicardEquiv hn).injective
    rw [projectiveSpacePicardEquiv_projTwistingSheaf]
  · have : Pic.mk (R := (Proj 𝒜).sheaf) L hL' = Pic.mk (R := (Proj 𝒜).sheaf) _ (hT l) :=
      (Pic.mk_eq_mk_iff hL' (hT l)).2 ⟨e⟩
    rw [this, projectiveSpacePicardEquiv_projTwistingSheaf]

end Hartshorne

/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ProjectiveSpaceClassGroup
import Hartshorne.Scheme.ProjTwistingSheaf
import Hartshorne.Scheme.LocallyFactorialClassPicard
import Hartshorne.Scheme.TotalQuotientIntegral

/-!
# The Picard group of projective space

Hartshorne, *Algebraic Geometry*, II.6, Corollary 6.17 (p. 145).

Work in progress: the embedding of the twisting sheaf `𝒪(l)` into the sheaf of rational functions
`K_X` of `X = ℙⁿ_k`, `s ↦ s / x₀^l`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization Opposite

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

end ProjectiveSpacePicard

end Hartshorne

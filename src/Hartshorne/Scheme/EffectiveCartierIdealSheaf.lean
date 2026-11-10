/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.EffectiveCartierDivisor
import Hartshorne.Scheme.ClosedImmersionIdealSheaf

/-!
# The ideal sheaf of an effective Cartier divisor

Hartshorne, *Algebraic Geometry*, II, Proposition 6.18 (pp. 145–146).

Let `D` be an effective Cartier divisor on `X` and `Y = (idealSheafData hD).subscheme` its
associated locally principal closed subscheme, with closed immersion `i : Y ⟶ X`. The ideal sheaf
`I_Y = ker (𝒪_X ⟶ i_* 𝒪_Y)` of `Y` (`Hartshorne.closedImmersionIdealSheaf`) is isomorphic to
`𝒪_X(-D)`, compatibly with the inclusions of both into `𝒪_X`
(`Scheme.CartierDivisor.idealSheafIso`, `Scheme.CartierDivisor.idealSheafIso_hom_ι`).
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

universe u

noncomputable section

variable {X : Scheme.{u}}

/-- A section of an `𝒪_X`-module which vanishes on a neighbourhood of every point is zero. -/
theorem Scheme.Modules.section_eq_zero_of_locally {M : X.Modules} {U : X.Opens} (s : Γ(M, U))
    (h : ∀ x ∈ U, ∃ (W : X.Opens) (hWU : W ≤ U), x ∈ W ∧ M.presheaf.map (homOfLE hWU).op s = 0) :
    s = 0 := by
  refine TopCat.Presheaf.section_ext ⟨M.presheaf, M.isSheaf⟩ U s 0 fun x hx => ?_
  obtain ⟨W, hWU, hxW, hW⟩ := h x hx
  change M.presheaf.germ U x hx s = M.presheaf.germ U x hx 0
  rw [← TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE hWU) x hxW s, hW, map_zero, map_zero]

namespace Scheme.CartierDivisor

open Hartshorne

variable {D : X.CartierDivisor} (hD : D.IsEffective)

/-- The closed immersion of the locally principal closed subscheme associated to `D`. -/
abbrev subschemeι : (idealSheafData hD).subscheme ⟶ X := (idealSheafData hD).subschemeι

/-- `𝒪_X(-D) ⟶ 𝒪_X` as a morphism of `X.Modules`. -/
abbrev idealSheafιX : ((-D).sheaf : X.Modules) ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
  idealSheafι hD

/-- `𝒪_X ⟶ i_* 𝒪_Y` as a morphism of `X.Modules`. -/
abbrev toSubschemeX : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶
    (Scheme.Modules.pushforward (subschemeι hD)).obj
      (SheafOfModules.unit (idealSheafData hD).subscheme.ringCatSheaf) :=
  structureSheafToPushforward (subschemeι hD)

/-- Over an affine open, the image of `𝒪_X(-D)` restricts to zero on the subscheme. -/
theorem structureSheafToPushforward_idealSheafι_app_affine (W : X.affineOpens)
    (s : Γ((-D).sheaf, (W : X.Opens))) :
    Scheme.Modules.Hom.app (toSubschemeX hD) W ((idealSheafιX hD).app W s) = 0 := by
  have hmem : (idealSheafιX hD).app W s ∈
      RingHom.ker ((idealSheafDataOfHom (idealSheafι hD)).subschemeι.app W).hom := by
    rw [ker_subschemeι_app_idealSheafDataOfHom]
    exact ⟨s, rfl⟩
  exact hmem

/-- `𝒪_X(-D) ⟶ 𝒪_X ⟶ i_* 𝒪_Y` is zero. -/
theorem idealSheafι_comp_structureSheafToPushforward :
    idealSheafιX hD ≫ structureSheafToPushforward (subschemeι hD) = 0 := by
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  ext s
  change Scheme.Modules.Hom.app (toSubschemeX hD) V ((idealSheafιX hD).app V s) = 0
  refine Scheme.Modules.section_eq_zero_of_locally _ fun x hx => ?_
  obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset hx
  refine ⟨W, hWV, hxW, ?_⟩
  erw [← modules_app_res (toSubschemeX hD) hWV, ← modules_app_res (idealSheafιX hD) hWV]
  exact structureSheafToPushforward_idealSheafι_app_affine hD ⟨W, hW⟩ _

/-- The comparison `𝒪_X(-D) ⟶ I_Y`. -/
def toIdealSheaf : (-D).sheaf ⟶ closedImmersionIdealSheaf (subschemeι hD) :=
  kernel.lift _ (idealSheafιX hD) (idealSheafι_comp_structureSheafToPushforward hD)

@[reassoc (attr := simp)]
theorem toIdealSheaf_ι :
    toIdealSheaf hD ≫ closedImmersionIdealSheafι (subschemeι hD) = idealSheafιX hD :=
  kernel.lift_ι _ _ _

instance : Mono (toIdealSheaf hD) := mono_of_mono_fac (toIdealSheaf_ι hD)

/-- On affine opens, `𝒪_X(-D) ⟶ I_Y` is surjective on sections. -/
theorem toIdealSheaf_app_surjective (W : X.affineOpens) :
    Function.Surjective ((toIdealSheaf hD).app W) := by
  intro t
  set g := toSubschemeX hD
  have ht : Scheme.Modules.Hom.app g W ((closedImmersionIdealSheafι (subschemeι hD)).app W t) = 0 := by
    exact congrArg (fun φ => Scheme.Modules.Hom.app φ W t)
      (kernel.condition (structureSheafToPushforward (subschemeι hD)))
  have hmem : (closedImmersionIdealSheafι (subschemeι hD)).app W t ∈
      RingHom.ker ((idealSheafDataOfHom (idealSheafι hD)).subschemeι.app W).hom := ht
  rw [ker_subschemeι_app_idealSheafDataOfHom] at hmem
  obtain ⟨s, hs⟩ := hmem
  refine ⟨s, modules_app_injective (closedImmersionIdealSheafι (subschemeι hD)) W ?_⟩
  change ((toIdealSheaf hD) ≫ closedImmersionIdealSheafι (subschemeι hD)).app W s = _
  rw [toIdealSheaf_ι]
  exact hs

instance : Epi (toIdealSheaf hD) := by
  refine Preadditive.epi_of_cokernel_zero (Scheme.Modules.hom_ext _ _ fun V => ?_)
  ext u
  change (cokernel.π (toIdealSheaf hD)).app V u = 0
  refine Scheme.Modules.section_eq_zero_of_locally _ fun x hx => ?_
  obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset hx
  refine ⟨W, hWV, hxW, ?_⟩
  rw [← modules_app_res (cokernel.π (toIdealSheaf hD)) hWV u]
  obtain ⟨s, hs⟩ := toIdealSheaf_app_surjective hD ⟨W, hW⟩
    ((closedImmersionIdealSheaf (subschemeι hD)).presheaf.map (homOfLE hWV).op u)
  erw [← hs]
  change (toIdealSheaf hD ≫ cokernel.π (toIdealSheaf hD)).app W s = 0
  rw [cokernel.condition]
  rfl

instance : IsIso (toIdealSheaf hD) := isIso_of_mono_of_epi _

/-- **Hartshorne II, Proposition 6.18.** For an effective Cartier divisor `D` with associated
locally principal closed subscheme `Y`, the ideal sheaf `I_Y ⊆ 𝒪_X` is isomorphic to
`𝒪_X(-D)` as a subsheaf of `𝒪_X` (`idealSheafIso_hom_ι`). -/
def idealSheafIso : (-D).sheaf ≅ closedImmersionIdealSheaf (subschemeι hD) :=
  asIso (toIdealSheaf hD)

@[reassoc (attr := simp)]
theorem idealSheafIso_hom_ι :
    (idealSheafIso hD).hom ≫ closedImmersionIdealSheafι (subschemeι hD) = idealSheafιX hD :=
  toIdealSheaf_ι hD

end Scheme.CartierDivisor

end

end AlgebraicGeometry

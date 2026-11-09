/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ExteriorPerfectPairing
import Hartshorne.RingedSpace.PicardGroup

/-!
# A rank-two locally free sheaf is its dual twisted by its determinant

Hartshorne, *Algebraic Geometry*, II, Exercise 5.16(b) (printed p. 127).

For an `𝒪_X`-module `F` on a ringed space, the degree-one exterior power is `F` itself:
`moduleSheafExteriorPowerOneIso F : ⋀^1 F ≅ F`, the sheafification of the sectionwise
isomorphisms `⋀^1 F(U) ≅ F(U)` (Mathlib's `exteriorPower.oneEquiv`), followed by the counit of
sheafification at the sheaf `F`.

For `F` locally free of rank `2`, the perfect exterior-power pairing with `r = s = 1`, `n = 2`
(`ExteriorPerfectPairing.exteriorPowerDualTensorIso`) gives `⋀^1 F ≅ (⋀^1 F)^∨ ⊗ ⋀^2 F`;
replacing `⋀^1 F` by `F` on both sides gives `rankTwoDualTensorIso : F ≅ F^∨ ⊗ ⋀^2 F`.
-/

universe u

open CategoryTheory TopologicalSpace Opposite

namespace Hartshorne

open SheafTensorOperations

section DegreeOne

variable {A : Type u} [CommRing A] {M : Type u} [AddCommGroup M] [Module A M]
  {B : Type u} [CommRing B] {N : Type u} [AddCommGroup N] [Module B N]

/-- The identification `⋀^1 M ≅ M` is natural for semilinear maps. -/
theorem exteriorPower_oneEquiv_exteriorPowerMap (σ : A →+* B) (f : M →ₛₗ[σ] N)
    (x : ⋀[A]^1 M) :
    exteriorPower.oneEquiv B N (exteriorPowerMap 1 σ f x) =
      f (exteriorPower.oneEquiv A M x) := by
  obtain ⟨m, rfl⟩ := (exteriorPower.oneEquiv A M).symm.surjective x
  have hm : (exteriorPower.oneEquiv A M).symm m = exteriorPower.ιMulti A 1 (fun _ => m) := by
    apply (exteriorPower.oneEquiv A M).injective
    rw [LinearEquiv.apply_symm_apply, exteriorPower.oneEquiv_ιMulti]
  rw [hm, exteriorPowerMap_ιMulti, exteriorPower.oneEquiv_ιMulti,
    exteriorPower.oneEquiv_ιMulti]

end DegreeOne

section DegreeOneSheaf

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{u}}
  (F : SheafOfModules.{u} (siteRingCatSheaf R))

/-- The presheaf `U ↦ ⋀^1 F(U)` is the presheaf of sections of `F`. -/
noncomputable def exteriorPowerPresheafOneIso :
    moduleSheafExteriorPowerPresheaf 1 F ≅
      (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 _)).obj F :=
  PresheafOfModules.isoMk (fun U => (exteriorPower.oneEquiv _ (F.val.obj U)).toModuleIso)
    (fun U V i => by
      ext x
      exact exteriorPower_oneEquiv_exteriorPowerMap _ (F.val.restrictₛₗ i) x)

/-- **The degree-one exterior power.** `⋀^1 F ≅ F`. -/
noncomputable def moduleSheafExteriorPowerOneIso : moduleSheafExteriorPower 1 F ≅ F :=
  (PresheafOfModules.sheafification (𝟙 (siteRingCatSheaf R).obj)).mapIso
      (exteriorPowerPresheafOneIso F) ≪≫
    asIso ((PresheafOfModules.sheafificationAdjunction (𝟙 (siteRingCatSheaf R).obj)).counit.app F)

end DegreeOneSheaf

namespace ExteriorPerfectPairing

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

open Ringed

/-- **Hartshorne II, Exercise 5.16(b), rank two.** A locally free sheaf `F` of rank `2` is
isomorphic to its dual twisted by its determinant: `F ≅ F^∨ ⊗ ⋀^2 F`. It is the case `r = s = 1`,
`n = 2` of the perfect exterior-power pairing, together with `⋀^1 F ≅ F`. -/
noncomputable def rankTwoDualTensorIso {F : SheafOfModules.{u} (ringCatSheafOf R)}
    (hF : IsLocallyFreeOfRank F 2) :
    F ≅ moduleSheafTensor (moduleSheafDual F) (moduleSheafExteriorPower 2 F) :=
  (moduleSheafExteriorPowerOneIso F).symm ≪≫ exteriorPowerDualTensorIso F 1 1 rfl hF ≪≫
    moduleSheafTensorIsoOfIso (moduleSheafDualIsoOfIso (moduleSheafExteriorPowerOneIso F))
      (Iso.refl _)

end ExteriorPerfectPairing

end Hartshorne

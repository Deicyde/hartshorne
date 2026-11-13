/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.KoszulRegularImmersionTopExtConormalFrame
import Hartshorne.Scheme.RankTwoDualDeterminant
import Hartshorne.RingedSpace.SheafExtStructureSheaf

/-!
# The top sheaf Ext of a Koszul-regular immersion in every codimension

For a Koszul-regular closed immersion `i : X ⟶ Y` of codimension `r` with ideal sheaf `I` and a
quasi-coherent `𝒪_Y`-module `M`, `Hartshorne.KoszulTarget.sheafExtIsoDualTensor` is an isomorphism
`ℰxt^r_Y(i_* 𝒪_X, M) ≅ i_*((⋀^r(i^* I))^∨ ⊗ i^* M)`, with `i^* I` the conormal sheaf `I/I²` on
`X`. For `r ≥ 1` it is `sheafExtTopIsoDualTensor` (gluing of the local Koszul calculations). For
`r = 0` the ideal sheaf vanishes, so `i` is an isomorphism
(`Hartshorne.IsKoszulRegularImmersion.isIso_of_zero`), and the isomorphism
(`sheafExtZeroIsoDualTensor`) is
`ℰxt⁰(i_* 𝒪_X, M) ≅ ℋom(i_* 𝒪_X, M) ≅ ℋom(𝒪_Y, M) ≅ M ≅ i_* i^* M ≅ i_* ℋom(⋀⁰(i^* I), i^* M)`,
using `⋀⁰ F ≅ 𝒪` (`moduleSheafExteriorPowerZeroIso`) and that pushforward along an isomorphism is
an equivalence (`pushforwardEquivOfIsIso`).
-/

universe u

open CategoryTheory Opposite TopologicalSpace Limits

set_option backward.isDefEq.respectTransparency false

namespace Hartshorne

open AlgebraicGeometry

/-- A Koszul-regular immersion of codimension `0` is an isomorphism: its ideal sheaf vanishes. -/
theorem IsKoszulRegularImmersion.isIso_of_zero {X Y : Scheme.{u}} {i : X ⟶ Y}
    (h : IsKoszulRegularImmersion i 0) : IsIso i := by
  have := h.isClosedImmersion
  rw [IsClosedImmersion.isIso_iff_ker_eq_bot]
  choose U hyU f hI _ using h.exists_isKoszulRegular
  refine le_bot_iff.mp (Scheme.IdealSheafData.le_of_iSup_eq_top U
    (eq_top_iff.mpr fun y _ => Opens.mem_iSup.mpr ⟨y, hyU y⟩) fun y => ?_)
  rw [hI y, Set.range_eq_empty, Ideal.span_empty]
  exact bot_le

section ExteriorZero

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{u}}
  (F : SheafOfModules.{u} (siteRingCatSheaf R))

open SheafTensorOperations

/-- The identification `⋀⁰ M ≅ A` is compatible with semilinear maps. -/
lemma exteriorPower_zeroEquiv_exteriorPowerMap {A B : Type u} [CommRing A] [CommRing B]
    {σ : A →+* B} {M N : Type u} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]
    (f : M →ₛₗ[σ] N) (x : ⋀[A]^0 M) :
    exteriorPower.zeroEquiv B N (exteriorPowerMap 0 σ f x) = σ (exteriorPower.zeroEquiv A M x) := by
  obtain ⟨a, rfl⟩ : ∃ a : A, a • exteriorPower.ιMulti A 0 (Fin.elim0 : Fin 0 → M) = x := by
    refine ⟨exteriorPower.zeroEquiv A M x, (exteriorPower.zeroEquiv A M).injective ?_⟩
    rw [map_smul, exteriorPower.zeroEquiv_ιMulti, smul_eq_mul, mul_one]
  rw [map_smulₛₗ, exteriorPowerMap_ιMulti, map_smul, map_smul, exteriorPower.zeroEquiv_ιMulti,
    exteriorPower.zeroEquiv_ιMulti, smul_eq_mul, smul_eq_mul, mul_one, mul_one]

/-- The presheaf `U ↦ ⋀^0 F(U)` is the structure presheaf. -/
noncomputable def exteriorPowerPresheafZeroIso :
    moduleSheafExteriorPowerPresheaf 0 F ≅
      (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 _)).obj
        (SheafOfModules.unit (siteRingCatSheaf R)) :=
  PresheafOfModules.isoMk (fun U => (exteriorPower.zeroEquiv _ (F.val.obj U)).toModuleIso)
    (fun U V i => by
      ext x
      exact exteriorPower_zeroEquiv_exteriorPowerMap (F.val.restrictₛₗ i) x)

/-- **The degree-zero exterior power.** `⋀^0 F ≅ 𝒪`. -/
noncomputable def moduleSheafExteriorPowerZeroIso :
    moduleSheafExteriorPower 0 F ≅ SheafOfModules.unit (siteRingCatSheaf R) :=
  (PresheafOfModules.sheafification (𝟙 (siteRingCatSheaf R).obj)).mapIso
      (exteriorPowerPresheafZeroIso F) ≪≫
    asIso ((PresheafOfModules.sheafificationAdjunction (𝟙 (siteRingCatSheaf R).obj)).counit.app
      (SheafOfModules.unit (siteRingCatSheaf R)))

end ExteriorZero

namespace KoszulTarget

open KoszulImmersion Ringed

section IsoCase

variable {X Y : Scheme.{u}} (i : X ⟶ Y) [IsIso i]

/-- Pushforward along an isomorphism of schemes is an equivalence. -/
noncomputable def pushforwardEquivOfIsIso : X.Modules ≌ Y.Modules :=
  CategoryTheory.Equivalence.mk (Scheme.Modules.pushforward i)
    (Scheme.Modules.pushforward (inv i))
    ((Scheme.Modules.pushforwardId X).symm ≪≫
      (Scheme.Modules.pushforwardCongr (IsIso.hom_inv_id i)).symm ≪≫
      (Scheme.Modules.pushforwardComp i (inv i)).symm)
    (Scheme.Modules.pushforwardComp (inv i) i ≪≫
      Scheme.Modules.pushforwardCongr (IsIso.inv_hom_id i) ≪≫ Scheme.Modules.pushforwardId Y)

/-- For an isomorphism `i`, the unit `M ⟶ i_* i^* M` is an isomorphism. -/
instance isIso_pullbackPushforwardAdjunction_unit :
    IsIso (Scheme.Modules.pullbackPushforwardAdjunction i).unit := by
  have : (Scheme.Modules.pushforward i).IsEquivalence :=
    (pushforwardEquivOfIsIso i).isEquivalence_functor
  have := (Scheme.Modules.pullbackPushforwardAdjunction i).isEquivalence_left_of_isEquivalence_right
  infer_instance

/-- The map `𝒪_Y ⟶ i_* 𝒪_X` is an isomorphism for an isomorphism `i`. -/
instance isIso_structureSheafToPushforward : IsIso (structureSheafToPushforward i) :=
  ModuleGluing.isIso_of_bijective _ fun A =>
    ConcreteCategory.bijective_of_isIso (i.app A.unop)

end IsoCase

variable {X Y : Scheme.{u}} {i : X ⟶ Y}

/-- **The sheaf Ext of a Koszul-regular immersion in codimension `0`.** Then `i` is an
isomorphism, and `ℰxt⁰_Y(i_* 𝒪_X, M) = ℋom(i_* 𝒪_X, M) ≅ M ≅ i_*((⋀⁰(i^* I))^∨ ⊗ i^* M)`. -/
noncomputable def sheafExtZeroIsoDualTensor (h : IsKoszulRegularImmersion i 0) (M : Y.Modules) :
    (Ringed.sheafExt (R := Y.sheaf) ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit X.ringCatSheaf)) 0).obj M ≅
        (Scheme.Modules.pushforward i).obj (moduleSheafTensor (R := X.sheaf)
          (moduleSheafDual (R := X.sheaf) (moduleSheafExteriorPower (R := X.sheaf) 0
            ((Scheme.Modules.pullback i).obj (closedImmersionIdealSheaf i))))
          ((Scheme.Modules.pullback i).obj M)) :=
  haveI := h.isIso_of_zero
  (moduleSheafHomFunctor (R := Y.sheaf) ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit X.ringCatSheaf))).rightDerivedZeroIsoSelf.app M ≪≫
    ((moduleSheafHomBifunctor (R := Y.sheaf)).mapIso
      (asIso (structureSheafToPushforward i)).op).app M ≪≫
    (moduleSheafHomStructureModuleIso (R := Y.sheaf)).app M ≪≫
    @asIso _ _ _ _ ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M)
      (@NatIso.isIso_app_of_isIso _ _ _ _ _ _ _ (isIso_pullbackPushforwardAdjunction_unit i) M) ≪≫
    (Scheme.Modules.pushforward i).mapIso
      ((moduleSheafHomStructureModuleIso (R := X.sheaf)).app _).symm ≪≫
    (Scheme.Modules.pushforward i).mapIso (((moduleSheafHomBifunctor (R := X.sheaf)).mapIso
      (moduleSheafExteriorPowerZeroIso (R := X.sheaf)
        ((Scheme.Modules.pullback i).obj (closedImmersionIdealSheaf i))).op).app _) ≪≫
    (Scheme.Modules.pushforward i).mapIso (moduleSheafDualTensorIso (R := X.sheaf) _ _
      (isFiniteLocallyFree_of_iso (moduleSheafExteriorPowerZeroIso (R := X.sheaf) _).symm
        (structureModule_isInvertible (R := X.sheaf)).isFiniteLocallyFree)).symm

/-- **The top sheaf Ext of a Koszul-regular immersion.** For a Koszul-regular closed immersion
`i : X ⟶ Y` of codimension `r` with ideal sheaf `I` and a quasi-coherent `𝒪_Y`-module `M`,
`ℰxt^r_Y(i_* 𝒪_X, M) ≅ i_*((⋀^r(i^* I))^∨ ⊗ i^* M)`, where `i^* I` is the conormal sheaf `I/I²`
on `X` (`sheafExtTopIsoDualTensor` for `r ≥ 1`, `sheafExtZeroIsoDualTensor` for `r = 0`). -/
noncomputable def sheafExtIsoDualTensor : ∀ {r : ℕ} (_ : IsKoszulRegularImmersion i r)
    (M : Y.Modules) [M.IsQuasicoherent],
    (Ringed.sheafExt (R := Y.sheaf) ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit X.ringCatSheaf)) r).obj M ≅
        (Scheme.Modules.pushforward i).obj (moduleSheafTensor (R := X.sheaf)
          (moduleSheafDual (R := X.sheaf) (moduleSheafExteriorPower (R := X.sheaf) r
            ((Scheme.Modules.pullback i).obj (closedImmersionIdealSheaf i))))
          ((Scheme.Modules.pullback i).obj M))
  | 0, h, M, _ => sheafExtZeroIsoDualTensor h M
  | _ + 1, h, M, _ => sheafExtTopIsoDualTensor h M

end KoszulTarget

end Hartshorne

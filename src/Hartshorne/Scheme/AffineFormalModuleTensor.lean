/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.FormalCompletionModule
import Hartshorne.Scheme.FormalCompletionModuleAffineSections
import Hartshorne.Scheme.AffineFormalModuleExact
import Hartshorne.Scheme.ClosedImmersionIdealSheaf
import Hartshorne.Scheme.FormalCompletionAffineSections
import Hartshorne.Scheme.FormalSpectrum
import Hartshorne.Scheme.ModuleSheafTensor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Sites.Pullback

/-!
# Completed modules and the ordinary tensor product (infrastructure)

Hartshorne, *Algebraic Geometry*, II.9, Proposition 9.4(b) (pp. 195–196): for a Noetherian ring
`A`, an ideal `I` and a finite `A`-module `M`, the completion of `M~` on `X̂ = Spf_I(A)` is
`M~|_{V(I)} ⊗_{𝒪_{Spec A}|_{V(I)}} 𝒪_X̂`, an ordinary tensor product of sheaves of modules.

This file builds the objects in that statement, for any scheme `X`, quasi-coherent ideal subsheaf
`I` cutting out `Y`, and `𝒪_X`-module `F`, with `i : |Y| ⟶ X` the inclusion of the support:

* `Hartshorne.QuasicoherentIdealSubsheaf.restrictedStructureSheaf I`: the sheaf of rings
  `𝒪_X|_{|Y|} = i⁻¹ 𝒪_X` on `|Y|` (the topological inverse image).
* `Hartshorne.QuasicoherentIdealSubsheaf.restrictedStructureSheafUnit I`: the adjunction unit
  `𝒪_X ⟶ i_* i⁻¹ 𝒪_X`.
* `Hartshorne.QuasicoherentIdealSubsheaf.structureSheafToFormalCompletion I`: the canonical map
  `𝒪_X ⟶ i_* 𝒪_X̂` (on sections, `formalCompletionSectionsMap`).
* `Hartshorne.QuasicoherentIdealSubsheaf.restrictedStructureSheafToFormalCompletion I`: its
  adjoint `𝒪_X|_{|Y|} ⟶ 𝒪_X̂`, a map of sheaves of rings on `|Y|`.
* `Hartshorne.QuasicoherentIdealSubsheaf.restrictedModule I F`: `F|_{|Y|} = i⁻¹ F` as an
  `𝒪_X|_{|Y|}`-module, the module inverse image along `𝒪_X ⟶ i_* i⁻¹ 𝒪_X`.
* `Hartshorne.QuasicoherentIdealSubsheaf.formalCompletionRestrictedModule I`: `𝒪_X̂` as an
  `𝒪_X|_{|Y|}`-module.
* `Hartshorne.QuasicoherentIdealSubsheaf.restrictedModuleTensorFormalCompletion I F`: the ordinary
  tensor product `F|_{|Y|} ⊗_{𝒪_X|_{|Y|}} 𝒪_X̂` of sheaves of `𝒪_X|_{|Y|}`-modules.
* `Hartshorne.QuasicoherentIdealSubsheaf.moduleCompletionRestrictedModule I F`: the completion
  `F̂` viewed as an `𝒪_X|_{|Y|}`-module.

The comparison map between the last two and Proposition 9.4(b) itself are not yet formalized; see
the implementation note of the article. The private helpers at the end prepare the comparison map
`F ⟶ i_* F̂`: its components `F ⟶ i_* (F / I ^ (n + 1) F)|_Y` (the quotient map, the unit of
the pullback–pushforward adjunction along `Y_(n+1) ⟶ X`, and restriction of sections along
equal opens), the adjunction identity relating the units along `Y_(n+1) ⟶ Y_(n+2) ⟶ X` and
`Y_(n+1) ⟶ X`, and the section-level identities relating these restrictions to the transition
maps of the completion.
-/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Topology Opposite TopologicalSpace

namespace Hartshorne

universe u

namespace QuasicoherentIdealSubsheaf

variable {X : Scheme.{u}} (I : QuasicoherentIdealSubsheaf X)

/-- **`𝒪_X|_{|Y|}`**: the topological inverse image `i⁻¹ 𝒪_X` of the structure sheaf along the
inclusion `i : |Y| ⟶ X` of the support of the closed subscheme cut out by `I`, a sheaf of
commutative rings on `|Y|`. -/
def restrictedStructureSheaf : TopCat.Sheaf CommRingCat.{u} (I.infinitesimalNeighborhood 1) :=
  ((Opens.map (I.infinitesimalNeighborhoodι 1).base).sheafPullback CommRingCat.{u}
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology (I.infinitesimalNeighborhood 1))).obj
      X.sheaf

/-- The adjunction `i⁻¹ ⊣ i_*` for sheaves of commutative rings along `i : |Y| ⟶ X`. -/
private abbrev restrictedStructureSheafAdj :=
  (Opens.map (I.infinitesimalNeighborhoodι 1).base).sheafAdjunctionContinuous CommRingCat.{u}
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology (I.infinitesimalNeighborhood 1))

/-- The adjunction unit `𝒪_X ⟶ i_* i⁻¹ 𝒪_X`. -/
def restrictedStructureSheafUnit :
    X.sheaf ⟶ ((Opens.map (I.infinitesimalNeighborhoodι 1).base).sheafPushforwardContinuous
      CommRingCat.{u} _ _).obj I.restrictedStructureSheaf :=
  I.restrictedStructureSheafAdj.unit.app X.sheaf

/-- **The canonical map `𝒪_X ⟶ i_* 𝒪_X̂`**: on an open `U` of `X`, the map
`Γ(U, 𝒪_X) ⟶ Γ(U ∩ |Y|, 𝒪_X̂)` induced by restriction to the thickenings `Y_(n+1)`. -/
def structureSheafToFormalCompletion :
    X.sheaf ⟶ ((Opens.map (I.infinitesimalNeighborhoodι 1).base).sheafPushforwardContinuous
      CommRingCat.{u} _ _).obj I.formalCompletionSheaf where
  hom :=
    { app U := I.formalCompletionSectionsMap U.unop
      naturality _ _ f := (I.formalCompletionSectionsMap_naturality (leOfHom f.unop)).symm }

/-- **The ring map `𝒪_X|_{|Y|} ⟶ 𝒪_X̂`**, adjoint to `𝒪_X ⟶ i_* 𝒪_X̂`. -/
def restrictedStructureSheafToFormalCompletion :
    I.restrictedStructureSheaf ⟶ I.formalCompletionSheaf :=
  (I.restrictedStructureSheafAdj.homEquiv _ _).symm I.structureSheafToFormalCompletion

/-- The map `𝒪_X ⟶ i_* 𝒪_X̂` factors as the unit `𝒪_X ⟶ i_* i⁻¹ 𝒪_X` followed by the pushforward
of `𝒪_X|_{|Y|} ⟶ 𝒪_X̂`. -/
lemma restrictedStructureSheafUnit_comp_toFormalCompletion :
    I.restrictedStructureSheafUnit ≫
        ((Opens.map (I.infinitesimalNeighborhoodι 1).base).sheafPushforwardContinuous
          CommRingCat.{u} _ _).map I.restrictedStructureSheafToFormalCompletion =
      I.structureSheafToFormalCompletion := by
  exact (I.restrictedStructureSheafAdj.homEquiv_unit _ _ _).symm.trans
    (Equiv.apply_symm_apply _ _)

/-- The unit `𝒪_X ⟶ i_* i⁻¹ 𝒪_X` as a map of sheaves of rings in `RingCat`. -/
def restrictedStructureSheafUnitRingCat :
    X.ringCatSheaf ⟶ ((Opens.map (I.infinitesimalNeighborhoodι 1).base).sheafPushforwardContinuous
      RingCat.{u} _ _).obj (ringCatSheafOf I.restrictedStructureSheaf) where
  hom := Functor.whiskerRight I.restrictedStructureSheafUnit.hom (forget₂ CommRingCat RingCat.{u})

instance : (PresheafOfModules.pushforward.{u}
    I.restrictedStructureSheafUnitRingCat.hom).IsRightAdjoint :=
  Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
    (PresheafOfModules.pullbackObjIsDefined_eq_top _)

instance : (SheafOfModules.pushforward.{u} I.restrictedStructureSheafUnitRingCat).IsRightAdjoint :=
  (SheafOfModules.PullbackConstruction.adjunction.{u} _).isRightAdjoint

/-- `𝒪_X ⟶ i_* 𝒪_X̂` as a map of sheaves of rings in `RingCat`. -/
def structureSheafToFormalCompletionRingCat :
    X.ringCatSheaf ⟶ ((Opens.map (I.infinitesimalNeighborhoodι 1).base).sheafPushforwardContinuous
      RingCat.{u} _ _).obj I.formalCompletionRingCatSheaf where
  hom := Functor.whiskerRight I.structureSheafToFormalCompletion.hom
    (forget₂ CommRingCat RingCat.{u})

instance : (PresheafOfModules.pushforward.{u}
    I.structureSheafToFormalCompletionRingCat.hom).IsRightAdjoint :=
  Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
    (PresheafOfModules.pullbackObjIsDefined_eq_top _)

instance : (SheafOfModules.pushforward.{u}
    I.structureSheafToFormalCompletionRingCat).IsRightAdjoint :=
  (SheafOfModules.PullbackConstruction.adjunction.{u} _).isRightAdjoint

/-- `𝒪_X|_{|Y|} ⟶ 𝒪_X̂` as a map of sheaves of rings in `RingCat`. -/
def restrictedStructureSheafToFormalCompletionRingCat :
    ringCatSheafOf I.restrictedStructureSheaf ⟶ I.formalCompletionRingCatSheaf where
  hom := Functor.whiskerRight I.restrictedStructureSheafToFormalCompletion.hom
    (forget₂ CommRingCat RingCat.{u})

variable (F : X.Modules)

/-- **`F|_{|Y|}`**: the restriction `i⁻¹ F` of an `𝒪_X`-module to the support `|Y|`, as a module
over `𝒪_X|_{|Y|} = i⁻¹ 𝒪_X`; it is the module inverse image along the unit
`𝒪_X ⟶ i_* i⁻¹ 𝒪_X`, the left adjoint of the pushforward `i_*`. -/
def restrictedModule : SheafOfModules.{u} (ringCatSheafOf I.restrictedStructureSheaf) :=
  (SheafOfModules.pullback.{u} I.restrictedStructureSheafUnitRingCat).obj F

/-- **`𝒪_X̂` as an `𝒪_X|_{|Y|}`-module**, through the ring map `𝒪_X|_{|Y|} ⟶ 𝒪_X̂`. -/
def formalCompletionRestrictedModule :
    SheafOfModules.{u} (ringCatSheafOf I.restrictedStructureSheaf) :=
  (SheafOfModules.restrictScalars.{u} I.restrictedStructureSheafToFormalCompletionRingCat).obj
    (SheafOfModules.unit _)

/-- **The ordinary tensor product `F|_{|Y|} ⊗_{𝒪_X|_{|Y|}} 𝒪_X̂`** of sheaves of
`𝒪_X|_{|Y|}`-modules on `|Y|` (Hartshorne II.9, Proposition 9.4(b), right-hand side). No
completed tensor product is involved. -/
def restrictedModuleTensorFormalCompletion :
    SheafOfModules.{u} (ringCatSheafOf I.restrictedStructureSheaf) :=
  moduleSheafTensor (I.restrictedModule F) I.formalCompletionRestrictedModule

/-- **The completion `F̂` as an `𝒪_X|_{|Y|}`-module**, through `𝒪_X|_{|Y|} ⟶ 𝒪_X̂`. -/
def moduleCompletionRestrictedModule :
    SheafOfModules.{u} (ringCatSheafOf I.restrictedStructureSheaf) :=
  (SheafOfModules.restrictScalars.{u} I.restrictedStructureSheafToFormalCompletionRingCat).obj
    (I.moduleCompletion F)


/-- The map `𝒪_X ⟶ i_* 𝒪_X̂` is compatible with the projections `𝒪_X̂ ⟶ 𝒪_{Y_(n+1)}` and the
restrictions `𝒪_X ⟶ 𝒪_{Y_(n+1)}`, on sections over `U ∩ |Y|`. -/
lemma structureSheafToFormalCompletionRingCat_compat (n : ℕ) (V : X.Opensᵒᵖ)
    (r : X.ringCatSheaf.obj.obj V) :
    (I.infinitesimalNeighborhood (n + 1)).ringCatSheaf.obj.map
        ((I.functorToPreimageInfinitesimalNeighborhoodι n).app V.unop).op
        ((I.infinitesimalNeighborhoodι (n + 1)).toRingCatSheafHom.hom.app V r) =
      (I.formalCompletionRingCatSheafπ n).hom.app
        (op ((Opens.map (I.infinitesimalNeighborhoodι 1).base).obj V.unop))
        (I.structureSheafToFormalCompletionRingCat.hom.app V r) :=
  (congrArg (fun g => g.hom r) (I.formalCompletionSectionsMap_π V.unop n)).symm

/-- The cone `F ⟶ i_* (F / I ^ (n + 1) F)|_Y` over the pushforward to `X` of the inverse system
defining the completion `F̂`, with the canonical maps as components. -/
def moduleCompletionPushforwardCone :
    Cone (I.moduleCompletionDiagram F ⋙
      SheafOfModules.pushforward.{u} I.structureSheafToFormalCompletionRingCat) where
  pt := F
  π := NatTrans.ofOpSequence
    (fun n => I.moduleCompletionLevelMap I.structureSheafToFormalCompletionRingCat
      I.structureSheafToFormalCompletionRingCat_compat F n)
    (fun n => (Category.id_comp _).trans
      ((I.moduleCompletionLevelMap_comp_moduleCompletionMap _ _ F n).symm.trans
        (congrArg (fun g => _ ≫ (SheafOfModules.pushforward.{u}
          I.structureSheafToFormalCompletionRingCat).map g)
          (Functor.ofOpSequence_map_homOfLE_succ (I.moduleCompletionMap F) n).symm)))

/-- **The canonical map `F ⟶ i_* F̂`** of `𝒪_X`-modules, for `i : |Y| ⟶ X` and the structure of
`i_* F̂` as an `𝒪_X`-module through `𝒪_X ⟶ i_* 𝒪_X̂`: the map into the inverse limit induced by
the canonical maps `F ⟶ i_* (F / I ^ (n + 1) F)|_Y`. -/
def toModuleCompletionPushforward :
    F ⟶ (SheafOfModules.pushforward.{u} I.structureSheafToFormalCompletionRingCat).obj
      (I.moduleCompletion F) :=
  (isLimitOfPreserves (SheafOfModules.pushforward.{u} I.structureSheafToFormalCompletionRingCat)
    (limit.isLimit (I.moduleCompletionDiagram F))).lift (I.moduleCompletionPushforwardCone F)

/-- The canonical map `F ⟶ i_* F̂` followed by the projection to `i_* (F / I ^ (n + 1) F)|_Y` is
the canonical map at level `n`. -/
@[reassoc]
lemma toModuleCompletionPushforward_π (n : ℕ) :
    I.toModuleCompletionPushforward F ≫
        (SheafOfModules.pushforward.{u} I.structureSheafToFormalCompletionRingCat).map
          (I.moduleCompletionπ F n) =
      I.moduleCompletionLevelMap I.structureSheafToFormalCompletionRingCat
        I.structureSheafToFormalCompletionRingCat_compat F n :=
  (isLimitOfPreserves (SheafOfModules.pushforward.{u} I.structureSheafToFormalCompletionRingCat)
    (limit.isLimit (I.moduleCompletionDiagram F))).fac (I.moduleCompletionPushforwardCone F) (op n)

/-- Maps into `i_* F̂` agree once their projections to all `i_* (F / I ^ (n + 1) F)|_Y` agree. -/
lemma pushforward_moduleCompletion_hom_ext {G : X.Modules}
    {f g : G ⟶ (SheafOfModules.pushforward.{u} I.structureSheafToFormalCompletionRingCat).obj
      (I.moduleCompletion F)}
    (h : ∀ n, f ≫ (SheafOfModules.pushforward.{u} I.structureSheafToFormalCompletionRingCat).map
        (I.moduleCompletionπ F n) =
      g ≫ (SheafOfModules.pushforward.{u} I.structureSheafToFormalCompletionRingCat).map
        (I.moduleCompletionπ F n)) :
    f = g :=
  (isLimitOfPreserves (SheafOfModules.pushforward.{u} I.structureSheafToFormalCompletionRingCat)
    (limit.isLimit (I.moduleCompletionDiagram F))).hom_ext (fun ⟨n⟩ => h n)

/-- **Naturality of `F ⟶ i_* F̂`** in `F`. -/
@[reassoc]
lemma toModuleCompletionPushforward_naturality {F G : X.Modules} (φ : F ⟶ G) :
    φ ≫ I.toModuleCompletionPushforward G =
      I.toModuleCompletionPushforward F ≫
        (SheafOfModules.pushforward.{u} I.structureSheafToFormalCompletionRingCat).map
          (I.moduleCompletionHom φ) := by
  refine I.pushforward_moduleCompletion_hom_ext G (fun n => ?_)
  have e := I.moduleCompletionLevelMap_naturality _
    I.structureSheafToFormalCompletionRingCat_compat φ n
  rw [← I.toModuleCompletionPushforward_π F n, ← I.toModuleCompletionPushforward_π G n] at e
  have hP := ((SheafOfModules.pushforward.{u} I.structureSheafToFormalCompletionRingCat).map_comp
      _ _).symm.trans ((congrArg (SheafOfModules.pushforward.{u}
        I.structureSheafToFormalCompletionRingCat).map (I.moduleCompletionHom_π φ n).symm).trans
      ((SheafOfModules.pushforward.{u} I.structureSheafToFormalCompletionRingCat).map_comp _ _))
  exact (Category.assoc _ _ _).trans (e.symm.trans ((Category.assoc _ _ _).trans
    ((whisker_eq _ hP).trans (Category.assoc _ _ _).symm)))

/-- **The canonical map `f^* F ⟶ F̂`** of `𝒪_X̂`-modules, for the morphism of ringed spaces
`f : (|Y|, 𝒪_X̂) ⟶ (X, 𝒪_X)` given by `i : |Y| ⟶ X` and `𝒪_X ⟶ i_* 𝒪_X̂`. Here
`f^* F = i⁻¹ F ⊗_{i⁻¹ 𝒪_X} 𝒪_X̂` is the module pullback; the map is adjoint to `F ⟶ i_* F̂`. -/
def pullbackToModuleCompletion :
    (SheafOfModules.pullback.{u} I.structureSheafToFormalCompletionRingCat).obj F ⟶
      I.moduleCompletion F :=
  ((SheafOfModules.pullbackPushforwardAdjunction.{u}
    I.structureSheafToFormalCompletionRingCat).homEquiv _ _).symm
      (I.toModuleCompletionPushforward F)

/-- **Naturality of `f^* F ⟶ F̂`** in `F`. -/
@[reassoc]
lemma pullbackToModuleCompletion_naturality {F G : X.Modules} (φ : F ⟶ G) :
    (SheafOfModules.pullback.{u} I.structureSheafToFormalCompletionRingCat).map φ ≫
        I.pullbackToModuleCompletion G =
      I.pullbackToModuleCompletion F ≫ I.moduleCompletionHom φ := by
  unfold pullbackToModuleCompletion
  exact (((SheafOfModules.pullbackPushforwardAdjunction.{u}
    I.structureSheafToFormalCompletionRingCat).homEquiv_naturality_left_symm φ _).symm.trans
      (congrArg _ (I.toModuleCompletionPushforward_naturality φ))).trans
    ((SheafOfModules.pullbackPushforwardAdjunction.{u}
      I.structureSheafToFormalCompletionRingCat).homEquiv_naturality_right_symm _ _)


section RankOne

/-- The functor `U ↦ U ∩ |Y|` on opens is final: `⊤` is terminal in each comma category. -/
private instance final_opensMap_infinitesimalNeighborhoodι :
    (Opens.map (I.infinitesimalNeighborhoodι 1).base).Final := by
  constructor
  intro U
  refine isConnected_of_isTerminal _ (x := StructuredArrow.mk
    (homOfLE le_top : U ⟶ (Opens.map (I.infinitesimalNeighborhoodι 1).base).obj ⊤)) ?_
  refine IsTerminal.ofUniqueHom
    (fun A ↦ StructuredArrow.homMk (homOfLE le_top) (Subsingleton.elim _ _)) ?_
  intro A m
  ext
  exact Subsingleton.elim _ _

private instance isIso_pullbackObjUnitToUnit :
    IsIso (SheafOfModules.pullbackObjUnitToUnit.{u} I.structureSheafToFormalCompletionRingCat) :=
  @SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal _ _ _ _ _ _ _ _ _ _ _ _
    (final_opensMap_infinitesimalNeighborhoodι I)

/-- The map `𝒪_X̂ ⟶ (𝒪_X)^` of `𝒪_X̂`-modules, `f^* 𝒪_X ⟶ (𝒪_X)^` composed with `𝒪_X̂ ≅ f^* 𝒪_X`. -/
private def unitToModuleCompletionUnit :
    SheafOfModules.unit.{u} I.formalCompletionRingCatSheaf ⟶
      I.moduleCompletion (SheafOfModules.unit.{u} X.ringCatSheaf) :=
  inv (SheafOfModules.pullbackObjUnitToUnit.{u} I.structureSheafToFormalCompletionRingCat) ≫
    I.pullbackToModuleCompletion (SheafOfModules.unit.{u} X.ringCatSheaf)

private lemma pullbackObjUnitToUnit_comp_unitToModuleCompletionUnit :
    SheafOfModules.pullbackObjUnitToUnit.{u} I.structureSheafToFormalCompletionRingCat ≫
      I.unitToModuleCompletionUnit = I.pullbackToModuleCompletion _ :=
  IsIso.hom_inv_id_assoc
    (SheafOfModules.pullbackObjUnitToUnit.{u} I.structureSheafToFormalCompletionRingCat) _

private lemma unitToPushforwardObjUnit_comp_unitToModuleCompletionUnit :
    SheafOfModules.unitToPushforwardObjUnit.{u} I.structureSheafToFormalCompletionRingCat ≫
      (SheafOfModules.pushforward.{u} I.structureSheafToFormalCompletionRingCat).map
        I.unitToModuleCompletionUnit =
      I.toModuleCompletionPushforward (SheafOfModules.unit.{u} X.ringCatSheaf) := by
  apply ((SheafOfModules.pullbackPushforwardAdjunction.{u}
    I.structureSheafToFormalCompletionRingCat).homEquiv _ _).symm.injective
  exact ((SheafOfModules.pullbackPushforwardAdjunction.{u}
    I.structureSheafToFormalCompletionRingCat).homEquiv_naturality_right_symm _ _).trans
    I.pullbackObjUnitToUnit_comp_unitToModuleCompletionUnit

private lemma unitToModuleCompletionUnit_app_χ (U : X.Opens) (a : Γ(X, U)) :
    I.unitToModuleCompletionUnit.val.app (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ U))
        (I.structureSheafToFormalCompletionRingCat.hom.app (op U) a) =
      (I.toModuleCompletionPushforward _).val.app (op U) a :=
  congrArg (fun f => f.val.app (op U) a) I.unitToPushforwardObjUnit_comp_unitToModuleCompletionUnit

/-- On sections over `U ∩ |Y|`, the map `𝒪_X̂ ⟶ (𝒪_X)^` followed by the projection to level `n` is
multiplication by the canonical image of `1` at level `n`. -/
private lemma unitToModuleCompletionUnit_π (n : ℕ) (U : X.Opens)
    (x : I.formalCompletionRingCatSheaf.obj.obj (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ U))) :
    (I.moduleCompletionπ _ n).val.app _ (I.unitToModuleCompletionUnit.val.app _ x) =
      x • (show (I.moduleCompletionObj (SheafOfModules.unit.{u} X.ringCatSheaf) n).val.obj
          (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ U)) from
        (I.moduleCompletionLevelMap I.structureSheafToFormalCompletionRingCat
          I.structureSheafToFormalCompletionRingCat_compat _ n).val.app (op U)
          (1 : Γ(X, U))) := by
  let one : (SheafOfModules.unit.{u} I.formalCompletionRingCatSheaf).val.obj
      (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ U)) :=
    (1 : I.formalCompletionRingCatSheaf.obj.obj (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ U)))
  have h1 : I.unitToModuleCompletionUnit.val.app (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ U)) x =
      x • I.unitToModuleCompletionUnit.val.app (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ U)) one :=
    (congrArg _ (mul_one x).symm).trans
      (map_smul (I.unitToModuleCompletionUnit.val.app _).hom x one)
  have h2 : I.unitToModuleCompletionUnit.val.app (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ U)) one =
      (I.toModuleCompletionPushforward _).val.app (op U) (1 : Γ(X, U)) :=
    (congrArg (I.unitToModuleCompletionUnit.val.app _)
      (map_one (I.structureSheafToFormalCompletionRingCat.hom.app (op U)).hom).symm).trans
      (I.unitToModuleCompletionUnit_app_χ U 1)
  have h3 := congrArg (fun f => f.val.app (op U) (1 : Γ(X, U)))
    (I.toModuleCompletionPushforward_π (SheafOfModules.unit.{u} X.ringCatSheaf) n)
  refine (congrArg ((I.moduleCompletionπ _ n).val.app _) h1).trans ?_
  refine (map_smul ((I.moduleCompletionπ _ n).val.app _).hom x _).trans ?_
  exact congrArg (x • ·) ((congrArg ((I.moduleCompletionπ _ n).val.app _) h2).trans h3)

/-- Scalars acting on a pushforward act through the ring map. -/
private lemma pushforward_smul_congr {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {G : C ⥤ D} [G.IsContinuous J K]
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (φ : R ⟶ (G.sheafPushforwardContinuous RingCat.{u} J K).obj S) (M : SheafOfModules.{u} S)
    (V : Cᵒᵖ) {r r' : R.obj.obj V} (h : φ.hom.app V r = φ.hom.app V r')
    (m : ((SheafOfModules.pushforward.{u} φ).obj M).val.obj V) : r • m = r' • m :=
  congrArg (fun (a : S.obj.obj (op (G.obj V.unop))) =>
    (a • (show M.val.obj (op (G.obj V.unop)) from m) : M.val.obj (op (G.obj V.unop)))) h

/-- Scalars acting on a pushforward act through the ring map. -/
private lemma pushforward_smul_eq {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {G : C ⥤ D} [G.IsContinuous J K]
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (φ : R ⟶ (G.sheafPushforwardContinuous RingCat.{u} J K).obj S) (M : SheafOfModules.{u} S)
    (V : Cᵒᵖ) (r : R.obj.obj V) (m : ((SheafOfModules.pushforward.{u} φ).obj M).val.obj V) :
    (r • m : ((SheafOfModules.pushforward.{u} φ).obj M).val.obj V) =
      ((show S.obj.obj (op (G.obj V.unop)) from φ.hom.app V r) •
        (show M.val.obj (op (G.obj V.unop)) from m) : M.val.obj (op (G.obj V.unop))) :=
  rfl

/-- The canonical map at level `n` on a function `a`, as `a` times the image of `1`. -/
private lemma moduleCompletionLevelMap_unit_apply (n : ℕ) (U : X.Opens) (a : Γ(X, U)) :
    (show (I.moduleCompletionObj (SheafOfModules.unit.{u} X.ringCatSheaf) n).val.obj
        (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ U)) from
      (I.moduleCompletionLevelMap I.structureSheafToFormalCompletionRingCat
        I.structureSheafToFormalCompletionRingCat_compat (SheafOfModules.unit.{u} X.ringCatSheaf) n).val.app (op U) a) =
      (show I.formalCompletionRingCatSheaf.obj.obj (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ U)) from
        I.structureSheafToFormalCompletionRingCat.hom.app (op U) a) •
        (show (I.moduleCompletionObj (SheafOfModules.unit.{u} X.ringCatSheaf) n).val.obj
            (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ U)) from
          (I.moduleCompletionLevelMap I.structureSheafToFormalCompletionRingCat
            I.structureSheafToFormalCompletionRingCat_compat (SheafOfModules.unit.{u} X.ringCatSheaf) n).val.app (op U)
            (1 : Γ(X, U))) :=
  (congrArg ((I.moduleCompletionLevelMap I.structureSheafToFormalCompletionRingCat
      I.structureSheafToFormalCompletionRingCat_compat (SheafOfModules.unit.{u} X.ringCatSheaf) n).val.app (op U)) (mul_one a).symm).trans
    ((map_smul ((I.moduleCompletionLevelMap I.structureSheafToFormalCompletionRingCat
      I.structureSheafToFormalCompletionRingCat_compat (SheafOfModules.unit.{u} X.ringCatSheaf) n).val.app (op U)).hom
      (show X.ringCatSheaf.obj.obj (op U) from a)
      (show (SheafOfModules.unit.{u} X.ringCatSheaf).val.obj (op U) from (1 : Γ(X, U)))).trans (pushforward_smul_eq I.structureSheafToFormalCompletionRingCat
        (I.moduleCompletionObj (SheafOfModules.unit.{u} X.ringCatSheaf) n) (op U) a _))

/-- The projection of `𝒪_X ⟶ i_* 𝒪_X̂` to level `n` is restriction to `Y_(n+1)`. -/
private lemma formalCompletionRingCatSheafπ_structureSheafToFormalCompletionRingCat (n : ℕ)
    (U : X.Opens) (a : Γ(X, U)) :
    (I.formalCompletionRingCatSheafπ n).hom.app (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ U))
        (I.structureSheafToFormalCompletionRingCat.hom.app (op U) a) =
      I.formalCompletionSheafObjSectionsMap n U a :=
  congrArg (fun g => g.hom a) (I.formalCompletionSectionsMap_π U n)

private lemma mem_of_mem_smul_top {R : Type*} [CommRing R] (J : Ideal R) {x : R}
    (h : x ∈ J • (⊤ : Submodule R R)) : x ∈ J := by
  rwa [smul_eq_mul, Ideal.mul_top] at h

/-- On sections over `U ∩ |Y|` with `U` affine, `𝒪_X̂ ⟶ (𝒪_X)^` is injective. -/
private lemma unitToModuleCompletionUnit_injective (U : X.affineOpens)
    (x : I.formalCompletionRingCatSheaf.obj.obj
      (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ (U : X.Opens))))
    (hx : I.unitToModuleCompletionUnit.val.app _ x = 0) : x = 0 := by
  have : (SheafOfModules.unit.{u} X.ringCatSheaf : X.Modules).IsQuasicoherent :=
    ClosedImmersionIdeal.isQuasicoherent_unit X
  have hπ : ∀ n, (limit.π I.formalCompletionDiagram (op n)).hom.app
      (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ (U : X.Opens))) x = 0 := by
    intro n
    obtain ⟨a, ha⟩ := I.surjective_formalCompletionSheafObjSectionsMap n U
      ((limit.π I.formalCompletionDiagram (op n)).hom.app _ x)
    have hlev : I.moduleCompletionSectionsMap (SheafOfModules.unit.{u} X.ringCatSheaf) n U a = 0 :=
      (I.moduleCompletionLevelMap_unit_apply n U a).trans
        ((pushforward_smul_congr (I.formalCompletionRingCatSheafπ n)
          (I.moduleCompletionNeighborhood (SheafOfModules.unit.{u} X.ringCatSheaf) n) _
          ((I.formalCompletionRingCatSheafπ_structureSheafToFormalCompletionRingCat n U a).trans ha)
          _).trans ((I.unitToModuleCompletionUnit_π n U x).symm.trans
            ((congrArg _ hx).trans (map_zero _))))
    have hmem := (I.moduleCompletionSectionsMap_eq_zero_iff (SheafOfModules.unit.{u} X.ringCatSheaf) n U a).1 hlev
    have ha' : a ∈ RingHom.ker (I.formalCompletionSheafObjSectionsMap n U).hom := by
      rw [I.ker_formalCompletionSheafObjSectionsMap n U]
      exact mem_of_mem_smul_top _ hmem
    exact ha.symm.trans ha'
  refine (I.formalCompletionAffineSectionsIso U).injective
    ((adicCompletion_ext_succ fun n => ?_).trans (map_zero _).symm)
  refine (I.formalCompletionSheafObjAffineEquiv U n).injective ?_
  exact (formalCompletionSheafObjAffineEquiv_evalₐ_formalCompletionAffineSectionsIso I U n x).trans
    ((hπ n).trans ((congrArg _ (map_zero _)).trans (map_zero _)).symm)

/-- On sections over `U ∩ |Y|` with `U` affine, `𝒪_X̂ ⟶ (𝒪_X)^` is surjective. -/
private lemma unitToModuleCompletionUnit_surjective (U : X.affineOpens)
    (z : ((SheafOfModules.pushforward.{u} I.structureSheafToFormalCompletionRingCat).obj
      (I.moduleCompletion (SheafOfModules.unit.{u} X.ringCatSheaf))).val.obj (op (U : X.Opens))) :
    ∃ x, ((SheafOfModules.pushforward.{u} I.structureSheafToFormalCompletionRingCat).map
      I.unitToModuleCompletionUnit).val.app (op (U : X.Opens)) x = z := by
  have : (SheafOfModules.unit.{u} X.ringCatSheaf : X.Modules).IsQuasicoherent :=
    ClosedImmersionIdeal.isQuasicoherent_unit X
  choose t ht using fun n => I.moduleCompletionSectionsMap_surjective (SheafOfModules.unit.{u} X.ringCatSheaf) n U
    (((SheafOfModules.pushforward.{u} I.structureSheafToFormalCompletionRingCat).map
      (I.moduleCompletionπ (SheafOfModules.unit.{u} X.ringCatSheaf) n)).val.app (op (U : X.Opens)) z)
  have hs' : ∀ n, (I.moduleCompletionLevelMap I.structureSheafToFormalCompletionRingCat
      I.structureSheafToFormalCompletionRingCat_compat (SheafOfModules.unit.{u} X.ringCatSheaf) n).val.app
        (op (U : X.Opens)) (t n) =
      ((SheafOfModules.pushforward.{u} I.structureSheafToFormalCompletionRingCat).map
        (I.moduleCompletionπ (SheafOfModules.unit.{u} X.ringCatSheaf) n)).val.app (op (U : X.Opens)) z := fun n =>
    (I.moduleCompletionLevelMap_val_app I.structureSheafToFormalCompletionRingCat
      I.structureSheafToFormalCompletionRingCat_compat (SheafOfModules.unit.{u} X.ringCatSheaf) n U (t n)).trans (ht n)
  let t' : ℕ → Γ(X, (U : X.Opens)) := t
  have hS : ∀ n, t' (n + 1) - t' n ∈ I.ideal U ^ (n + 1) := by
    intro n
    have a1 := (I.moduleCompletionMap_val_app_moduleCompletionLevelMap
      I.structureSheafToFormalCompletionRingCat I.structureSheafToFormalCompletionRingCat_compat
      (SheafOfModules.unit.{u} X.ringCatSheaf) n U (t (n + 1))).symm.trans
      ((congrArg (fun y => ((SheafOfModules.pushforward.{u}
        I.structureSheafToFormalCompletionRingCat).map
        (I.moduleCompletionMap (SheafOfModules.unit.{u} X.ringCatSheaf) n)).val.app (op (U : X.Opens)) y) (hs' (n + 1))).trans
        (I.moduleCompletionMap_val_app_moduleCompletionπ
          I.structureSheafToFormalCompletionRingCat (SheafOfModules.unit.{u} X.ringCatSheaf) n U z))
    have hmem := (I.moduleCompletionSectionsMap_eq_zero_iff (SheafOfModules.unit.{u} X.ringCatSheaf) n U _).1
      ((map_sub _ _ _).trans (sub_eq_zero.2 (a1.trans (hs' n).symm)))
    exact mem_of_mem_smul_top _ hmem
  let f : AdicCompletion.AdicCauchySequence (I.ideal U) Γ(X, (U : X.Opens)) :=
    AdicCompletion.AdicCauchySequence.mk (I.ideal U) Γ(X, (U : X.Opens))
      t' (fun n => by
      refine SModEq.sub_mem.2 ?_
      have hmem : t' n - t' (n + 1) ∈ I.ideal U ^ n :=
        Ideal.pow_le_pow_right (Nat.le_succ n) (by rw [← neg_sub]; exact neg_mem (hS n))
      rw [smul_eq_mul, Ideal.mul_top]
      exact hmem)
  let x := (I.formalCompletionAffineSectionsIso U).symm (AdicCompletion.mk _ _ f)
  have hx : ∀ n, (limit.π I.formalCompletionDiagram (op n)).hom.app
      (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ (U : X.Opens))) x =
        I.formalCompletionSheafObjSectionsMap n U (t' n) := by
    intro n
    rw [← formalCompletionSheafObjAffineEquiv_evalₐ_formalCompletionAffineSectionsIso,
      RingEquiv.apply_symm_apply, AdicCompletion.evalₐ_mk, formalCompletionSheafObjAffineEquiv_mk]
    exact (RingHom.sub_mem_ker_iff (I.formalCompletionSheafObjSectionsMap n U).hom).1 (by
      rw [I.ker_formalCompletionSheafObjSectionsMap n U]
      exact hS n)
  refine ⟨x, ?_⟩
  have hc := isLimitOfPreserves (SheafOfModules.pushforward.{u}
    I.structureSheafToFormalCompletionRingCat)
    (limit.isLimit (I.moduleCompletionDiagram (SheafOfModules.unit.{u} X.ringCatSheaf)))
  refine sections_isLimit_mapCone_ext hc (op (U : X.Opens)) _ z (fun n => ?_)
  exact (I.unitToModuleCompletionUnit_π n U x).trans
    ((pushforward_smul_congr (I.formalCompletionRingCatSheafπ n)
      (I.moduleCompletionNeighborhood (SheafOfModules.unit.{u} X.ringCatSheaf) n) _
      ((hx n).trans
        (I.formalCompletionRingCatSheafπ_structureSheafToFormalCompletionRingCat n U (t n)).symm)
      _).trans ((I.moduleCompletionLevelMap_unit_apply n U (t n)).symm.trans (hs' n)))

/-- `𝒪_X̂ ⟶ (𝒪_X)^` is an isomorphism. -/
private lemma isIso_unitToModuleCompletionUnit : IsIso I.unitToModuleCompletionUnit := by
  have hB : Opens.IsBasis ((Opens.map (I.infinitesimalNeighborhoodι 1).base).obj ''
      X.affineOpens) :=
    opens_isBasis_map_image _ (I.infinitesimalNeighborhoodι 1).isClosedEmbedding.isInducing
      X.isBasis_affineOpens
  have hmono : Mono I.unitToModuleCompletionUnit := by
    let S := ShortComplex.mk (0 : SheafOfModules.unit.{u} I.formalCompletionRingCatSheaf ⟶ _)
      I.unitToModuleCompletionUnit zero_comp
    have hS : S.Exact := sheafOfModules_exact_of_isBasis_pushforward_sections S
      I.structureSheafToFormalCompletionRingCat hB (fun U hU x hx =>
        ⟨0, (map_zero _).trans (I.unitToModuleCompletionUnit_injective ⟨U, hU⟩ x hx).symm⟩)
    exact (S.exact_iff_mono rfl).1 hS
  have hepi : Epi I.unitToModuleCompletionUnit := by
    let S := ShortComplex.mk I.unitToModuleCompletionUnit
      (0 : _ ⟶ I.moduleCompletion (SheafOfModules.unit.{u} X.ringCatSheaf)) comp_zero
    have hS : S.Exact := sheafOfModules_exact_of_isBasis_pushforward_sections S
      I.structureSheafToFormalCompletionRingCat hB (fun U hU x _ =>
        I.unitToModuleCompletionUnit_surjective ⟨U, hU⟩ x)
    exact (S.exact_iff_epi rfl).1 hS
  exact isIso_of_mono_of_epi _

/-- **The completion of the structure sheaf.** The canonical map `f^* 𝒪_X ⟶ (𝒪_X)^` is an
isomorphism: `(𝒪_X)^ ≅ 𝒪_X̂`. -/
theorem isIso_pullbackToModuleCompletion_unit :
    IsIso (I.pullbackToModuleCompletion (SheafOfModules.unit.{u} X.ringCatSheaf)) := by
  have := I.isIso_unitToModuleCompletionUnit
  rw [← I.pullbackObjUnitToUnit_comp_unitToModuleCompletionUnit]
  infer_instance

end RankOne

end QuasicoherentIdealSubsheaf

section FiniteModuleNatTrans

variable {C : Type*} [Category C] [Abelian C]

/-- A four lemma: for a morphism `φ` of short complexes with `S₂` exact, `S₁.g` epi, `φ.τ₁` epi
and `φ.τ₂` mono, the map `φ.τ₃` is mono. -/
private lemma mono_τ₃_of_exact_of_epi {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂) (h₂ : S₂.Exact)
    [Epi S₁.g] [Epi φ.τ₁] [Mono φ.τ₂] : Mono φ.τ₃ := by
  refine Preadditive.mono_of_cancel_zero _ (fun {A} f₃ hf₃ => ?_)
  obtain ⟨A₁, π₁, _, f₂, hf₂⟩ := surjective_up_to_refinements_of_epi S₁.g f₃
  have h : (f₂ ≫ φ.τ₂) ≫ S₂.g = 0 := by
    rw [Category.assoc, φ.comm₂₃, ← Category.assoc, ← hf₂, Category.assoc, hf₃, comp_zero]
  obtain ⟨A₂, π₂, _, g₁, hg₁⟩ := h₂.exact_up_to_refinements _ h
  obtain ⟨A₃, π₃, _, f₁, hf₁⟩ := surjective_up_to_refinements_of_epi φ.τ₁ g₁
  have h' : f₁ ≫ S₁.f = π₃ ≫ π₂ ≫ f₂ := by
    rw [← cancel_mono φ.τ₂, Category.assoc, ← φ.comm₁₂, ← reassoc_of% hf₁, ← hg₁]
    simp only [Category.assoc]
  rw [← cancel_epi π₁, comp_zero, hf₂, ← cancel_epi π₂, ← cancel_epi π₃, comp_zero, comp_zero,
    ← Category.assoc π₂, ← Category.assoc π₃, ← Category.assoc π₃, Category.assoc _ π₂ f₂, ← h',
    Category.assoc, S₁.zero, comp_zero]

variable {A : Type u} [CommRing A] {Φ₁ Φ₂ : ModuleCat.{u} A ⥤ C}
  [Φ₁.PreservesZeroMorphisms] [Φ₂.PreservesZeroMorphisms] (c : Φ₁ ⟶ Φ₂)

/-- The short exact sequence `0 ⟶ ker p ⟶ M ⟶ N ⟶ 0` of a surjective linear map `p`. -/
private def kerShortComplex {M N : ModuleCat.{u} A} (p : M ⟶ N) : ShortComplex (ModuleCat.{u} A) :=
  ShortComplex.mk (ModuleCat.ofHom (LinearMap.ker p.hom).subtype) p (by ext x; exact x.2)

private lemma kerShortComplex_shortExact {M N : ModuleCat.{u} A} (p : M ⟶ N)
    (hp : Function.Surjective p) : (kerShortComplex p).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2
      (LinearMap.exact_subtype_ker_map p.hom)
  · exact (ModuleCat.mono_iff_injective _).2 Subtype.val_injective
  · exact (ModuleCat.epi_iff_surjective _).2 hp

omit [Abelian C] [Φ₁.PreservesZeroMorphisms] [Φ₂.PreservesZeroMorphisms] in
/-- A natural transformation `c : Φ₁ ⟶ Φ₂` of functors from `A`-modules to an abelian category is
epi at every finite module once it is an isomorphism at the finite free modules and `Φ₂` sends
surjections of finite modules to epimorphisms. -/
private lemma epi_app_of_finite
    (hepi : ∀ {M N : ModuleCat.{u} A} (p : M ⟶ N), Module.Finite A M → Module.Finite A N →
      Function.Surjective p → Epi (Φ₂.map p))
    (hfree : ∀ n : ℕ, IsIso (c.app (ModuleCat.of A (Fin n → A))))
    (M : ModuleCat.{u} A) [Module.Finite A M] : Epi (c.app M) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A M
  have := hepi (ModuleCat.ofHom f) inferInstance inferInstance hf
  have : Epi (Φ₁.map (ModuleCat.ofHom f) ≫ c.app M) := by
    rw [c.naturality]
    infer_instance
  exact epi_of_epi (Φ₁.map (ModuleCat.ofHom f)) (c.app M)

/-- **Natural transformations between right exact functors on finite modules.** Let `A` be a
Noetherian ring, `Φ₁ Φ₂` functors from `A`-modules to an abelian category and `c : Φ₁ ⟶ Φ₂`.
Suppose `Φ₁` is right exact on short exact sequences, `Φ₂` is right exact on short exact
sequences of finite modules, and `c` is an isomorphism at the finite free modules `A ^ n`. Then
`c` is an isomorphism at every finite module. -/
theorem isIso_app_of_finite_of_rightExact [IsNoetherianRing A]
    (h₁ : ∀ S : ShortComplex (ModuleCat.{u} A), S.ShortExact →
      (S.map Φ₁).Exact ∧ Epi (Φ₁.map S.g))
    (h₂ : ∀ S : ShortComplex (ModuleCat.{u} A), S.ShortExact → Module.Finite A S.X₁ →
      Module.Finite A S.X₂ → Module.Finite A S.X₃ → (S.map Φ₂).Exact ∧ Epi (Φ₂.map S.g))
    (hfree : ∀ n : ℕ, IsIso (c.app (ModuleCat.of A (Fin n → A))))
    (M : ModuleCat.{u} A) [Module.Finite A M] : IsIso (c.app M) := by
  have hepi : ∀ {M N : ModuleCat.{u} A} (p : M ⟶ N), Module.Finite A M → Module.Finite A N →
      Function.Surjective p → Epi (Φ₂.map p) := fun {M N} p hM hN hp =>
    (h₂ (kerShortComplex p) (kerShortComplex_shortExact p hp)
      (Module.Finite.of_injective (LinearMap.ker p.hom).subtype Subtype.val_injective) hM hN).2
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A M
  let S := kerShortComplex (ModuleCat.ofHom f)
  have hS := kerShortComplex_shortExact (ModuleCat.ofHom f) hf
  have hK : Module.Finite A S.X₁ :=
    Module.Finite.of_injective (LinearMap.ker f).subtype Subtype.val_injective
  have hF : Module.Finite A S.X₂ := inferInstanceAs (Module.Finite A (Fin n → A))
  have hM : Module.Finite A S.X₃ := inferInstanceAs (Module.Finite A M)
  have : Epi (S.map Φ₁).g := (h₁ S hS).2
  have : Epi (S.mapNatTrans c).τ₁ := epi_app_of_finite c hepi hfree S.X₁
  have := epi_app_of_finite c hepi hfree M
  have : Mono (S.mapNatTrans c).τ₂ := inferInstanceAs (Mono (c.app (ModuleCat.of A (Fin n → A))))
  have : Mono (c.app M) :=
    mono_τ₃_of_exact_of_epi (S.mapNatTrans c) (h₂ S hS hK hF hM).1
  exact isIso_of_mono_of_epi _

/-- The linear map `A ^ n ⟶ A ^ (n + 1)`, `w ↦ (0, w)`. -/
private def consZeroLinear (n : ℕ) : (Fin n → A) →ₗ[A] (Fin (n + 1) → A) where
  toFun w := Fin.cons 0 w
  map_add' w w' := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' a w := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- The split short exact sequence `0 ⟶ A ^ n ⟶ A ^ (n + 1) ⟶ A ⟶ 0`. -/
private def consShortComplex (n : ℕ) : ShortComplex (ModuleCat.{u} A) :=
  ShortComplex.mk (X₁ := ModuleCat.of A (Fin n → A)) (X₂ := ModuleCat.of A (Fin (n + 1) → A))
    (X₃ := ModuleCat.of A A) (ModuleCat.ofHom (consZeroLinear n))
    (ModuleCat.ofHom (LinearMap.proj 0)) (by ext w; rfl)

private lemma consShortComplex_shortExact (n : ℕ) : (consShortComplex (A := A) n).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · refine (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2 (fun v => ?_)
    constructor
    · intro hv
      refine ⟨Fin.tail v, ?_⟩
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hv.symm
      · rfl
    · rintro ⟨w, rfl⟩
      rfl
  · refine (ModuleCat.mono_iff_injective _).2 (fun w w' h => ?_)
    funext j
    exact congrFun h j.succ
  · exact (ModuleCat.epi_iff_surjective _).2 (fun a => ⟨fun _ => a, rfl⟩)

private instance (n : ℕ) : IsSplitMono (consShortComplex (A := A) n).f :=
  IsSplitMono.mk' ⟨ModuleCat.ofHom (LinearMap.pi fun j => LinearMap.proj j.succ), by ext w; rfl⟩

/-- Under the hypotheses of `isIso_app_of_finite_of_rightExact`, with `Φ₂` exact on short exact
sequences of finite modules, an isomorphism at `A` gives isomorphisms at all `A ^ n`. -/
private lemma isIso_app_free
    (h₁ : ∀ S : ShortComplex (ModuleCat.{u} A), S.ShortExact →
      (S.map Φ₁).Exact ∧ Epi (Φ₁.map S.g))
    (h₂ : ∀ S : ShortComplex (ModuleCat.{u} A), S.ShortExact → Module.Finite A S.X₁ →
      Module.Finite A S.X₂ → Module.Finite A S.X₃ → (S.map Φ₂).ShortExact)
    (hA : IsIso (c.app (ModuleCat.of A A))) (n : ℕ) :
    IsIso (c.app (ModuleCat.of A (Fin n → A))) := by
  induction n with
  | zero =>
    have hz : IsZero (ModuleCat.of A (Fin 0 → A)) :=
      ModuleCat.isZero_of_subsingleton _
    have h1 := Φ₁.map_isZero hz
    have h2 := Φ₂.map_isZero hz
    exact ⟨⟨h2.to_ _, h1.eq_of_src _ _, h2.eq_of_src _ _⟩⟩
  | succ n ih =>
    let S := consShortComplex (A := A) n
    have hS := consShortComplex_shortExact (A := A) n
    have hF : ∀ k : ℕ, Module.Finite A (ModuleCat.of A (Fin k → A)) := fun k =>
      inferInstanceAs (Module.Finite A (Fin k → A))
    have hA' : Module.Finite A (ModuleCat.of A A) := inferInstanceAs (Module.Finite A A)
    have h₁S : (S.map Φ₁).ShortExact :=
      ShortComplex.ShortExact.mk' (h₁ S hS).1 (inferInstanceAs (Mono (Φ₁.map S.f))) (h₁ S hS).2
    have : IsIso (S.mapNatTrans c).τ₁ := ih
    have : IsIso (S.mapNatTrans c).τ₃ := hA
    exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ (S.mapNatTrans c) h₁S (h₂ S hS (hF n) (hF (n + 1)) hA')

/-- **Natural transformations between right exact functors on finite modules**, from the rank one
free module: as `isIso_app_of_finite_of_rightExact`, with `Φ₂` exact on short exact sequences of
finite modules and `c` an isomorphism at `A`. -/
theorem isIso_app_of_finite_of_isIso_app_self [IsNoetherianRing A]
    (h₁ : ∀ S : ShortComplex (ModuleCat.{u} A), S.ShortExact →
      (S.map Φ₁).Exact ∧ Epi (Φ₁.map S.g))
    (h₂ : ∀ S : ShortComplex (ModuleCat.{u} A), S.ShortExact → Module.Finite A S.X₁ →
      Module.Finite A S.X₂ → Module.Finite A S.X₃ → (S.map Φ₂).ShortExact)
    (hA : IsIso (c.app (ModuleCat.of A A))) (M : ModuleCat.{u} A) [Module.Finite A M] :
    IsIso (c.app M) :=
  isIso_app_of_finite_of_rightExact c h₁
    (fun S hS h1 h2 h3 => ⟨(h₂ S hS h1 h2 h3).exact, (h₂ S hS h1 h2 h3).epi_g⟩)
    (isIso_app_free c h₁ h₂ hA) M

end FiniteModuleNatTrans

section AffineTensor

variable {A : CommRingCat.{u}} (I : Ideal A)

/-- **The canonical map `f^* (M~) ⟶ (M~)^`**, natural in the `A`-module `M`, for
`f : (V(I), 𝒪_X̂) ⟶ Spec A` the morphism of ringed spaces of `X̂ = Spf_I(A)`. Here
`f^* (M~) = M~|_{V(I)} ⊗_{𝒪_{Spec A}|_{V(I)}} 𝒪_X̂` is the module pullback. -/
def tildePullbackToModuleCompletion :
    tilde.functor A ⋙ SheafOfModules.pullback.{u}
        (specIdealSubsheaf A I).structureSheafToFormalCompletionRingCat ⟶
      tilde.functor A ⋙ (specIdealSubsheaf A I).moduleCompletionFunctor where
  app M := (specIdealSubsheaf A I).pullbackToModuleCompletion ((tilde.functor A).obj M)
  naturality _ _ φ :=
    (specIdealSubsheaf A I).pullbackToModuleCompletion_naturality ((tilde.functor A).map φ)

/-- **Hartshorne II, Proposition 9.4(b)**: for a Noetherian ring `A`, an ideal `I` and a finite
`A`-module `M`, the canonical map `M~|_{V(I)} ⊗_{𝒪_{Spec A}|_{V(I)}} 𝒪_X̂ ⟶ (M~)^` on
`X̂ = Spf_I(A)` is an isomorphism. The left side is the module pullback `f^* (M~)` along the
morphism of ringed spaces `f : (V(I), 𝒪_X̂) ⟶ Spec A`, an ordinary tensor product. -/
theorem isIso_tildePullbackToModuleCompletion [IsNoetherianRing A] (M : ModuleCat.{u} A)
    [Module.Finite A M] :
    IsIso ((specIdealSubsheaf A I).pullbackToModuleCompletion (tilde M)) := by
  let adj := tilde.adjunction.comp (SheafOfModules.pullbackPushforwardAdjunction.{u}
    (specIdealSubsheaf A I).structureSheafToFormalCompletionRingCat)
  have : (tilde.functor A ⋙ SheafOfModules.pullback.{u}
      (specIdealSubsheaf A I).structureSheafToFormalCompletionRingCat).IsLeftAdjoint :=
    adj.isLeftAdjoint
  have : (tilde.functor A ⋙ SheafOfModules.pullback.{u}
      (specIdealSubsheaf A I).structureSheafToFormalCompletionRingCat).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  have := adj.leftAdjoint_preservesColimits
  refine isIso_app_of_finite_of_isIso_app_self (tildePullbackToModuleCompletion I) ?_ ?_ ?_ M
  · intro S hS
    have := hS.epi_g
    exact ⟨hS.exact.map_of_epi_of_preservesCokernel _ hS.epi_g inferInstance, inferInstance⟩
  · intro S hS h1 h2 h3
    exact moduleCompletion_tilde_shortExact I S hS
  · exact (specIdealSubsheaf A I).isIso_pullbackToModuleCompletion_unit

/-- **Hartshorne II, Proposition 9.4(b)** (the isomorphism): for `A` Noetherian and `M` a finite
`A`-module, `M~|_{V(I)} ⊗_{𝒪_{Spec A}|_{V(I)}} 𝒪_X̂ ≅ (M~)^` as `𝒪_X̂`-modules on
`X̂ = Spf_I(A)`, the left side being the module pullback along `(V(I), 𝒪_X̂) ⟶ Spec A`. -/
def tildePullbackIsoModuleCompletion [IsNoetherianRing A] (M : ModuleCat.{u} A)
    [Module.Finite A M] :
    (SheafOfModules.pullback.{u} (specIdealSubsheaf A I).structureSheafToFormalCompletionRingCat).obj
        (tilde M) ≅ (specIdealSubsheaf A I).moduleCompletion (tilde M) :=
  have := isIso_tildePullbackToModuleCompletion I M
  asIso ((specIdealSubsheaf A I).pullbackToModuleCompletion (tilde M))

end AffineTensor

end Hartshorne

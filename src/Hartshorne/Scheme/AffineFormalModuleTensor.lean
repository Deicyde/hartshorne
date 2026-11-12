/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.FormalCompletionModule
import Hartshorne.Scheme.FormalCompletionModuleAffineSections
import Hartshorne.Scheme.AffineFormalModuleExact
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

end Hartshorne

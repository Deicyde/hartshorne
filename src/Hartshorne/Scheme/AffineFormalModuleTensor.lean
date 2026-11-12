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

end QuasicoherentIdealSubsheaf

end Hartshorne

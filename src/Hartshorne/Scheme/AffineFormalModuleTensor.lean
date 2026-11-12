/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.FormalCompletionModule
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
the implementation note of the article. The private helpers at the end are the components
`F ⟶ i_* (F / I ^ (n + 1) F)|_Y` of the comparison map and the adjunction identity used to check
their compatibility with the transition maps.
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

end QuasicoherentIdealSubsheaf

section PushforwardRestrictInv

variable {C D E : Type*} [Category C] [Category D] [Category E]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {L : GrothendieckTopology E}
  {F₁ : C ⥤ E} {F₂ : C ⥤ D} {G : D ⥤ E}
  [F₁.IsContinuous J L] [F₂.IsContinuous J K] [G.IsContinuous K L]
  {T : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}} {S : Sheaf L RingCat.{u}}
  (α : F₂ ⋙ G ⟶ F₁) (ψ : R ⟶ (G.sheafPushforwardContinuous RingCat.{u} K L).obj S)
  (φ₂ : T ⟶ (F₂.sheafPushforwardContinuous RingCat.{u} J K).obj R)
  (φ₁ : T ⟶ (F₁.sheafPushforwardContinuous RingCat.{u} J L).obj S)
  (h : ∀ (V : Cᵒᵖ) (r : T.obj.obj V),
    S.obj.map (α.app V.unop).op (φ₁.hom.app V r) =
      ψ.hom.app (op (F₂.obj V.unop)) (φ₂.hom.app V r))

include h in
/-- The map `(F₁)_* M ⟶ (F₂)_* G_* M` restricting sections along `α : F₂ ⋙ G ⟶ F₁`. -/
private def pushforwardRestrictToComp (M : SheafOfModules.{u} S) :
    (SheafOfModules.pushforward.{u} φ₁).obj M ⟶
      (SheafOfModules.pushforward.{u} φ₂).obj ((SheafOfModules.pushforward.{u} ψ).obj M) :=
  ⟨PresheafOfModules.homMk
    { app V := M.val.presheaf.map (α.app V.unop).op
      naturality V W f := by
        change M.val.presheaf.map _ ≫ M.val.presheaf.map _ =
          M.val.presheaf.map _ ≫ M.val.presheaf.map _
        rw [← Functor.map_comp, ← Functor.map_comp]
        exact congrArg (fun g => M.val.presheaf.map g)
          (congrArg Quiver.Hom.op (α.naturality f.unop).symm) }
    (fun V r m => (M.val.map_smul (α.app V.unop).op (φ₁.hom.app V r) m).trans
      (congrArg (fun a => a • M.val.map (α.app V.unop).op m) (h V r)))⟩

private lemma pushforwardRestrictToComp_val_app (M : SheafOfModules.{u} S) (V : Cᵒᵖ) (x) :
    (pushforwardRestrictToComp α ψ φ₂ φ₁ h M).val.app V x =
      M.val.map (α.app V.unop).op x :=
  rfl

end PushforwardRestrictInv

namespace QuasicoherentIdealSubsheaf

variable {X : Scheme.{u}} (I : QuasicoherentIdealSubsheaf X) (F : X.Modules)

/-- For a module `N` on `Y_(n+1)`, the pushforward of `N` along `Y_(n+1) ⟶ X` mapped to its
transport to `|Y|` pushed forward along `|Y| ⟶ X` (restriction along equal opens). -/
private def neighborhoodRestrict (n : ℕ) (N : (I.infinitesimalNeighborhood (n + 1)).Modules) :
    (Scheme.Modules.pushforward (I.infinitesimalNeighborhoodι (n + 1))).obj N ⟶
      (SheafOfModules.pushforward.{u} I.structureSheafToFormalCompletionRingCat).obj
        ((SheafOfModules.pushforward.{u} (I.formalCompletionRingCatSheafπ n)).obj N) :=
  pushforwardRestrictToComp
    (F₂ := Opens.map (I.infinitesimalNeighborhoodι 1).base)
    (G := (I.isOpenEmbedding_infinitesimalNeighborhoodFromOne n).functor)
    { app U := homOfLE (I.functor_obj_preimage_infinitesimalNeighborhoodι n U).le }
    (I.formalCompletionRingCatSheafπ n) I.structureSheafToFormalCompletionRingCat
    (I.infinitesimalNeighborhoodι (n + 1)).toRingCatSheafHom
    (fun V r => by
      have := congrArg (fun g => g.hom r) (I.formalCompletionSectionsMap_π V.unop n)
      exact this.symm)
    N

private abbrev neighborhoodPushforwardToObj (n : ℕ) :
    (Scheme.Modules.pushforward (I.infinitesimalNeighborhoodι (n + 1))).obj
        (I.moduleCompletionNeighborhood F n) ⟶
      (SheafOfModules.pushforward.{u} I.structureSheafToFormalCompletionRingCat).obj
        (I.moduleCompletionObj F n) :=
  I.neighborhoodRestrict n (I.moduleCompletionNeighborhood F n)

/-- The `n`-th component `F ⟶ F / I ^ (n + 1) F ⟶ (F / I ^ (n + 1) F)|_Y`, pushed forward. -/
private def toModuleCompletionObjPushforward (n : ℕ) :
    F ⟶ (SheafOfModules.pushforward.{u} I.structureSheafToFormalCompletionRingCat).obj
        (I.moduleCompletionObj F n) :=
  cokernel.π (I.powSmulι F n) ≫
    (Scheme.Modules.pullbackPushforwardAdjunction (I.infinitesimalNeighborhoodι (n + 1))).unit.app
      _ ≫ I.neighborhoodPushforwardToObj F n

section UnitLemmas

variable {Z Y' W : Scheme.{u}}

private lemma unit_pullbackCongr {f g : Z ⟶ W} (h : f = g) (Q : W.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app Q ≫
        (Scheme.Modules.pushforward f).map ((Scheme.Modules.pullbackCongr h).hom.app Q) ≫
          (Scheme.Modules.pushforwardCongr h).hom.app _ =
      (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app Q := by
  subst h
  ext U x
  simp [Scheme.Modules.pullbackCongr]
  rfl

private lemma unit_pullbackComp (s : Z ⟶ Y') (a : Y' ⟶ W) (Q : W.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction a).unit.app Q ≫
        (Scheme.Modules.pushforward a).map
          ((Scheme.Modules.pullbackPushforwardAdjunction s).unit.app
            ((Scheme.Modules.pullback a).obj Q)) ≫
          (Scheme.Modules.pushforwardComp s a).hom.app _ =
      (Scheme.Modules.pullbackPushforwardAdjunction (s ≫ a)).unit.app Q ≫
        (Scheme.Modules.pushforward (s ≫ a)).map ((Scheme.Modules.pullbackComp s a).inv.app Q) := by
  have := unit_conjugateEquiv ((Scheme.Modules.pullbackPushforwardAdjunction a).comp
    (Scheme.Modules.pullbackPushforwardAdjunction s))
    (Scheme.Modules.pullbackPushforwardAdjunction (s ≫ a)) (Scheme.Modules.pullbackComp s a).inv Q
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at this
  simp only [Category.assoc] at this
  exact this

private lemma unit_comp_pushforward_transition {Z Y' W : Scheme.{u}} (s : Z ⟶ Y') (a : Y' ⟶ W)
    (b : Z ⟶ W) (hs : s ≫ a = b) {Q' Q : W.Modules} (q : Q' ⟶ Q) :
    (Scheme.Modules.pullbackPushforwardAdjunction a).unit.app Q' ≫
      (Scheme.Modules.pushforward a).map
        ((Scheme.Modules.pullback a).map q ≫
          (Scheme.Modules.pullbackPushforwardAdjunction s).unit.app _ ≫
          (Scheme.Modules.pushforward s).map
            ((Scheme.Modules.pullbackComp s a).hom.app Q ≫
              (Scheme.Modules.pullbackCongr hs).hom.app Q)) =
    q ≫ (Scheme.Modules.pullbackPushforwardAdjunction b).unit.app Q ≫
      (Scheme.Modules.pushforwardCongr hs).inv.app _ ≫
      (Scheme.Modules.pushforwardComp s a).inv.app _ := by
  subst hs
  have e1 := unit_pullbackComp s a Q
  have e1' : (Scheme.Modules.pullbackPushforwardAdjunction a).unit.app Q ≫
        (Scheme.Modules.pushforward a).map
          ((Scheme.Modules.pullbackPushforwardAdjunction s).unit.app
            ((Scheme.Modules.pullback a).obj Q)) =
      (Scheme.Modules.pullbackPushforwardAdjunction (s ≫ a)).unit.app Q ≫
        (Scheme.Modules.pushforward (s ≫ a)).map ((Scheme.Modules.pullbackComp s a).inv.app Q) ≫
          (Scheme.Modules.pushforwardComp s a).inv.app _ := by
    rw [← reassoc_of% e1]
    simp
  have hg : (Scheme.Modules.pullbackCongr (rfl : s ≫ a = s ≫ a)).hom.app Q = 𝟙 _ := rfl
  have hP : (Scheme.Modules.pullbackPushforwardAdjunction (s ≫ a)).unit.app Q =
      (Scheme.Modules.pullbackPushforwardAdjunction (s ≫ a)).unit.app Q ≫
        (Scheme.Modules.pushforwardCongr (rfl : s ≫ a = s ≫ a)).inv.app
          ((Scheme.Modules.pullback (s ≫ a)).obj Q) := by
    have e2 := unit_pullbackCongr (rfl : s ≫ a = s ≫ a) Q
    rw [hg, CategoryTheory.Functor.map_id] at e2
    erw [Category.id_comp] at e2
    calc _ = ((Scheme.Modules.pullbackPushforwardAdjunction (s ≫ a)).unit.app Q ≫
          (Scheme.Modules.pushforwardCongr (rfl : s ≫ a = s ≫ a)).hom.app _) ≫
          (Scheme.Modules.pushforwardCongr (rfl : s ≫ a = s ≫ a)).inv.app _ := by
            rw [Category.assoc, Iso.hom_inv_id_app]
            erw [Category.comp_id]
      _ = _ := by rw [e2]
  have hn : (Scheme.Modules.pushforwardComp s a).inv.app
        ((Scheme.Modules.pullback s).obj ((Scheme.Modules.pullback a).obj Q)) ≫
      (Scheme.Modules.pushforward a).map
        ((Scheme.Modules.pushforward s).map ((Scheme.Modules.pullbackComp s a).hom.app Q)) =
      (Scheme.Modules.pushforward (s ≫ a)).map ((Scheme.Modules.pullbackComp s a).hom.app Q) ≫
        (Scheme.Modules.pushforwardComp s a).inv.app ((Scheme.Modules.pullback (s ≫ a)).obj Q) :=
    ((Scheme.Modules.pushforwardComp s a).inv.naturality
      ((Scheme.Modules.pullbackComp s a).hom.app Q)).symm
  simp only [Functor.map_comp, hg, Category.comp_id]
  rw [← reassoc_of% hP]
  have hu : (Scheme.Modules.pullbackPushforwardAdjunction a).unit.app Q' ≫
      (Scheme.Modules.pushforward a).map ((Scheme.Modules.pullback a).map q) =
      q ≫ (Scheme.Modules.pullbackPushforwardAdjunction a).unit.app Q :=
    Adjunction.unit_naturality _ q
  rw [← Category.assoc, hu, Category.assoc]
  congr 1
  rw [reassoc_of% e1', hn, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

end UnitLemmas

end QuasicoherentIdealSubsheaf

end Hartshorne

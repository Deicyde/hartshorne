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

section PushforwardTransition

variable {C D E₀ E₁ : Type*} [Category C] [Category D] [Category E₀] [Category E₁]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {L₀ : GrothendieckTopology E₀} {L₁ : GrothendieckTopology E₁}
  {A : C ⥤ E₁} {S : E₁ ⥤ E₀} {P : C ⥤ D} {H₁ : D ⥤ E₁} {H₀ : D ⥤ E₀}
  [A.IsContinuous J L₁] [S.IsContinuous L₁ L₀] [P.IsContinuous J K]
  [H₁.IsContinuous K L₁] [H₀.IsContinuous K L₀]
  {T : Sheaf J RingCat.{u}} {Rd : Sheaf K RingCat.{u}}
  {R₀ : Sheaf L₀ RingCat.{u}} {R₁ : Sheaf L₁ RingCat.{u}}
  (φA : T ⟶ (A.sheafPushforwardContinuous RingCat.{u} J L₁).obj R₁)
  (σ : R₁ ⟶ (S.sheafPushforwardContinuous RingCat.{u} L₁ L₀).obj R₀)
  (χ : T ⟶ (P.sheafPushforwardContinuous RingCat.{u} J K).obj Rd)
  (π₀ : Rd ⟶ (H₀.sheafPushforwardContinuous RingCat.{u} K L₀).obj R₀)
  (α₀ : P ⋙ H₀ ⟶ A ⋙ S)
  (h₀ : ∀ (V : Cᵒᵖ) (r : T.obj.obj V),
    R₀.obj.map (α₀.app V.unop).op (σ.hom.app (op (A.obj V.unop)) (φA.hom.app V r)) =
      π₀.hom.app (op (P.obj V.unop)) (χ.hom.app V r))

include h₀ in
/-- The map `A_* S_* N ⟶ P_* (H₀)_* N` restricting sections along `α₀ : P ⋙ H₀ ⟶ A ⋙ S`. -/
private def pushforwardPushforwardRestrict (N : SheafOfModules.{u} R₀) :
    (SheafOfModules.pushforward.{u} φA).obj ((SheafOfModules.pushforward.{u} σ).obj N) ⟶
      (SheafOfModules.pushforward.{u} χ).obj ((SheafOfModules.pushforward.{u} π₀).obj N) :=
  ⟨PresheafOfModules.homMk
    { app V := N.val.presheaf.map (α₀.app V.unop).op
      naturality V W f := by
        change N.val.presheaf.map _ ≫ N.val.presheaf.map _ =
          N.val.presheaf.map _ ≫ N.val.presheaf.map _
        rw [← Functor.map_comp, ← Functor.map_comp]
        exact congrArg (fun g => N.val.presheaf.map g)
          (congrArg Quiver.Hom.op (α₀.naturality f.unop).symm) }
    (fun V r m => (N.val.map_smul (α₀.app V.unop).op _ m).trans
      (congrArg (fun a => a • N.val.map (α₀.app V.unop).op m) (h₀ V r)))⟩

variable (π₁ : Rd ⟶ (H₁.sheafPushforwardContinuous RingCat.{u} K L₁).obj R₁)
  (α₁ : P ⋙ H₁ ⟶ A)
  (h₁ : ∀ (V : Cᵒᵖ) (r : T.obj.obj V),
    R₁.obj.map (α₁.app V.unop).op (φA.hom.app V r) =
      π₁.hom.app (op (P.obj V.unop)) (χ.hom.app V r))
  (β : H₀ ⟶ H₁ ⋙ S)
  (hβ : ∀ (V : Dᵒᵖ) (r : Rd.obj.obj V),
    R₀.obj.map (β.app V.unop).op (σ.hom.app (op (H₁.obj V.unop)) (π₁.hom.app V r)) =
      π₀.hom.app V r)

/-- Restricting along `α₁` and then applying `g` and restricting along `β` is applying `g` and
restricting along `α₀`, when `α₀ = β ≫ S α₁`. -/
private lemma pushforwardRestrictToComp_comp_transition
    (hα : ∀ U : C, α₀.app U = β.app (P.obj U) ≫ S.map (α₁.app U))
    {N : SheafOfModules.{u} R₀} {N' : SheafOfModules.{u} R₁}
    (g : N' ⟶ (SheafOfModules.pushforward.{u} σ).obj N) :
    pushforwardRestrictToComp α₁ π₁ χ φA h₁ N' ≫
      (SheafOfModules.pushforward.{u} χ).map
        ((SheafOfModules.pushforward.{u} π₁).map g ≫
          sheafOfModulesPushforwardCompRestrict β σ π₁ π₀ hβ N) =
    (SheafOfModules.pushforward.{u} φA).map g ≫ pushforwardPushforwardRestrict φA σ χ π₀ α₀ h₀ N := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext (fun U => ?_))
  ext y
  change N.val.map (β.app (P.obj U.unop)).op
      (g.val.app (op (H₁.obj (P.obj U.unop))) (N'.val.map (α₁.app U.unop).op y)) =
    N.val.map (α₀.app U.unop).op (g.val.app (op (A.obj U.unop)) y)
  have hg := PresheafOfModules.naturality_apply g.val (α₁.app U.unop).op y
  refine (congrArg (N.val.map (β.app (P.obj U.unop)).op) hg).trans ?_
  change N.val.map (β.app (P.obj U.unop)).op
      (N.val.map (S.map (α₁.app U.unop)).op (g.val.app (op (A.obj U.unop)) y)) = _
  refine (PresheafOfModules.map_comp_apply N.val (S.map (α₁.app U.unop)).op
    (β.app (P.obj U.unop)).op _).symm.trans ?_
  rw [hα, op_comp]

variable {B : C ⥤ E₀} [B.IsContinuous J L₀]
  (φB : T ⟶ (B.sheafPushforwardContinuous RingCat.{u} J L₀).obj R₀)
  (δ : A ⋙ S ⟶ B) (α₀' : P ⋙ H₀ ⟶ B)
  (h₀' : ∀ (V : Cᵒᵖ) (r : T.obj.obj V),
    R₀.obj.map (α₀'.app V.unop).op (φB.hom.app V r) =
      π₀.hom.app (op (P.obj V.unop)) (χ.hom.app V r))

/-- A map `B_* N ⟶ A_* S_* N` restricting sections along `δ : A ⋙ S ⟶ B`, followed by restriction
along `α₀`, is restriction along `α₀ ≫ δ`. -/
private lemma comp_pushforwardPushforwardRestrict (hδ : ∀ U : C, α₀'.app U = α₀.app U ≫ δ.app U)
    {N : SheafOfModules.{u} R₀}
    (θ : (SheafOfModules.pushforward.{u} φB).obj N ⟶
      (SheafOfModules.pushforward.{u} φA).obj ((SheafOfModules.pushforward.{u} σ).obj N))
    (hθ : ∀ (U : Cᵒᵖ) (y : N.val.obj (op (B.obj U.unop))),
      θ.val.app U y = N.val.map (δ.app U.unop).op y) :
    θ ≫ pushforwardPushforwardRestrict φA σ χ π₀ α₀ h₀ N =
      pushforwardRestrictToComp α₀' π₀ χ φB h₀' N := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext (fun U => ?_))
  ext y
  change N.val.map (α₀.app U.unop).op (θ.val.app U y) = N.val.map (α₀'.app U.unop).op y
  refine (congrArg (N.val.map (α₀.app U.unop).op) (hθ U y)).trans ?_
  refine (PresheafOfModules.map_comp_apply N.val (δ.app U.unop).op (α₀.app U.unop).op _).symm.trans ?_
  rw [hδ, op_comp]

end PushforwardTransition

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

private lemma unit_comp_pushforward_transition' {Z Y' W : Scheme.{u}} (s : Z ⟶ Y')
    (a : Y' ⟶ W) (b : Z ⟶ W) (hs : s ≫ a = b) {Q' Q : W.Modules} (q : Q' ⟶ Q)
    {N' : Y'.Modules} (p : N' ⟶ (Scheme.Modules.pullback a).obj Q)
    (v : Q' ⟶ (Scheme.Modules.pushforward a).obj N')
    (hv : v ≫ (Scheme.Modules.pushforward a).map p =
      q ≫ (Scheme.Modules.pullbackPushforwardAdjunction a).unit.app Q) :
    v ≫ (Scheme.Modules.pushforward a).map
        (p ≫ (Scheme.Modules.pullbackPushforwardAdjunction s).unit.app _ ≫
          (Scheme.Modules.pushforward s).map
            ((Scheme.Modules.pullbackComp s a).hom.app Q ≫
              (Scheme.Modules.pullbackCongr hs).hom.app Q)) =
    q ≫ (Scheme.Modules.pullbackPushforwardAdjunction b).unit.app Q ≫
      (Scheme.Modules.pushforwardCongr hs).inv.app _ ≫
      (Scheme.Modules.pushforwardComp s a).inv.app _ := by
  have h := unit_comp_pushforward_transition s a b hs (𝟙 Q)
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp] at h
  rw [Functor.map_comp, reassoc_of% hv]
  congr 1

end UnitLemmas

/-- The open of `Y_(n+1)` corresponding to `U ∩ |Y|` lies in the preimage of `U` along
`Y_(n+1) ⟶ Y_(n+2) ⟶ X`. -/
private lemma functor_obj_le_preimage_succ_ι (n : ℕ) (U : X.Opens) :
    (I.isOpenEmbedding_infinitesimalNeighborhoodFromOne n).functor.obj
        (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ U) ≤
      I.infinitesimalNeighborhoodSucc n ⁻¹ᵁ (I.infinitesimalNeighborhoodι (n + 2) ⁻¹ᵁ U) := by
  rw [I.functor_obj_preimage_infinitesimalNeighborhoodι n U, ← Scheme.Hom.comp_preimage,
    I.infinitesimalNeighborhoodSucc_comp_ι n]

private lemma succ_ι_app_restrict (n : ℕ) (U : X.Opens) (r : Γ(X, U)) :
    (I.infinitesimalNeighborhood (n + 1)).presheaf.map
        (homOfLE (I.functor_obj_le_preimage_succ_ι n U)).op
        ((I.infinitesimalNeighborhoodSucc n).app _ ((I.infinitesimalNeighborhoodι (n + 2)).app U r)) =
      I.formalCompletionSheafObjSectionsMap n U r := by
  have h := Scheme.Hom.appLE_comp_appLE (I.infinitesimalNeighborhoodSucc n)
    (I.infinitesimalNeighborhoodι (n + 2)) U (I.infinitesimalNeighborhoodι (n + 2) ⁻¹ᵁ U)
    ((I.isOpenEmbedding_infinitesimalNeighborhoodFromOne n).functor.obj
      (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ U)) le_rfl (I.functor_obj_le_preimage_succ_ι n U)
  have h' := congrArg (fun φ => φ.hom r) (h.trans (Scheme.Hom.appLE_congr_hom
    (I.infinitesimalNeighborhoodSucc_comp_ι n) _ _ _
    (I.functor_obj_preimage_infinitesimalNeighborhoodι n U).le))
  simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply, homOfLE_refl, op_id,
    CategoryTheory.Functor.map_id, CommRingCat.hom_id, RingHom.id_apply] at h'
  exact h'

/-- For a module `N` on `Y_(n+1)`, the pushforward along `Y_(n+1) ⟶ Y_(n+2) ⟶ X` mapped to the
transport of `N` to `|Y|` pushed forward along `|Y| ⟶ X` (restriction of sections). -/
private def succRestrict (n : ℕ) (N : (I.infinitesimalNeighborhood (n + 1)).Modules) :
    (SheafOfModules.pushforward.{u} (I.infinitesimalNeighborhoodι (n + 2)).toRingCatSheafHom).obj
        ((SheafOfModules.pushforward.{u} (I.infinitesimalNeighborhoodSucc n).toRingCatSheafHom).obj
          N) ⟶
      (SheafOfModules.pushforward.{u} I.structureSheafToFormalCompletionRingCat).obj
        ((SheafOfModules.pushforward.{u} (I.formalCompletionRingCatSheafπ n)).obj N) :=
  pushforwardPushforwardRestrict
    (P := Opens.map (I.infinitesimalNeighborhoodι 1).base)
    (H₀ := (I.isOpenEmbedding_infinitesimalNeighborhoodFromOne n).functor)
    (I.infinitesimalNeighborhoodι (n + 2)).toRingCatSheafHom
    (I.infinitesimalNeighborhoodSucc n).toRingCatSheafHom
    I.structureSheafToFormalCompletionRingCat (I.formalCompletionRingCatSheafπ n)
    { app U := homOfLE (I.functor_obj_le_preimage_succ_ι n U) }
    (fun V r => (I.succ_ι_app_restrict n V.unop r).trans
      (congrArg (fun g => g.hom r) (I.formalCompletionSectionsMap_π V.unop n)).symm)
    N

private lemma preimage_comp_le_of_eq {Z₀ Z₁ W' : Scheme.{u}} {s : Z₀ ⟶ Z₁} {a : Z₁ ⟶ W'}
    {b : Z₀ ⟶ W'} (hs : s ≫ a = b) (U : W'.Opens) : s ⁻¹ᵁ (a ⁻¹ᵁ U) ≤ b ⁻¹ᵁ U := by
  subst hs
  exact le_rfl

/-- The sections of `b_* N ≅ (s ≫ a)_* N ≅ a_* s_* N` (for `s ≫ a = b`) are restrictions along
the equality of opens. -/
private lemma pushforwardCongr_inv_comp_pushforwardComp_inv_val_app {Z₀ Z₁ W' : Scheme.{u}}
    {s : Z₀ ⟶ Z₁} {a : Z₁ ⟶ W'} {b : Z₀ ⟶ W'} (hs : s ≫ a = b) (N : Z₀.Modules)
    (U : W'.Opensᵒᵖ) (y : N.val.obj (op (b ⁻¹ᵁ U.unop))) :
    ((Scheme.Modules.pushforwardCongr hs).inv.app N ≫
        (Scheme.Modules.pushforwardComp s a).inv.app N).val.app U y =
      N.val.map (homOfLE (preimage_comp_le_of_eq hs U.unop)).op y := by
  subst hs
  rfl

private lemma neighborhoodRestrict_comp_transition (n : ℕ)
    (N : (I.infinitesimalNeighborhood (n + 1)).Modules)
    (N' : (I.infinitesimalNeighborhood (n + 1 + 1)).Modules)
    (g : N' ⟶ (Scheme.Modules.pushforward (I.infinitesimalNeighborhoodSucc n)).obj N) :
    I.neighborhoodRestrict (n + 1) N' ≫
      (SheafOfModules.pushforward.{u} I.structureSheafToFormalCompletionRingCat).map
        ((SheafOfModules.pushforward.{u} (I.formalCompletionRingCatSheafπ (n + 1))).map g ≫
          sheafOfModulesPushforwardCompRestrict (I.functorToPreimageInfinitesimalNeighborhoodSucc n)
            (I.infinitesimalNeighborhoodSucc n).toRingCatSheafHom
            (I.formalCompletionRingCatSheafπ (n + 1)) (I.formalCompletionRingCatSheafπ n)
            (fun V r => I.formalCompletionSheafMap_limit_π_apply n V.unop r) N) =
    (SheafOfModules.pushforward.{u} (I.infinitesimalNeighborhoodι (n + 2)).toRingCatSheafHom).map g ≫
      I.succRestrict n N :=
  pushforwardRestrictToComp_comp_transition _ _ _ _ _ _ _ _ _ _ _ (fun _ => Subsingleton.elim _ _) g

private lemma pushforwardCongr_comp_succRestrict (n : ℕ)
    (N : (I.infinitesimalNeighborhood (n + 1)).Modules) :
    ((Scheme.Modules.pushforwardCongr (I.infinitesimalNeighborhoodSucc_comp_ι n)).inv.app N ≫
        (Scheme.Modules.pushforwardComp (I.infinitesimalNeighborhoodSucc n)
          (I.infinitesimalNeighborhoodι (n + 2))).inv.app N) ≫ I.succRestrict n N =
      I.neighborhoodRestrict n N :=
by
  have key := comp_pushforwardPushforwardRestrict
    (P := Opens.map (I.infinitesimalNeighborhoodι 1).base)
    (H₀ := (I.isOpenEmbedding_infinitesimalNeighborhoodFromOne n).functor)
    (I.infinitesimalNeighborhoodι (n + 2)).toRingCatSheafHom
    (I.infinitesimalNeighborhoodSucc n).toRingCatSheafHom
    I.structureSheafToFormalCompletionRingCat (I.formalCompletionRingCatSheafπ n)
    { app U := homOfLE (I.functor_obj_le_preimage_succ_ι n U) }
    (fun V r => (I.succ_ι_app_restrict n V.unop r).trans
      (congrArg (fun g => g.hom r) (I.formalCompletionSectionsMap_π V.unop n)).symm)
    (I.infinitesimalNeighborhoodι (n + 1)).toRingCatSheafHom
    { app U := homOfLE (preimage_comp_le_of_eq (I.infinitesimalNeighborhoodSucc_comp_ι n) U) }
    { app U := homOfLE (I.functor_obj_preimage_infinitesimalNeighborhoodι n U).le }
    (fun V r => by
      have := congrArg (fun g => g.hom r) (I.formalCompletionSectionsMap_π V.unop n)
      exact this.symm)
    (fun _ => Subsingleton.elim _ _)
    (N := N)
    ((Scheme.Modules.pushforwardCongr (I.infinitesimalNeighborhoodSucc_comp_ι n)).inv.app N ≫
        (Scheme.Modules.pushforwardComp (I.infinitesimalNeighborhoodSucc n)
          (I.infinitesimalNeighborhoodι (n + 2))).inv.app N)
    (pushforwardCongr_inv_comp_pushforwardComp_inv_val_app
      (I.infinitesimalNeighborhoodSucc_comp_ι n) N)
  exact key

end QuasicoherentIdealSubsheaf

end Hartshorne

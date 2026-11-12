/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.FormalCompletion
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-!
# The completion of a module along a closed subscheme

Hartshorne, *Algebraic Geometry*, II.9, completion of a coherent sheaf (p. 194).

Let `I` be a quasi-coherent ideal subsheaf of `𝒪_X` cutting out `Y = Y_1`, let `Y_n` be the
infinitesimal neighbourhoods cut out by `I ^ n`, and let `X̂_Y` be the formal completion, with
structure sheaf `𝒪_{X̂_Y} = lim_n 𝒪_{Y_(n+1)}` on `|Y|`. For an `𝒪_X`-module `F`, the completion
of `F` along `Y` is

`F̂ = lim_n (F / I ^ (n + 1) F)|_Y`,

a sheaf of `𝒪_{X̂_Y}`-modules on `|Y|`.

* `Hartshorne.QuasicoherentIdealSubsheaf.moduleCompletionQuotient I F n`: the `𝒪_X`-module
  `F / I ^ (n + 1) F`, the cokernel of the inclusion of the submodule sheaf `I ^ (n + 1) F`.
* `Hartshorne.QuasicoherentIdealSubsheaf.moduleCompletionNeighborhood I F n`: its restriction to
  `Y_(n+1)`, the module pullback along `Y_(n+1) ⟶ X`. Since `F / I ^ (n + 1) F` is killed by
  `I ^ (n + 1)`, this is the sheaf `(F / I ^ (n + 1) F)|_Y` with its `𝒪_{Y_(n+1)}`-module structure.
* `Hartshorne.QuasicoherentIdealSubsheaf.moduleCompletionObj I F n`: the same sheaf on `|Y|`,
  transported along the homeomorphism `Y ⟶ Y_(n+1)`, as an `𝒪_{X̂_Y}`-module through the
  projection `𝒪_{X̂_Y} ⟶ 𝒪_{Y_(n+1)}`.
* `Hartshorne.QuasicoherentIdealSubsheaf.moduleCompletionMap I F n`: the transition map, induced by
  the quotient map `F / I ^ (n + 2) F ⟶ F / I ^ (n + 1) F` and restriction along
  `Y_(n+1) ⟶ Y_(n+2)`.
* `Hartshorne.QuasicoherentIdealSubsheaf.moduleCompletionDiagram I F`: the inverse system.
* `Hartshorne.QuasicoherentIdealSubsheaf.moduleCompletion I F`: its limit `F̂`, a sheaf of modules
  over the structure sheaf of `X̂_Y`.
* `Hartshorne.QuasicoherentIdealSubsheaf.moduleCompletionπ I F n`: the projection
  `F̂ ⟶ (F / I ^ (n + 1) F)|_Y`, compatible with the transition maps
  (`moduleCompletionπ_comp_moduleCompletionMap`).

Hartshorne works over a Noetherian scheme `X` with `F` coherent; the construction uses no
finiteness, so it is made for every scheme and every `𝒪_X`-module.
-/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Topology Opposite TopologicalSpace

namespace Hartshorne

universe u

section PushforwardRestrict

variable {C D E : Type*} [Category C] [Category D] [Category E]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {L : GrothendieckTopology E}
  {F₁ : C ⥤ E} {F₂ : C ⥤ D} {G : D ⥤ E}
  [F₁.IsContinuous J L] [F₂.IsContinuous J K] [G.IsContinuous K L]
  {T : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}} {S : Sheaf L RingCat.{u}}
  (α : F₁ ⟶ F₂ ⋙ G) (ψ : R ⟶ (G.sheafPushforwardContinuous RingCat.{u} K L).obj S)
  (φ₂ : T ⟶ (F₂.sheafPushforwardContinuous RingCat.{u} J K).obj R)
  (φ₁ : T ⟶ (F₁.sheafPushforwardContinuous RingCat.{u} J L).obj S)
  (h : ∀ (V : Cᵒᵖ) (r : T.obj.obj V),
    S.obj.map (α.app V.unop).op (ψ.hom.app (op (F₂.obj V.unop)) (φ₂.hom.app V r)) =
      φ₁.hom.app V r)

include h in
/-- Given functors `F₁ : C ⥤ E`, `F₂ : C ⥤ D`, `G : D ⥤ E` and a natural transformation
`α : F₁ ⟶ F₂ ⋙ G`, compatible ring maps give a map of sheaves of modules from the pushforward
along `G` and then `F₂` to the pushforward along `F₁`, restricting sections along `α`. -/
def sheafOfModulesPushforwardCompRestrict (M : SheafOfModules.{u} S) :
    (SheafOfModules.pushforward.{u} φ₂).obj ((SheafOfModules.pushforward.{u} ψ).obj M) ⟶
      (SheafOfModules.pushforward.{u} φ₁).obj M :=
  ⟨PresheafOfModules.homMk
    { app V := M.val.presheaf.map (α.app V.unop).op
      naturality V W f := by
        change M.val.presheaf.map _ ≫ M.val.presheaf.map _ =
          M.val.presheaf.map _ ≫ M.val.presheaf.map _
        rw [← Functor.map_comp, ← Functor.map_comp]
        exact congrArg (fun g => M.val.presheaf.map g)
          (congrArg Quiver.Hom.op (α.naturality f.unop).symm) }
    (fun V r m => (M.val.map_smul (α.app V.unop).op (ψ.hom.app _ (φ₂.hom.app V r)) m).trans
      (congrArg (fun a => a • M.val.map (α.app V.unop).op m) (h V r)))⟩

lemma sheafOfModulesPushforwardCompRestrict_val_app (M : SheafOfModules.{u} S) (V : Cᵒᵖ) (x) :
    (sheafOfModulesPushforwardCompRestrict α ψ φ₂ φ₁ h M).val.app V x =
      M.val.map (α.app V.unop).op x :=
  rfl

end PushforwardRestrict

namespace QuasicoherentIdealSubsheaf

open ArtinReesKernelSheaf

variable {X : Scheme.{u}} (I : QuasicoherentIdealSubsheaf X)

/-- The structure sheaf `lim_n 𝒪_{Y_(n+1)}` of the formal completion, as a sheaf of rings in
`RingCat`, the form in which it carries sheaves of modules. -/
abbrev formalCompletionRingCatSheaf :
    Sheaf (Opens.grothendieckTopology (I.infinitesimalNeighborhood 1 : TopCat)) RingCat.{u} :=
  (sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj I.formalCompletionSheaf

/-- The functor on opens induced by the homeomorphism `Y ⟶ Y_(n+1)` is continuous. -/
instance isContinuous_functor_infinitesimalNeighborhoodFromOne (n : ℕ) :
    (I.isOpenEmbedding_infinitesimalNeighborhoodFromOne n).functor.IsContinuous
      (Opens.grothendieckTopology (I.infinitesimalNeighborhood 1 : TopCat))
      (Opens.grothendieckTopology (I.infinitesimalNeighborhood (n + 1) : TopCat)) :=
  (I.isOpenEmbedding_infinitesimalNeighborhoodFromOne n).functor_isContinuous

/-- The projection `𝒪_{X̂_Y} ⟶ 𝒪_{Y_(n+1)}` of sheaves of rings on `|Y|`, with `𝒪_{Y_(n+1)}`
transported along the homeomorphism `Y ⟶ Y_(n+1)`. -/
def formalCompletionRingCatSheafπ (n : ℕ) :
    I.formalCompletionRingCatSheaf ⟶
      ((I.isOpenEmbedding_infinitesimalNeighborhoodFromOne n).functor.sheafPushforwardContinuous
        RingCat.{u} _ _).obj (I.infinitesimalNeighborhood (n + 1)).ringCatSheaf :=
  (sheafCompose _ (forget₂ CommRingCat RingCat.{u})).map (limit.π I.formalCompletionDiagram (op n))

/-- The projections of the formal completion are compatible with the transition maps. -/
lemma limit_π_formalCompletionDiagram_comp_formalCompletionSheafMap (n : ℕ) :
    limit.π I.formalCompletionDiagram (op (n + 1)) ≫ I.formalCompletionSheafMap n =
      limit.π I.formalCompletionDiagram (op n) := by
  have hw := limit.w I.formalCompletionDiagram (homOfLE (Nat.le_add_right n 1)).op
  have hmap : I.formalCompletionDiagram.map (homOfLE (Nat.le_add_right n 1)).op =
      I.formalCompletionSheafMap n :=
    CategoryTheory.Functor.ofOpSequence_map_homOfLE_succ _ n
  rw [hmap] at hw
  exact hw

/-- The projection to `𝒪_{Y_(n+2)}` followed by restriction to `Y_(n+1)` is the projection to
`𝒪_{Y_(n+1)}`, on sections over `V ⊆ |Y|`. -/
lemma formalCompletionSheafMap_limit_π_apply (n : ℕ) (V : Opens (I.infinitesimalNeighborhood 1))
    (r : I.formalCompletionSheaf.presheaf.obj (op V)) :
    (I.infinitesimalNeighborhood (n + 1)).presheaf.map
        (homOfLE (I.functor_obj_le_preimage_infinitesimalNeighborhoodSucc n V)).op
        ((I.infinitesimalNeighborhoodSucc n).app _
          ((limit.π I.formalCompletionDiagram (op (n + 1))).hom.app (op V) r)) =
      (limit.π I.formalCompletionDiagram (op n)).hom.app (op V) r := by
  rw [← I.limit_π_formalCompletionDiagram_comp_formalCompletionSheafMap n]
  rfl

/-- The inclusion of the image of `V ⊆ |Y|` in `Y_(n+1)` into the preimage in `Y_(n+1)` of its
image in `Y_(n+2)`, as a natural transformation of functors on the opens of `|Y|`. -/
def functorToPreimageInfinitesimalNeighborhoodSucc (n : ℕ) :
    (I.isOpenEmbedding_infinitesimalNeighborhoodFromOne n).functor ⟶
      (I.isOpenEmbedding_infinitesimalNeighborhoodFromOne (n + 1)).functor ⋙
        Opens.map (I.infinitesimalNeighborhoodSucc n).base where
  app V := homOfLE (I.functor_obj_le_preimage_infinitesimalNeighborhoodSucc n V)

variable (F : X.Modules)

/-- The inclusion `I ^ (n + 1) F ⟶ F` of the submodule sheaf `I ^ (n + 1) F` of `F`. -/
def powSmulι (n : ℕ) :
    ArtinReesKernelSheaf.toModules
      (powSmul (quasicoherentIdealSubsheafEquiv I) (n + 1) (⊤ : F.val.Submodule))
      (isLocal_powSmul _ _ _) ⟶ F :=
  ⟨PresheafOfModules.Submodule.ι _⟩

/-- `I ^ (n + 2) F ⟶ F` factors through `I ^ (n + 1) F ⟶ F`. -/
@[reassoc]
lemma inclusion_comp_powSmulι (n : ℕ) :
    inclusion _ _ (powSmul_antitone (quasicoherentIdealSubsheafEquiv I) ⊤ (Nat.le_succ (n + 1))) ≫
      I.powSmulι F n = I.powSmulι F (n + 1) :=
  SheafOfModules.Hom.ext (PresheafOfModules.Submodule.homOfLE_ι _)

/-- **The quotient `F / I ^ (n + 1) F`** of an `𝒪_X`-module, the cokernel of the inclusion of the
submodule sheaf `I ^ (n + 1) F`. -/
def moduleCompletionQuotient (n : ℕ) : X.Modules :=
  cokernel (I.powSmulι F n)

/-- The quotient map `F / I ^ (n + 2) F ⟶ F / I ^ (n + 1) F`. -/
def moduleCompletionQuotientMap (n : ℕ) :
    I.moduleCompletionQuotient F (n + 1) ⟶ I.moduleCompletionQuotient F n :=
  cokernel.desc _ (cokernel.π _) ((I.inclusion_comp_powSmulι_assoc F n _).symm.trans
    ((congrArg (inclusion _ _ _ ≫ ·) (cokernel.condition _)).trans Limits.comp_zero))

@[reassoc (attr := simp)]
lemma π_moduleCompletionQuotientMap (n : ℕ) :
    cokernel.π (I.powSmulι F (n + 1)) ≫ I.moduleCompletionQuotientMap F n =
      cokernel.π (I.powSmulι F n) :=
  cokernel.π_desc _ _ _

/-- **`(F / I ^ (n + 1) F)|_Y` as a module on `Y_(n+1)`**: the pullback of `F / I ^ (n + 1) F`
along the closed immersion `Y_(n+1) ⟶ X`. As `F / I ^ (n + 1) F` is killed by `I ^ (n + 1)`, this
is the restriction of `F / I ^ (n + 1) F` to `Y` with its `𝒪_{Y_(n+1)}`-module structure. -/
def moduleCompletionNeighborhood (n : ℕ) : (I.infinitesimalNeighborhood (n + 1)).Modules :=
  (Scheme.Modules.pullback (I.infinitesimalNeighborhoodι (n + 1))).obj
    (I.moduleCompletionQuotient F n)

/-- `Y_(n+1) ⟶ Y_(n+2) ⟶ X` is the closed immersion `Y_(n+1) ⟶ X`. -/
private lemma infinitesimalNeighborhoodSucc_comp_ι' (n : ℕ) :
    I.infinitesimalNeighborhoodSucc n ≫ I.infinitesimalNeighborhoodι (n + 2) =
      I.infinitesimalNeighborhoodι (n + 1) :=
  Scheme.IdealSheafData.inclusion_subschemeι _

/-- The transition map `(F / I ^ (n + 2) F)|_Y ⟶ (F / I ^ (n + 1) F)|_Y` on `Y_(n+2)`: pull back
the quotient map along `Y_(n+2) ⟶ X`, then restrict to `Y_(n+1)`. -/
def moduleCompletionNeighborhoodMap (n : ℕ) :
    I.moduleCompletionNeighborhood F (n + 1) ⟶
      (Scheme.Modules.pushforward (I.infinitesimalNeighborhoodSucc n)).obj
        (I.moduleCompletionNeighborhood F n) :=
  (Scheme.Modules.pullback (I.infinitesimalNeighborhoodι (n + 2))).map
      (I.moduleCompletionQuotientMap F n) ≫
    (Scheme.Modules.pullbackPushforwardAdjunction (I.infinitesimalNeighborhoodSucc n)).unit.app _ ≫
    (Scheme.Modules.pushforward (I.infinitesimalNeighborhoodSucc n)).map
      ((Scheme.Modules.pullbackComp (I.infinitesimalNeighborhoodSucc n)
          (I.infinitesimalNeighborhoodι (n + 2))).hom.app _ ≫
        (Scheme.Modules.pullbackCongr (I.infinitesimalNeighborhoodSucc_comp_ι' n)).hom.app _)

/-- **`(F / I ^ (n + 1) F)|_Y` as an `𝒪_{X̂_Y}`-module**: the `𝒪_{Y_(n+1)}`-module
`moduleCompletionNeighborhood I F n`, transported to `|Y|` along the homeomorphism `Y ⟶ Y_(n+1)`
and viewed as an `𝒪_{X̂_Y}`-module through the projection `𝒪_{X̂_Y} ⟶ 𝒪_{Y_(n+1)}`. -/
def moduleCompletionObj (n : ℕ) : SheafOfModules.{u} I.formalCompletionRingCatSheaf :=
  (SheafOfModules.pushforward.{u} (I.formalCompletionRingCatSheafπ n)).obj
    (I.moduleCompletionNeighborhood F n)

/-- **The transition map** `(F / I ^ (n + 2) F)|_Y ⟶ (F / I ^ (n + 1) F)|_Y` of `𝒪_{X̂_Y}`-modules
on `|Y|`: induced by the quotient map, followed by restriction along `Y_(n+1) ⟶ Y_(n+2)`. -/
def moduleCompletionMap (n : ℕ) :
    I.moduleCompletionObj F (n + 1) ⟶ I.moduleCompletionObj F n :=
  (SheafOfModules.pushforward.{u} (I.formalCompletionRingCatSheafπ (n + 1))).map
      (I.moduleCompletionNeighborhoodMap F n) ≫
    sheafOfModulesPushforwardCompRestrict (I.functorToPreimageInfinitesimalNeighborhoodSucc n)
      (I.infinitesimalNeighborhoodSucc n).toRingCatSheafHom (I.formalCompletionRingCatSheafπ (n + 1))
      (I.formalCompletionRingCatSheafπ n)
      (fun V r => I.formalCompletionSheafMap_limit_π_apply n V.unop r)
      (I.moduleCompletionNeighborhood F n)

/-- **The inverse system of the completion of `F`**: `n ↦ (F / I ^ (n + 1) F)|_Y`, as
`𝒪_{X̂_Y}`-modules on `|Y|`, for `n ≥ 0`, that is Hartshorne's `F / I ^ n F` for `n ≥ 1`. -/
def moduleCompletionDiagram : ℕᵒᵖ ⥤ SheafOfModules.{u} I.formalCompletionRingCatSheaf :=
  CategoryTheory.Functor.ofOpSequence (I.moduleCompletionMap F)

/-- **The completion of a module along a closed subscheme** (Hartshorne II.9, p. 194, there for a
coherent module on a Noetherian scheme): `F̂ = lim_n (F / I ^ (n + 1) F)|_Y`, the inverse limit of
the restrictions to `|Y|` of the quotients `F / I ^ (n + 1) F`, as a sheaf of modules over the
structure sheaf `lim_n (𝒪_X / I ^ (n + 1))|_Y` of the formal completion `X̂_Y`. -/
def moduleCompletion : SheafOfModules.{u} I.formalCompletionRingCatSheaf :=
  limit (I.moduleCompletionDiagram F)

/-- The projection `F̂ ⟶ (F / I ^ (n + 1) F)|_Y`. -/
def moduleCompletionπ (n : ℕ) : I.moduleCompletion F ⟶ I.moduleCompletionObj F n :=
  limit.π (I.moduleCompletionDiagram F) (op n)

/-- The projections of the completion are compatible with the transition maps. -/
@[reassoc (attr := simp)]
lemma moduleCompletionπ_comp_moduleCompletionMap (n : ℕ) :
    I.moduleCompletionπ F (n + 1) ≫ I.moduleCompletionMap F n = I.moduleCompletionπ F n := by
  have hw := limit.w (I.moduleCompletionDiagram F) (homOfLE (Nat.le_add_right n 1)).op
  have hmap : (I.moduleCompletionDiagram F).map (homOfLE (Nat.le_add_right n 1)).op =
      I.moduleCompletionMap F n :=
    CategoryTheory.Functor.ofOpSequence_map_homOfLE_succ _ n
  rw [hmap] at hw
  exact hw

/-- **Sections of the completion.** For every open `V ⊆ |Y|`, the sections of `F̂` over `V` are the
inverse limit of the sections over `V` of the `(F / I ^ (n + 1) F)|_Y`, with the projections. -/
def isLimitModuleCompletionSections (V : Opens (I.infinitesimalNeighborhood 1)) :
    IsLimit ((SheafOfModules.evaluation I.formalCompletionRingCatSheaf (op V)).mapCone
      (limit.cone (I.moduleCompletionDiagram F))) :=
  isLimitOfPreserves _ (limit.isLimit _)

end QuasicoherentIdealSubsheaf

end Hartshorne

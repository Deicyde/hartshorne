/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.RingedSpace.ModuleSheafHom
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-!
# Sheaf Hom as a left-exact functor

Hartshorne, *Algebraic Geometry*, III.6 (opening, p. 233).

Let `(X, 𝒪_X)` be a ringed space, given by a topological space `X` and a sheaf `R` of commutative
rings on `X`, and let `F` be an `𝒪_X`-module. The sheaf Hom `ℋom(F, -)`
(`Hartshorne.Ringed.moduleSheafHom`) is functorial in its second argument through
postcomposition; we package it as an endofunctor `Hartshorne.Ringed.moduleSheafHomFunctor F` of
the category of `𝒪_X`-modules and show that it is additive and left exact, i.e. preserves finite
limits (`moduleSheafHomFunctor_additive_leftExact`). In fact it preserves all small limits
(`moduleSheafHomFunctor_preservesLimits`): limits of module sheaves are computed on sections,
restriction to an open `U` preserves them (`overFunctor_preservesLimits`), and the sections of
`ℋom(F, G)` over `U` are the morphisms `F|_U ⟶ G|_U`, which preserve limits in `G` as a corepresented
functor does.

Finally, the global sections of `ℋom(F, G)` are identified with the morphisms `F ⟶ G`, as
`𝒪_X(X)`-modules and naturally in `G` (`moduleSheafHomGlobalSectionsIso`).
-/

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace Hartshorne

namespace Ringed

variable {X : TopCat.{u}}

/-- Restriction of module sheaves to an open `U` (over the restricted structure sheaf on the opens
contained in `U`) preserves limits of small diagrams, since limits are computed on sections. -/
private noncomputable def overFunctorIsLimit {S : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
    (U : Opens X) {J : Type u} [SmallCategory J] {K : J ⥤ SheafOfModules.{u} S} {c : Cone K}
    (hc : IsLimit c) : IsLimit ((SheafOfModules.overFunctor S U).mapCone c) := by
  apply isLimitOfReflects (SheafOfModules.forget _)
  apply PresheafOfModules.evaluationJointlyReflectsLimits
  intro V
  apply isLimitOfReflects (forget (ModuleCat _))
  have := SheafOfModules.evaluationPreservesLimitsOfShape.{u} J S (op V.unop.left)
  have h₁ := isLimitOfPreserves (SheafOfModules.evaluation.{u} S (op V.unop.left)) hc
  have h₂ := isLimitOfPreserves (forget (ModuleCat.{u} (S.obj.obj (op V.unop.left)))) h₁
  exact h₂

/-- Restriction of module sheaves to an open `U` preserves small limits. -/
noncomputable instance overFunctor_preservesLimits
    (S : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X) :
    PreservesLimitsOfSize.{u, u} (SheafOfModules.overFunctor.{u} S U) :=
  ⟨fun {_} _ ↦ ⟨fun {_} ↦ ⟨fun {_} hc ↦ ⟨overFunctorIsLimit U hc⟩⟩⟩⟩

variable {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

/-- **The sheaf Hom functor** `ℋom(F, -)` on the module sheaves of a ringed space: it sends `G` to
the module sheaf `ℋom(F, G)` and a morphism `g : G ⟶ G'` to postcomposition with `g`. -/
noncomputable def moduleSheafHomFunctor (F : SheafOfModules.{u} (ringCatSheafOf R)) :
    SheafOfModules.{u} (ringCatSheafOf R) ⥤ SheafOfModules.{u} (ringCatSheafOf R) where
  obj G := moduleSheafHom F G
  map g := moduleSheafHomMap (𝟙 F) g
  map_id G := by
    apply SheafOfModules.hom_ext
    ext U σ
    change (SheafOfModules.overFunctor _ U.unop).map (𝟙 F) ≫ σ ≫
      (SheafOfModules.overFunctor _ U.unop).map (𝟙 G) = σ
    obtain ⟨τ, rfl⟩ : ∃ τ : F.over U.unop ⟶ G.over U.unop, τ = σ := ⟨σ, rfl⟩
    simp
  map_comp {G₁ G₂ G₃} g h := by
    apply SheafOfModules.hom_ext
    ext U σ
    change (SheafOfModules.overFunctor _ U.unop).map (𝟙 F) ≫ σ ≫ (g ≫ h).over U.unop =
      (SheafOfModules.overFunctor _ U.unop).map (𝟙 F) ≫
        ((SheafOfModules.overFunctor _ U.unop).map (𝟙 F) ≫ σ ≫ g.over U.unop) ≫ h.over U.unop
    obtain ⟨τ, rfl⟩ : ∃ τ : F.over U.unop ⟶ G₁.over U.unop, τ = σ := ⟨σ, rfl⟩
    simp

lemma moduleSheafHomFunctor_obj (F G : SheafOfModules.{u} (ringCatSheafOf R)) :
    (moduleSheafHomFunctor F).obj G = moduleSheafHom F G := rfl

lemma moduleSheafHomFunctor_map (F : SheafOfModules.{u} (ringCatSheafOf R))
    {G G' : SheafOfModules.{u} (ringCatSheafOf R)} (g : G ⟶ G') :
    (moduleSheafHomFunctor F).map g = moduleSheafHomMap (𝟙 F) g := rfl

/-- On sections over `U`, the sheaf Hom functor is postcomposition of local morphisms. -/
lemma moduleSheafHomFunctor_map_app (F : SheafOfModules.{u} (ringCatSheafOf R))
    {G G' : SheafOfModules.{u} (ringCatSheafOf R)} (g : G ⟶ G') (U : Opens X)
    (σ : (moduleSheafHom F G).val.obj (op U)) :
    moduleSheafHomOverSectionsAddEquiv F G' U ((moduleSheafHomFunctor F).map g |>.val.app (op U) σ) =
      moduleSheafHomOverSectionsAddEquiv F G U σ ≫ g.over U := by
  change (SheafOfModules.overFunctor _ U).map (𝟙 F) ≫ σ ≫ g.over U = σ ≫ g.over U
  obtain ⟨τ, rfl⟩ : ∃ τ : F.over U ⟶ G.over U, τ = σ := ⟨σ, rfl⟩
  simp

/-- The sheaf Hom functor `ℋom(F, -)` is additive. -/
noncomputable instance moduleSheafHomFunctor_additive (F : SheafOfModules.{u} (ringCatSheafOf R)) :
    (moduleSheafHomFunctor F).Additive where
  map_add := by
    intro G G' f g
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext σ
    rfl

/-- The sheaf Hom functor `ℋom(F, -)` sends a limit cone of a small diagram to a limit cone. -/
private noncomputable def moduleSheafHomFunctorIsLimit (F : SheafOfModules.{u} (ringCatSheafOf R))
    {J : Type u} [SmallCategory J] {K : J ⥤ SheafOfModules.{u} (ringCatSheafOf R)} {c : Cone K}
    (hc : IsLimit c) : IsLimit ((moduleSheafHomFunctor F).mapCone c) := by
  haveI := (SheafOfModules.fullyFaithfulForget (ringCatSheafOf R)).full
  haveI := (SheafOfModules.fullyFaithfulForget (ringCatSheafOf R)).faithful
  apply isLimitOfReflects (SheafOfModules.forget _)
  apply PresheafOfModules.evaluationJointlyReflectsLimits
  intro U
  apply isLimitOfReflects (forget (ModuleCat _))
  -- On sections over `U`, the cone is the corepresented functor of `F|_U` applied to the
  -- restriction of `c` to `U`, which is a limit cone.
  have h := isLimitOfPreserves (coyoneda.obj (op (F.over U.unop))) (overFunctorIsLimit U.unop hc)
  refine (IsLimit.equivOfNatIsoOfIso (NatIso.ofComponents (fun j ↦ Iso.refl _) ?_) _ _
    (Cone.ext (Iso.refl _) ?_)) h
  · intro j j' f
    ext σ
    change σ ≫ (K.map f).over U.unop =
      (SheafOfModules.overFunctor _ U.unop).map (𝟙 F) ≫ σ ≫ (K.map f).over U.unop
    simp
  · intro j
    ext σ
    change σ ≫ (c.π.app j).over U.unop =
      (SheafOfModules.overFunctor _ U.unop).map (𝟙 F) ≫ σ ≫ (c.π.app j).over U.unop
    simp

/-- The sheaf Hom functor `ℋom(F, -)` preserves all small limits. -/
noncomputable instance moduleSheafHomFunctor_preservesLimits
    (F : SheafOfModules.{u} (ringCatSheafOf R)) :
    PreservesLimitsOfSize.{u, u} (moduleSheafHomFunctor F) :=
  ⟨fun {_} _ ↦ ⟨fun {_} ↦ ⟨fun {_} hc ↦ ⟨moduleSheafHomFunctorIsLimit F hc⟩⟩⟩⟩

/-- **Sheaf Hom is additive and left exact** (Hartshorne III.6, p. 233). For a module sheaf `F` on
a ringed space, the sheaf Hom functor `ℋom(F, -)` on the category of `𝒪_X`-modules is additive and
left exact, that is, it preserves finite limits. -/
theorem moduleSheafHomFunctor_additive_leftExact (F : SheafOfModules.{u} (ringCatSheafOf R)) :
    (moduleSheafHomFunctor F).Additive ∧ PreservesFiniteLimits (moduleSheafHomFunctor F) :=
  ⟨inferInstance, inferInstance⟩

/-- The functor `G ↦ Hom(F, G)` from `𝒪_X`-modules to `𝒪_X(X)`-modules, where a global section
acts on a morphism by multiplying its values (the canonical action
`moduleSheafHomGlobalHomModule`), and a morphism `g` acts by postcomposition. -/
noncomputable def moduleSheafGlobalHomFunctor (F : SheafOfModules.{u} (ringCatSheafOf R)) :
    SheafOfModules.{u} (ringCatSheafOf R) ⥤ ModuleCat.{u} ((ringCatSheafOf R).obj.obj (op ⊤)) where
  obj G := @ModuleCat.of _ _ (F ⟶ G) _ (moduleSheafHomGlobalHomModule F G)
  map {G G'} g := by
    letI : Module ((ringCatSheafOf R).obj.obj (op ⊤)) (F ⟶ G) := moduleSheafHomGlobalHomModule F G
    letI : Module ((ringCatSheafOf R).obj.obj (op ⊤)) (F ⟶ G') :=
      moduleSheafHomGlobalHomModule F G'
    refine ModuleCat.ofHom
      { toFun := fun φ ↦ φ ≫ g
        map_add' := fun φ ψ ↦ Preadditive.add_comp _ _ _ φ ψ g
        map_smul' := ?_ }
    intro r φ
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    ext x
    change g.val.app V
        ((moduleSheafHomGlobalScalarRingHom G r).val.app (op V.unop) (φ.val.app V x)) =
      (moduleSheafHomGlobalScalarRingHom G' r).val.app (op V.unop) (g.val.app V (φ.val.app V x))
    rw [moduleSheafHom_global_scalar_app, moduleSheafHom_global_scalar_app]
    exact (g.val.app V).hom.map_smul _ _
  map_id G := by
    let : Module ((ringCatSheafOf R).obj.obj (op ⊤)) (F ⟶ G) := moduleSheafHomGlobalHomModule F G
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    exact Category.comp_id φ
  map_comp {G₁ G₂ G₃} g h := by
    let : Module ((ringCatSheafOf R).obj.obj (op ⊤)) (F ⟶ G₁) :=
      moduleSheafHomGlobalHomModule F G₁
    let : Module ((ringCatSheafOf R).obj.obj (op ⊤)) (F ⟶ G₃) :=
      moduleSheafHomGlobalHomModule F G₃
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    exact (Category.assoc φ g h).symm

/-- **Global sections of the sheaf Hom functor.** The global sections of `ℋom(F, G)` are the
morphisms `F ⟶ G`, as `𝒪_X(X)`-modules and naturally in `G`. -/
noncomputable def moduleSheafHomGlobalSectionsIso (F : SheafOfModules.{u} (ringCatSheafOf R)) :
    moduleSheafHomFunctor F ⋙ SheafOfModules.evaluation _ (op ⊤) ≅
      moduleSheafGlobalHomFunctor F :=
  NatIso.ofComponents (fun G ↦ (moduleSheafHomGlobalSectionsLinearEquiv F G).toModuleIso) (by
    intro G G' g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro σ
    exact (moduleSheafHom_global_map (𝟙 F) g σ).trans (Category.id_comp _))

/-- The global identification sends a global section of `ℋom(F, G)` to the corresponding morphism
`F ⟶ G`. -/
lemma moduleSheafHomGlobalSectionsIso_hom_app (F G : SheafOfModules.{u} (ringCatSheafOf R))
    (σ : (moduleSheafHom F G).val.obj (op ⊤)) :
    (moduleSheafHomGlobalSectionsIso F).hom.app G σ =
      moduleSheafHomGlobalSectionsLinearEquiv F G σ := rfl

end Ringed

end Hartshorne

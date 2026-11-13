/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.RingedSpace.FiniteLocallyFreeDuality
import Hartshorne.RingedSpace.SheafExtRestrictCompose

/-!
# Evaluation of local morphisms at a global section

For `𝒪_X`-modules `L`, `G` and a global section `ℓ ∈ L(X)`, evaluation at `ℓ` is the morphism
`ℋom(L, G) ⟶ G` sending a local morphism `ψ : L|_W ⟶ G|_W` to `ψ(ℓ|_W)`
(`Hartshorne.Ringed.homEvalAt`). It is compatible with precomposition and postcomposition
(`Hartshorne.Ringed.moduleSheafHomPrecomp_homEvalAt`, `Hartshorne.Ringed.homEvalAt_comp`), with
restriction to an open subset (`Hartshorne.Ringed.homRestrict_homEvalAt`) and with transport along
a homeomorphism (`Hartshorne.Ringed.homTransport_homEvalAt`).
-/

universe u

open CategoryTheory Opposite TopologicalSpace Limits

/- Sections of restricted and transported modules are only definitionally (not reducibly) sections
of the original modules. -/
set_option backward.isDefEq.respectTransparency false

namespace Hartshorne

namespace Ringed

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

lemma presheaf_map_map_apply (L : SheafOfModules.{u} (ringCatSheafOf R)) {a b c : (Opens X)ᵒᵖ}
    (f : a ⟶ b) (g : b ⟶ c) (h : a ⟶ c) (x : L.val.presheaf.obj a) :
    L.val.presheaf.map g (L.val.presheaf.map f x) = L.val.presheaf.map h x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- On sections over `W`, evaluation at the restriction of a global section `ℓ`. -/
noncomputable def homEvalAtSections {L : SheafOfModules.{u} (ringCatSheafOf R)}
    (ℓ : L.val.obj (op ⊤)) (G : SheafOfModules.{u} (ringCatSheafOf R)) (W : Opens X) :
    (moduleSheafHom L G).val.presheaf.obj (op W) →ₗ[R.obj.obj (op W)]
      G.val.presheaf.obj (op W) where
  toFun ψ := moduleSheafHomEval ψ (le_refl W) (L.val.presheaf.map (homOfLE le_top).op ℓ)
  map_add' _ _ := rfl
  map_smul' r ψ := by
    change moduleSheafHomEval (r • ψ) (le_refl W) _ = r • _
    rw [moduleSheafHomEval_smul]
    congr 1
    change (R.obj.map (𝟙 (op W))) r = r
    rw [CategoryTheory.Functor.map_id]
    rfl

/-- **Evaluation at a global section** `ℓ ∈ L(X)`: the morphism `ℋom(L, G) ⟶ G`,
`ψ ↦ ψ(ℓ|_W)` on sections over `W`. -/
noncomputable def homEvalAt {L : SheafOfModules.{u} (ringCatSheafOf R)} (ℓ : L.val.obj (op ⊤))
    (G : SheafOfModules.{u} (ringCatSheafOf R)) : moduleSheafHom L G ⟶ G :=
  modulesHomMk (homEvalAtSections ℓ G) fun W V i ψ => by
    change moduleSheafHomEval ψ ((le_refl V).trans i) (L.val.presheaf.map (homOfLE le_top).op ℓ) =
      G.val.presheaf.map (homOfLE i).op
        (moduleSheafHomEval ψ (le_refl W) (L.val.presheaf.map (homOfLE le_top).op ℓ))
    rw [← moduleSheafHomEval_natural ψ (le_refl W) i, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp]
    rfl

lemma homEvalAt_app {L : SheafOfModules.{u} (ringCatSheafOf R)} (ℓ : L.val.obj (op ⊤))
    (G : SheafOfModules.{u} (ringCatSheafOf R)) (W : Opens X)
    (ψ : (moduleSheafHom L G).val.obj (op W)) :
    (homEvalAt ℓ G).val.app (op W) ψ =
      moduleSheafHomEval ψ (le_refl W) (L.val.presheaf.map (homOfLE le_top).op ℓ) := rfl

/-- Evaluating `ψ ∘ g` at `ℓ` is evaluating `ψ` at `g(ℓ)`. -/
lemma moduleSheafHomPrecomp_homEvalAt {L L' : SheafOfModules.{u} (ringCatSheafOf R)}
    (g : L' ⟶ L) (ℓ : L'.val.obj (op ⊤)) (G : SheafOfModules.{u} (ringCatSheafOf R)) :
    (moduleSheafHomPrecomp g).app G ≫ homEvalAt ℓ G = homEvalAt (g.val.app (op ⊤) ℓ) G := by
  apply SheafOfModules.hom_ext
  ext W ψ
  change moduleSheafHomEval (sectionsMap (moduleSheafHomMap g (𝟙 G)) W.unop ψ) (le_refl _)
      (L'.val.presheaf.map (homOfLE le_top).op ℓ) =
    moduleSheafHomEval ψ (le_refl _) (L.val.presheaf.map (homOfLE le_top).op (g.val.app (op ⊤) ℓ))
  rw [moduleSheafHomEval_map]
  have h : sectionsMap g W.unop (L'.val.presheaf.map (homOfLE le_top).op ℓ) =
      L.val.presheaf.map (homOfLE le_top).op (g.val.app (op ⊤) ℓ) := by
    have h' := ConcreteCategory.congr_hom (g.val.naturality (homOfLE (le_top : W.unop ≤ ⊤)).op) ℓ
    simp only [ConcreteCategory.comp_apply] at h'
    exact h'
  rw [h]
  rfl

/-- Evaluating `g ∘ ψ` at `ℓ` is `g` applied to the evaluation of `ψ`. -/
lemma homEvalAt_comp {L : SheafOfModules.{u} (ringCatSheafOf R)} (ℓ : L.val.obj (op ⊤))
    {G G' : SheafOfModules.{u} (ringCatSheafOf R)} (g : G ⟶ G') :
    (moduleSheafHomFunctor L).map g ≫ homEvalAt ℓ G' = homEvalAt ℓ G ≫ g := by
  apply SheafOfModules.hom_ext
  ext W ψ
  change moduleSheafHomEval (sectionsMap (moduleSheafHomMap (𝟙 L) g) W.unop ψ) (le_refl _)
      (L.val.presheaf.map (homOfLE le_top).op ℓ) = _
  rw [moduleSheafHomEval_map]
  rfl

section Restrict

variable (U : Opens X)

/-- The restriction `ℓ|_U` of a global section, as a global section of `L|_U`. -/
noncomputable abbrev restrictSection {L : SheafOfModules.{u} (ringCatSheafOf R)}
    (ℓ : L.val.obj (op ⊤)) : ((moduleRestrict U).obj L).val.obj (op ⊤) :=
  L.val.presheaf.map (homOfLE le_top).op ℓ

/-- **Evaluation commutes with restriction**: `(ev_ℓ)|_U` is `ev_{ℓ|_U}` through
`ℋom_X(L, G)|_U ≅ ℋom_U(L|_U, G|_U)`. -/
lemma homRestrict_homEvalAt {L : SheafOfModules.{u} (ringCatSheafOf R)} (ℓ : L.val.obj (op ⊤))
    (G : SheafOfModules.{u} (ringCatSheafOf R)) :
    homRestrict L G ≫ homEvalAt (restrictSection U ℓ) ((moduleRestrict U).obj G) =
      (moduleRestrict U).map (homEvalAt ℓ G) := by
  apply SheafOfModules.hom_ext
  ext W σ
  change moduleSheafHomEval ((homRestrict L G).val.app W σ) (le_refl _)
      (((moduleRestrict U).obj L).val.presheaf.map (homOfLE le_top).op
        (restrictSection U ℓ)) =
    moduleSheafHomEval σ (le_refl _) (L.val.presheaf.map (homOfLE le_top).op ℓ)
  exact congrArg (moduleSheafHomEval _ _) (presheaf_map_map_apply L _ _ _ ℓ)

end Restrict

section Transport

open Transport

variable {A B : TopCat.{u}} {H : B ≅ A} {S : Sheaf (Opens.grothendieckTopology A) CommRingCat.{u}}
  {T : Sheaf (Opens.grothendieckTopology B) CommRingCat.{u}} (ρ : RingTransport H S T)

/-- A global section of `L`, as a global section of the transported module `τL`. -/
noncomputable abbrev transportSection {L : SheafOfModules.{u} (ringCatSheafOf T)}
    (ℓ : L.val.obj (op ⊤)) : ((transport ρ).obj L).val.obj (op ⊤) :=
  L.val.presheaf.map (homOfLE le_top).op ℓ

/-- **Evaluation commutes with transport**: `τ(ev_ℓ)` is `ev_ℓ` through
`τ ℋom_B(L, G) ≅ ℋom_A(τL, τG)`. -/
lemma homTransport_homEvalAt {L : SheafOfModules.{u} (ringCatSheafOf T)} (ℓ : L.val.obj (op ⊤))
    (G : SheafOfModules.{u} (ringCatSheafOf T)) :
    homTransport ρ L G ≫ homEvalAt (transportSection ρ ℓ) ((transport ρ).obj G) =
      (transport ρ).map (homEvalAt ℓ G) := by
  apply SheafOfModules.hom_ext
  ext W σ
  change moduleSheafHomEval ((homTransport ρ L G).val.app W σ) (le_refl _)
      (((transport ρ).obj L).val.presheaf.map (homOfLE le_top).op (transportSection ρ ℓ)) =
    moduleSheafHomEval σ (le_refl _) (L.val.presheaf.map (homOfLE le_top).op ℓ)
  exact congrArg (moduleSheafHomEval _ _) (presheaf_map_map_apply L _ _ _ ℓ)

end Transport

end Ringed

end Hartshorne

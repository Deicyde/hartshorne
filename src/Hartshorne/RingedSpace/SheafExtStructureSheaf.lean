/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.RingedSpace.SheafExt
import Hartshorne.RingedSpace.PicardGroup

/-!
# The sheaves `ℰxt(𝒪_X, G)`

Hartshorne, *Algebraic Geometry*, III.6, Proposition 6.3 (p. 234).

Let `(X, 𝒪_X)` be a ringed space, given by a topological space `X` and a sheaf `R` of commutative
rings on `X`. For every `𝒪_X`-module `G`, evaluation at the unit section identifies
`ℋom(𝒪_X, G)` with `G`, naturally in `G` (`Hartshorne.Ringed.moduleSheafHomStructureModuleIso`).
Hence `ℋom(𝒪_X, -)` is isomorphic to the identity functor, which is exact, so

* `ℰxt⁰(𝒪_X, G) ≅ G`, naturally in `G` (`Hartshorne.Ringed.sheafExtStructureModuleZeroIso`), and
* `ℰxtⁱ(𝒪_X, G) = 0` for every `i > 0` (`Hartshorne.Ringed.isZero_sheafExt_structureModule`).

Both statements together are `Hartshorne.Ringed.sheafExt_structureModule`.
-/

universe u

open CategoryTheory Opposite TopologicalSpace Limits

namespace Hartshorne

namespace Ringed

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

set_option hygiene false in
/-- `𝒪_X`-modules. -/
local notation "𝓜" => SheafOfModules.{u} (ringCatSheafOf R)

set_option hygiene false in
/-- Sections of the structure sheaf over an open. -/
local notation3 "𝒪(" U ")" => R.obj.obj (Opposite.op U)

/-- Sections of a module sheaf over an open, as an abelian group. -/
local notation3 "Γ(" M ", " U ")" => (PresheafOfModules.presheaf (SheafOfModules.val M)).obj
  (Opposite.op U)

/-- The unit section of `𝒪_X` over an open `W`. -/
private abbrev unitSection (W : Opens X) : Γ(structureModule R, W) :=
  show 𝒪(W) from 1

private lemma structureModule_map_unitSection {V W : Opens X} (i : V ≤ W) :
    (structureModule R).val.presheaf.map (homOfLE i).op (unitSection W) = unitSection V :=
  map_one (R.obj.map (homOfLE i).op).hom

/-- Evaluation at the unit section: a section `ψ` of `ℋom(𝒪_X, G)` over `W` is sent to
`ψ(1) ∈ G(W)`. -/
noncomputable def homStructureModuleEvalSections (G : 𝓜) (W : Opens X) :
    Γ(moduleSheafHom (structureModule R) G, W) →ₗ[𝒪(W)] Γ(G, W) where
  toFun ψ := moduleSheafHomEval ψ (le_refl W) (unitSection W)
  map_add' _ _ := rfl
  map_smul' r ψ := by
    change moduleSheafHomEval (r • ψ) (le_refl W) _ = r • _
    rw [moduleSheafHomEval_smul]
    congr 1
    change (R.obj.map (𝟙 (op W))) r = r
    rw [CategoryTheory.Functor.map_id]
    rfl

lemma homStructureModuleEvalSections_apply (G : 𝓜) (W : Opens X)
    (ψ : Γ(moduleSheafHom (structureModule R) G, W)) :
    homStructureModuleEvalSections G W ψ =
      moduleSheafHomEval ψ (le_refl W) (show 𝒪(W) from 1) := rfl

private lemma homStructureModuleEvalSections_eq (G : 𝓜) (W : Opens X) :
    ⇑(homStructureModuleEvalSections G W) =
      ⇑(Equiv.funUnique (ULift.{u} (Fin 1)) Γ(G, W)) ∘
        ⇑(localFrameEval (G := G)
          (fun _ : ULift.{u} (Fin 1) => unitSection (R := R) ⊤) (le_top : W ≤ ⊤)) := by
  funext ψ
  change _ = moduleSheafHomEval ψ (le_refl W) _
  rw [structureModule_map_unitSection]
  rfl

private lemma homStructureModuleEvalSections_bijective (G : 𝓜) (W : Opens X) :
    Function.Bijective (homStructureModuleEvalSections G W) := by
  rw [homStructureModuleEvalSections_eq]
  exact (Equiv.bijective _).comp (structureModule_isLocalFrame.localFrameEval_bijective le_top)

/-- The evaluation morphism `ℋom(𝒪_X, G) ⟶ G`, sending a local morphism `ψ` over `W` to `ψ(1)`. -/
noncomputable def moduleSheafHomStructureModuleEval (G : 𝓜) :
    moduleSheafHom (structureModule R) G ⟶ G :=
  modulesHomMk (homStructureModuleEvalSections G) fun W V i ψ => by
    change moduleSheafHomEval ψ ((le_refl V).trans i) (unitSection V) =
      G.val.presheaf.map (homOfLE i).op (moduleSheafHomEval ψ (le_refl W) (unitSection W))
    rw [← moduleSheafHomEval_natural ψ (le_refl W) i, structureModule_map_unitSection]

lemma moduleSheafHomStructureModuleEval_app (G : 𝓜) (W : Opens X)
    (ψ : Γ(moduleSheafHom (structureModule R) G, W)) :
    sectionsMap (moduleSheafHomStructureModuleEval G) W ψ =
      moduleSheafHomEval ψ (le_refl W) (show 𝒪(W) from 1) := rfl

instance moduleSheafHomStructureModuleEval_isIso (G : 𝓜) :
    IsIso (moduleSheafHomStructureModuleEval G) :=
  modules_isIso_of_locally_bijective _ fun _ =>
    ⟨⊤, trivial, fun V _ => homStructureModuleEvalSections_bijective G V⟩

lemma moduleSheafHomStructureModuleEval_naturality {G G' : 𝓜} (g : G ⟶ G') :
    (moduleSheafHomFunctor (structureModule R)).map g ≫ moduleSheafHomStructureModuleEval G' =
      moduleSheafHomStructureModuleEval G ≫ g := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext ψ
  rfl

/-- **`ℋom(𝒪_X, -)` is the identity functor.** For every `𝒪_X`-module `G`, evaluation at the unit
section is an isomorphism `ℋom(𝒪_X, G) ≅ G`, natural in `G`. -/
noncomputable def moduleSheafHomStructureModuleIso :
    moduleSheafHomFunctor (structureModule R) ≅ 𝟭 𝓜 :=
  NatIso.ofComponents
    (fun G => @asIso _ _ _ _ (moduleSheafHomStructureModuleEval G)
      (moduleSheafHomStructureModuleEval_isIso G))
    fun g => moduleSheafHomStructureModuleEval_naturality g

lemma moduleSheafHomStructureModuleIso_hom_app (G : 𝓜) :
    moduleSheafHomStructureModuleIso.hom.app G = moduleSheafHomStructureModuleEval G := rfl

/- As in `Hartshorne.RingedSpace.SheafExt`, use the preadditive structure coming from the abelian
structure, which is the one Mathlib's derived-functor API is stated with. -/
attribute [local instance 2000] Abelian.toPreadditive

/-- **`ℰxt⁰(𝒪_X, G) ≅ G`** (Hartshorne III.6, Proposition 6.3, p. 234). The natural
identification of `ℰxt⁰(𝒪_X, -) = R⁰ℋom(𝒪_X, -)` with the identity functor: the left exact functor
`ℋom(𝒪_X, -)` agrees with its zeroth right derived functor, and is identified with the identity by
evaluation at the unit section. -/
noncomputable def sheafExtStructureModuleZeroIso : sheafExt (structureModule R) 0 ≅ 𝟭 𝓜 :=
  (moduleSheafHomFunctor (structureModule R)).rightDerivedZeroIsoSelf ≪≫
    moduleSheafHomStructureModuleIso

/-- **`ℰxtⁱ(𝒪_X, G) = 0` for `i > 0`** (Hartshorne III.6, Proposition 6.3, p. 234). Since
`ℋom(𝒪_X, -)` is isomorphic to the identity functor, applying it to an injective resolution of `G`
gives a complex isomorphic to the resolution itself, whose cohomology vanishes in positive
degrees. -/
theorem isZero_sheafExt_structureModule (G : 𝓜) {i : ℕ} (hi : 0 < i) :
    IsZero ((sheafExt (structureModule R) i).obj G) := by
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  let I := injectiveResolution G
  refine IsZero.of_iso ?_ (sheafExtIsoHomology (structureModule R) I (n + 1))
  refine IsZero.of_iso ?_ ((HomologicalComplex.homologyFunctor _ _ (n + 1)).mapIso
    ((NatIso.mapHomologicalComplex moduleSheafHomStructureModuleIso _).app I.cocomplex ≪≫
      (Functor.mapHomologicalComplexIdIso _ _).app I.cocomplex))
  exact (I.cocomplex_exactAt_succ n).isZero_homology

/-- **Sheaf `ℰxt` from the structure sheaf** (Hartshorne III.6, Proposition 6.3, p. 234). For
every `𝒪_X`-module `G`, `ℰxt⁰(𝒪_X, G) ≅ G` naturally in `G`, and `ℰxtⁱ(𝒪_X, G) = 0` for every
`i > 0`. The natural isomorphism is `Hartshorne.Ringed.sheafExtStructureModuleZeroIso`. -/
theorem sheafExt_structureModule :
    Nonempty (sheafExt (structureModule R) 0 ≅ 𝟭 𝓜) ∧
      ∀ (G : 𝓜) (i : ℕ), 0 < i → IsZero ((sheafExt (structureModule R) i).obj G) :=
  ⟨⟨sheafExtStructureModuleZeroIso⟩, fun G _ hi => isZero_sheafExt_structureModule G hi⟩

end Ringed

end Hartshorne

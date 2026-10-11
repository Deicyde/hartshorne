/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
import Mathlib.Topology.Sheaves.Flasque
import Mathlib.Topology.Sheaves.Skyscraper

/-!
# The Godement flasque embedding

For an abelian sheaf `F` on a topological space `X`, its sheaf of discontinuous sections is the
product, over all `x : X`, of the skyscraper sheaf at `x` with value the stalk `F_x`. Thus its
sections on an open set are arbitrary choices of stalk elements at the points of that open set.
The germ maps assemble to a natural monomorphism from `F`, and the product is flasque.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Hartshorne

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false

noncomputable local instance {X : TopCat.{u}} (x : X) :
    ∀ U : Opens X, Decidable (x ∈ U) :=
  fun _U ↦ Classical.dec _

/-- The stalk-skyscraper endofunctor at a point. -/
private noncomputable abbrev godementFactor (X : TopCat.{u}) (x : X) :
    TopCat.Sheaf AddCommGrpCat.{u} X ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
  (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) ⋙
    skyscraperSheafFunctor x

/-- The family of skyscraper sheaves whose product is the Godement sheaf. -/
private noncomputable abbrev godementFactors
    (X : TopCat.{u}) (F : TopCat.Sheaf AddCommGrpCat.{u} X) (x : X) :
    TopCat.Sheaf AddCommGrpCat.{u} X :=
  (godementFactor X x).obj F

/-- The Godement/discontinuous-sections functor on abelian sheaves. -/
noncomputable abbrev godementFunctor (X : TopCat.{u}) :
    TopCat.Sheaf AddCommGrpCat.{u} X ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
  Functor.pi' (fun x : X ↦ godementFactor X x) ⋙ Pi.functor X

/-- The natural germ map from a sheaf to its Godement sheaf. -/
noncomputable def toGodement (X : TopCat.{u}) :
    𝟭 (TopCat.Sheaf AddCommGrpCat.{u} X) ⟶ godementFunctor X where
  app F := Pi.lift fun x ↦ (stalkSkyscraperSheafAdjunction x).unit.app F
  naturality {F G} f := by
    apply Pi.hom_ext
    intro x
    rw [Category.assoc, Pi.lift_π]
    change (f ≫ (stalkSkyscraperSheafAdjunction x).unit.app G) =
      Limits.Pi.lift (fun x ↦ (stalkSkyscraperSheafAdjunction x).unit.app F) ≫
        Limits.Pi.map (fun x ↦ (godementFactor X x).map f) ≫
          Limits.Pi.π (fun x ↦ (godementFactor X x).obj G) x
    rw [Pi.map_π, ← Category.assoc, Pi.lift_π]
    exact (stalkSkyscraperSheafAdjunction x).unit.naturality f

@[reassoc (attr := simp)]
theorem toGodement_app_comp_π (X : TopCat.{u})
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (x : X) :
    (toGodement X).app F ≫ Pi.π (godementFactors X F) x =
      (stalkSkyscraperSheafAdjunction x).unit.app F :=
  Pi.lift_π _ _

/-- The germ map from a sheaf to its Godement sheaf is a monomorphism. -/
instance toGodement_mono (X : TopCat.{u})
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) : Mono ((toGodement X).app F) := by
  let _ (x : X) : Mono
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((toGodement X).app F).hom) := by
    let r :=
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          (Pi.π (godementFactors X F) x).hom ≫
        (stalkSkyscraperSheafAdjunction x).counit.app
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj F.obj)
    exact ({
      retraction := r
      id := by
        dsimp only [r]
        rw [← Category.assoc, ← Functor.map_comp]
        rw [show ((toGodement X).app F).hom ≫
            (Pi.π (godementFactors X F) x).hom =
          ((stalkSkyscraperSheafAdjunction x).unit.app F).hom by
            exact congrArg (fun f ↦ f.hom) (toGodement_app_comp_π X F x)]
        exact (stalkSkyscraperSheafAdjunction x).left_triangle_components F
      } : SplitMono
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          ((toGodement X).app F).hom)).mono
  exact TopCat.Presheaf.mono_of_stalk_mono ((toGodement X).app F)

/-- Evaluation of an abelian sheaf on one open set, as a functor. -/
private abbrev sheafSectionsFunctor (X : TopCat.{u}) (U : (Opens X)ᵒᵖ) :
    TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
  TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
    (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj U

private noncomputable instance godementSectionsFunctor_preservesProduct
    (X : TopCat.{u}) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (U : (Opens X)ᵒᵖ) :
    PreservesLimit (Discrete.functor (godementFactors X F))
      (sheafSectionsFunctor X U) where
  preserves hc :=
    ⟨isLimitOfPreserves ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj U)
      (isLimitOfPreserves (TopCat.Sheaf.forget AddCommGrpCat.{u} X) hc)⟩

/-- Assemble a section of the product sheaf from one section of every factor. -/
private noncomputable def godementSectionOfComponents
    (X : TopCat.{u}) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (U : (Opens X)ᵒᵖ)
    (s : ∀ x : X, (godementFactors X F x).obj.obj U) :
    ((godementFunctor X).obj F).obj.obj U :=
  (PreservesProduct.iso (sheafSectionsFunctor X U) (godementFactors X F)).inv
    ((Limits.Concrete.productEquiv
      (fun x : X ↦ (sheafSectionsFunctor X U).obj (godementFactors X F x))).symm s)

@[simp]
private theorem godementSectionOfComponents_π
    (X : TopCat.{u}) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (U : (Opens X)ᵒᵖ)
    (s : ∀ x : X, (godementFactors X F x).obj.obj U) (x : X) :
    (Pi.π (godementFactors X F) x).hom.app U
        (godementSectionOfComponents X F U s) = s x := by
  change ((PreservesProduct.iso (sheafSectionsFunctor X U)
      (godementFactors X F)).inv ≫
      (sheafSectionsFunctor X U).map (Pi.π (godementFactors X F) x))
      ((Limits.Concrete.productEquiv
        (fun x : X ↦ (sheafSectionsFunctor X U).obj (godementFactors X F x))).symm s) = s x
  rw [← piComparison_comp_π, ← PreservesProduct.iso_hom,
    Iso.inv_hom_id_assoc]
  exact Limits.Concrete.productEquiv_symm_apply_π _ _ _

private theorem godement_section_ext
    (X : TopCat.{u}) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (U : (Opens X)ᵒᵖ)
    {s t : ((godementFunctor X).obj F).obj.obj U}
    (h : ∀ x : X, (Pi.π (godementFactors X F) x).hom.app U s =
      (Pi.π (godementFactors X F) x).hom.app U t) : s = t := by
  apply Limits.Concrete.Pi.map_ext (godementFactors X F) (sheafSectionsFunctor X U)
  exact h

/-- Every Godement sheaf is flasque. -/
instance godementFunctor_obj_isFlasque (X : TopCat.{u})
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    ((godementFunctor X).obj F).IsFlasque := by
  classical
  let _ (x : X) : (godementFactors X F x).IsFlasque :=
    isFlasque_skyscraperSheaf_of_hasZeroObject x _
  constructor
  intro U V i
  apply (AddCommGrpCat.epi_iff_surjective _).2
  intro s
  have hsurj (x : X) : Function.Surjective ((godementFactors X F x).obj.map i) :=
    (AddCommGrpCat.epi_iff_surjective _).1 inferInstance
  choose t ht using fun x : X ↦
    hsurj x ((Pi.π (godementFactors X F) x).hom.app V s)
  let t' := godementSectionOfComponents X F U t
  refine ⟨t', ?_⟩
  apply godement_section_ext X F V
  intro x
  calc
    (Pi.π (godementFactors X F) x).hom.app V
        (((godementFunctor X).obj F).obj.map i t') =
      (godementFactors X F x).obj.map i
        ((Pi.π (godementFactors X F) x).hom.app U t') := by
          have hn := ConcreteCategory.congr_hom
            ((Pi.π (godementFactors X F) x).hom.naturality i) t'
          simp only [ConcreteCategory.comp_apply] at hn
          convert hn using 1
          all_goals rfl
    _ = (godementFactors X F x).obj.map i (t x) := by
      rw [godementSectionOfComponents_π]
    _ = (Pi.π (godementFactors X F) x).hom.app V s := ht x

end


end Hartshorne

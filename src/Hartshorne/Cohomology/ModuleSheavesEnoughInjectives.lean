/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
import Mathlib.Topology.Sheaves.Module

/-!
# Enough injectives for module sheaves

Module presheaves have a separator and exact filtered colimits. These properties transfer
through module sheafification, so module sheaves form a Grothendieck abelian category.
The general enough-injectives theorem then gives Hartshorne III.2, Proposition 2.2 for an
arbitrary topological ringed space. The stalk/skyscraper construction is not needed here.
-/

open CategoryTheory CategoryTheory.Limits

universe u v₁ v₂ u₁ u₂

namespace Hartshorne

/-- The coproduct of free representable module presheaves is a separator. -/
private theorem presheafModules_hasSeparator
    {C : Type u} [SmallCategory C] (R : Cᵒᵖ ⥤ RingCat.{u}) :
    HasSeparator (PresheafOfModules.{u} R) := by
  refine ⟨∐ fun X : C => (PresheafOfModules.free R).obj (yoneda.obj X), ?_⟩
  exact (PresheafOfModules.freeYoneda.isSeparating R).isSeparator_coproduct

/-- Exact filtered colimits and the separator make module presheaves Grothendieck abelian. -/
private theorem presheafModules_isGrothendieckAbelian
    {C : Type u} [SmallCategory C] (R : Cᵒᵖ ⥤ RingCat.{u}) :
    IsGrothendieckAbelian.{u} (PresheafOfModules.{u} R) := by
  let _ : HasSeparator (PresheafOfModules.{u} R) := presheafModules_hasSeparator R
  refine {
    hasFilteredColimitsOfSize := ⟨fun _ _ _ => inferInstance⟩
    ab5OfSize := ⟨fun K _ _ => ?_⟩
  }
  exact HasExactColimitsOfShape.domain_of_functor K (PresheafOfModules.toPresheaf R)

/-- A left adjoint transports a separator when its right adjoint is faithful. -/
private theorem separator_leftAdjoint
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    {F : C ⥤ D} {G : D ⥤ C} [G.Faithful] (adj : F ⊣ G)
    {S : C} (hS : IsSeparator S) : IsSeparator (F.obj S) := by
  rw [isSeparator_def]
  intro X Y f g h
  apply G.map_injective
  apply hS.def
  intro a
  have ha := congrArg (adj.homEquiv S Y) (h ((adj.homEquiv S X).symm a))
  simpa only [adj.homEquiv_naturality_right, Equiv.apply_symm_apply] using ha

/-- Module sheafification transfers the Grothendieck abelian properties to module sheaves. -/
private theorem sheafModules_isGrothendieckAbelian
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) : IsGrothendieckAbelian.{u} (SheafOfModules.{u} R) := by
  let _ : IsGrothendieckAbelian.{u} (PresheafOfModules.{u} R.obj) :=
    presheafModules_isGrothendieckAbelian R.obj
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  refine {
    hasFilteredColimitsOfSize := ⟨fun _ _ _ => inferInstance⟩
    ab5OfSize := ⟨fun K _ _ => adj.hasExactColimitsOfShape K⟩
    hasSeparator := ?_
  }
  exact ⟨(PresheafOfModules.sheafification (𝟙 R.obj)).obj
      (separator (PresheafOfModules.{u} R.obj)),
    separator_leftAdjoint adj (isSeparator_separator (PresheafOfModules.{u} R.obj))⟩

/-- Module sheaves on an arbitrary topological ringed space have enough injectives. -/
theorem moduleSheaves_enoughInjectives (X : TopCat.{u})
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) :
    EnoughInjectives.{u} (SheafOfModules.{u} R) := by
  let _ : IsGrothendieckAbelian.{u} (SheafOfModules.{u} R) :=
    sheafModules_isGrothendieckAbelian R
  infer_instance

end Hartshorne

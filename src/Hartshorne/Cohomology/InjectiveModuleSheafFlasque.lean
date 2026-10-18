/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.ModuleSectionsRepresentable
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Topology.Sheaves.Flasque

/-!
# Injective module sheaves are flasque

Hartshorne III.2, Lemma 2.4, printed p. 207. Injectivity in the category of module
sheaves extends a section across the canonical monomorphism O_V → O_U. The proved
evaluation square identifies this extension with surjectivity of ordinary additive
restriction maps. No Noetherian hypothesis or injectivity after forgetting scalars is used.
-/

open CategoryTheory Opposite TopologicalSpace

namespace Hartshorne

universe u

set_option backward.isDefEq.respectTransparency false in
/-- Every injective module sheaf is flasque as its actual underlying abelian sheaf. -/
theorem injectiveModuleSheaf_isFlasque
    {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (F : SheafOfModules.{u} R) [Injective F] :
    TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf.{u} R).obj F) where
  epi {U V} i := by
    apply (AddCommGrpCat.epi_iff_surjective _).mpr
    change Function.Surjective (fun t : F.val.obj U ↦ (F.val.map i t : F.val.obj V))
    intro s
    obtain ⟨g, hg⟩ := Injective.factors
      ((moduleSectionsAddEquiv R V.unop F).symm s)
      (openStructureModuleInclusion R U.unop V.unop (leOfHom i.unop))
    refine ⟨moduleSectionsAddEquiv R U.unop F g, ?_⟩
    have h := moduleSectionsAddEquiv_restriction R U.unop F V.unop (leOfHom i.unop) g
    rw [hg] at h
    have hs := (moduleSectionsAddEquiv R V.unop F).apply_symm_apply s
    have hmap : (F.val.map i (moduleSectionsAddEquiv R U.unop F g) : F.val.obj V) =
        (moduleSectionsAddEquiv R V.unop F) ((moduleSectionsAddEquiv R V.unop F).symm s) := by
      have hi : (homOfLE (leOfHom i.unop)).op = i := Subsingleton.elim _ _
      rw [hi] at h
      exact h.symm
    exact hmap.trans hs

end Hartshorne

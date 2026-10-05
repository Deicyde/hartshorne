/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.EpiMono
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Topology.Sheaves.AddCommGrpCat

/-!
# The image of a sheaf morphism is a subsheaf

Hartshorne, *Algebraic Geometry*, II.1, p. 64 and Exercise 1.4(a,b), p. 66.

For a morphism of sheaves of abelian groups, its image sheaf is obtained by
sheafifying the pointwise image presheaf. The resulting morphism to the target
sheaf is a monomorphism.
-/

open CategoryTheory

universe u

namespace Hartshorne

noncomputable section

/-- For a morphism `φ : F ⟶ G` of sheaves of abelian groups, sheafification of
the pointwise image presheaf maps monomorphically to `G`.

The first map is sheafification of the inclusion of the abelian image of the
underlying presheaf morphism. The second map identifies the sheafification of
the already-sheaf `G` with `G`. -/
theorem imageSheafification_mono
    {X : TopCat.{u}} {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (φ : F ⟶ G) :
    Mono
      ((presheafToSheaf
          (Opens.grothendieckTopology X)
          AddCommGrpCat.{u}).map (Abelian.image.ι φ.hom) ≫
        (sheafificationIso G).inv) := by
  apply mono_comp'
  · exact preserves_mono_of_preservesLimit _ _
  · let e := sheafificationIso G
    change Mono e.inv
    exact ({ retraction := e.hom, id := e.inv_hom_id } : SplitMono e.inv).mono

end

end Hartshorne

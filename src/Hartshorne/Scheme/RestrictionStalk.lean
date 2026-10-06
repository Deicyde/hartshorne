/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Sheaves.AddCommGrpCat
import Mathlib.Topology.Sheaves.Sheafify

/-!
# Stalks of inverse-image sheaves

Hartshorne, *Algebraic Geometry*, II.1 (p. 65).

The stalk of an inverse-image sheaf at a point is canonically isomorphic to the stalk of the
original sheaf at the image point. In particular, restriction to a subspace preserves stalks.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Hartshorne

universe u

/-- The canonical isomorphism from the stalk of an inverse-image sheaf to the original stalk.

The first factor compares Mathlib's sheaf pullback with the sheafification of the presheaf
pullback. The second removes sheafification from the stalk, and the third is the inverse of the
presheaf-level stalk-pullback isomorphism. -/
noncomputable def restrictionStalkIso
    {X Y : TopCat.{u}} (f : X ⟶ Y) (F : Y.Sheaf AddCommGrpCat.{u}) (x : X) :
    ((TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj F).presheaf.stalk x ≅
      F.presheaf.stalk (f x) := by
  let P := (TopCat.Presheaf.pullback AddCommGrpCat.{u} f).obj F.presheaf
  letI := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
    x AddCommGrpCat.{u} P
  exact
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso
      ((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapIso
        ((TopCat.Sheaf.pullbackIso AddCommGrpCat.{u} f).app F)) ≪≫
    (asIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (toSheafify (Opens.grothendieckTopology X) P))).symm ≪≫
      (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} f F.presheaf x).symm

/-- **Hartshorne II.1.** There is a canonical isomorphism from the stalk of an inverse-image
sheaf to the original stalk at the image point. Its forward map is the canonical comparison
constructed by `restrictionStalkIso`. -/
theorem exists_restrictionStalkIso
    {X Y : TopCat.{u}} (f : X ⟶ Y) (F : Y.Sheaf AddCommGrpCat.{u}) (x : X) :
    ∃ e : ((TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj F).presheaf.stalk x ≅
        F.presheaf.stalk (f x),
      e.hom = (restrictionStalkIso f F x).hom :=
  ⟨restrictionStalkIso f F x, rfl⟩

end Hartshorne

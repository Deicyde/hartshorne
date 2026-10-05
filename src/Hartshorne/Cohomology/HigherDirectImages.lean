/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.AbelianPushforwardLeftExact
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Higher direct images of abelian sheaves

Hartshorne, *Algebraic Geometry*, III.8, p. 250.

The `i`-th higher direct image along a continuous map is the `i`-th right
derived functor of direct image. In degree zero it is naturally isomorphic to
ordinary direct image.
-/

open CategoryTheory

universe u

namespace Hartshorne

noncomputable local instance {X Y : TopCat.{u}} (f : X ⟶ Y) :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The `i`-th higher direct image functor for sheaves of abelian groups. -/
noncomputable def abelianHigherDirectImage
    {X Y : TopCat.{u}} (f : X ⟶ Y) (i : ℕ) :
    TopCat.Sheaf AddCommGrpCat.{u} X ⥤
      TopCat.Sheaf AddCommGrpCat.{u} Y :=
  (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).rightDerived i

/-- The degree-zero higher direct image is naturally isomorphic to ordinary
direct image. -/
noncomputable def abelianHigherDirectImageZeroIso
    {X Y : TopCat.{u}} (f : X ⟶ Y) :
    abelianHigherDirectImage f 0 ≅
      TopCat.Sheaf.pushforward AddCommGrpCat.{u} f :=
  Functor.rightDerivedZeroIsoSelf _

end Hartshorne

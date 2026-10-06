/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Data.ZMod.Basic

/-!
# Constant torsion sheaves on the small étale site

For a scheme `X`, this file defines the constant abelian sheaf with value
`ZMod (ℓ ^ r)` on the small étale site and its reduction maps as `r`
increases.  The construction makes sense without primality or invertibility
hypotheses; those assumptions enter the later theorems about ℓ-adic
cohomology.

We index by every natural number.  At `r = 0` the coefficient group is
`ZMod (ℓ ^ 0) = ZMod 1`, the trivial group, which is the harmless zeroth
stage of the inverse system indexed by positive powers in Hartshorne.
-/

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

/-- The constant sheaf with value `ZMod (ℓ ^ r)` on the small étale site of
`X`, obtained by sheafifying the constant presheaf. -/
noncomputable def constantTorsionEtaleSheaf
    (X : Scheme.{u}) (ℓ r : ℕ) :
    Sheaf X.smallEtaleTopology Ab.{u} :=
  (constantSheaf X.smallEtaleTopology Ab.{u}).obj
    ((AddCommGrpCat.uliftFunctor.{u}).obj
      (AddCommGrpCat.of (ZMod (ℓ ^ r))))

/-- Reduction modulo `ℓ ^ r` gives the transition from the constant
`ZMod (ℓ ^ s)` sheaf to the constant `ZMod (ℓ ^ r)` sheaf when `r ≤ s`. -/
noncomputable def constantTorsionEtaleSheafReduction
    (X : Scheme.{u}) (ℓ : ℕ) {r s : ℕ} (h : r ≤ s) :
    X.constantTorsionEtaleSheaf ℓ s ⟶
      X.constantTorsionEtaleSheaf ℓ r :=
  (constantSheaf X.smallEtaleTopology Ab.{u}).map
    ((AddCommGrpCat.uliftFunctor.{u}).map
      (AddCommGrpCat.ofHom
        (ZMod.castHom (pow_dvd_pow ℓ h)
          (ZMod (ℓ ^ r))).toAddMonoidHom))

end AlgebraicGeometry.Scheme

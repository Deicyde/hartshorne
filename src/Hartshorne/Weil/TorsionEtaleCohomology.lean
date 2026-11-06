/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Weil.ConstantTorsionEtaleSheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Sites.GlobalSections

/-!
# Torsion étale cohomology

For a scheme `X : Scheme.{u}`, the category `Sheaf X.smallEtaleTopology Ab.{u}`
of abelian sheaves on the small étale site is a Grothendieck abelian category
(Mathlib, via the essentially small affine étale site), so it has enough
injectives and hence injective resolutions.  The global sections functor
`Sheaf.Γ` (the right adjoint of the constant sheaf functor) is additive, and we
define `H^i_et(X, ℤ/ℓ^r)` as its `i`-th right derived functor evaluated at the
constant sheaf `ZMod (ℓ ^ r)`.

## Universes

The sheaf category has morphisms in `Type (u + 1)`, because the small étale
site `X.Etale` is a large category, but the global sections functor lands in
`Ab.{u}`, so the cohomology groups are `u`-small abelian groups.
-/

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

universe u

/-- The global sections functor on abelian sheaves on the small étale site is
additive: it is a right adjoint, so it preserves binary products. -/
instance additive_sheafΓ_smallEtaleTopology (X : Scheme.{u}) :
    (Sheaf.Γ X.smallEtaleTopology Ab.{u}).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Torsion étale cohomology `H^i_et(X, ℤ/ℓ^r)`: the `i`-th right derived
functor of global sections on abelian sheaves on the small étale site of `X`,
evaluated at the constant sheaf `ZMod (ℓ ^ r)`. -/
noncomputable def torsionEtaleCohomology (X : Scheme.{u}) (ℓ r i : ℕ) : Ab.{u} :=
  ((Sheaf.Γ X.smallEtaleTopology Ab.{u}).rightDerived i).obj
    (X.constantTorsionEtaleSheaf ℓ r)

end AlgebraicGeometry.Scheme

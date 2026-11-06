/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# The reduced induced closed subscheme

Hartshorne, *Algebraic Geometry*, II.3, Example 3.2.6 (p. 86).

For a closed subset `Z` of a scheme `X`, the vanishing ideal sheaf of `Z`
(on an affine open `U`, the ideal of sections of `𝒪_X(U)` lying in every prime
of `Z ∩ U`) defines a closed subscheme of `X`. On an affine open `U` it is
`Spec (𝒪_X(U) / I(U))`, and these affine pieces are glued; this is Mathlib's
`AlgebraicGeometry.Scheme.IdealSheafData.subscheme` applied to
`AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal`.

We record:

* `Hartshorne.reducedInducedSubscheme Z`: the reduced induced closed subscheme on `Z`;
* `Hartshorne.reducedInducedSubschemeι Z`: its closed immersion into `X`;
* `Hartshorne.ker_reducedInducedSubschemeι`: its ideal sheaf is the vanishing ideal of `Z`;
* `Hartshorne.range_reducedInducedSubschemeι`: its underlying set is exactly `Z`;
* `Hartshorne.isReduced_reducedInducedSubscheme`: it is reduced, since each affine
  piece is the spectrum of a quotient by a radical ideal.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hartshorne

universe u

variable {X : Scheme.{u}}

/-- The reduced induced closed subscheme on a closed subset `Z` of a scheme `X`: the closed
subscheme cut out by the vanishing ideal sheaf of `Z`. -/
noncomputable def reducedInducedSubscheme (Z : Closeds X) : Scheme.{u} :=
  (Scheme.IdealSheafData.vanishingIdeal Z).subscheme

/-- The inclusion of the reduced induced closed subscheme on `Z` into `X`. -/
noncomputable def reducedInducedSubschemeι (Z : Closeds X) : reducedInducedSubscheme Z ⟶ X :=
  (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι

/-- The inclusion of the reduced induced closed subscheme is a closed immersion. -/
instance isClosedImmersion_reducedInducedSubschemeι (Z : Closeds X) :
    IsClosedImmersion (reducedInducedSubschemeι Z) :=
  inferInstanceAs (IsClosedImmersion (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι)

/-- The ideal sheaf of the reduced induced closed subscheme on `Z` is the vanishing ideal
sheaf of `Z`. -/
theorem ker_reducedInducedSubschemeι (Z : Closeds X) :
    (reducedInducedSubschemeι Z).ker = Scheme.IdealSheafData.vanishingIdeal Z :=
  Scheme.IdealSheafData.ker_subschemeι _

/-- The reduced induced closed subscheme on `Z` is supported exactly on `Z`. -/
theorem range_reducedInducedSubschemeι (Z : Closeds X) :
    Set.range (reducedInducedSubschemeι Z) = (Z : Set X) :=
  (Scheme.IdealSheafData.range_subschemeι _).trans
    (Scheme.IdealSheafData.coe_support_vanishingIdeal Z)

/-- The reduced induced closed subscheme is reduced. -/
instance isReduced_reducedInducedSubscheme (Z : Closeds X) :
    IsReduced (reducedInducedSubscheme Z) := by
  have (U : X.affineOpens) : IsReduced
      ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeCover.openCover.X U) := by
    have : _root_.IsReduced
        (Γ(X, U) ⧸ (Scheme.IdealSheafData.vanishingIdeal Z).ideal U) :=
      (Ideal.isRadical_iff_quotient_reduced _).mp
        (by
          rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
          exact PrimeSpectrum.isRadical_vanishingIdeal _)
    change IsReduced (Spec (.of (Γ(X, U) ⧸ (Scheme.IdealSheafData.vanishingIdeal Z).ideal U)))
    infer_instance
  change IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme
  exact @IsReduced.of_openCover _ (Scheme.IdealSheafData.vanishingIdeal Z).subschemeCover.openCover
    this

end Hartshorne

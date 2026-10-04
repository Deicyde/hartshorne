/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Restricting a fiber product to an open subscheme

Hartshorne, *Algebraic Geometry*, II.3, Theorem 3.3 (pp. 87–88).

The inverse-image open subscheme of the first projection from a fiber product
represents the fiber product after restricting the first factor. The proof is
the vertical pasting of the pullback square defining morphism restriction with
the chosen categorical pullback square.
-/

namespace Hartshorne

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

/-- If `X ×_S Y` is restricted to the inverse image of an open subscheme
`U ⊆ X` under its first projection, the resulting scheme represents
`U ×_S Y`. -/
theorem isPullback_fiberProductRestrictOpen
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (U : X.Opens) :
    IsPullback ((pullback.fst f g) ∣_ U)
      (((pullback.fst f g) ⁻¹ᵁ U).ι ≫ pullback.snd f g)
      (U.ι ≫ f) g :=
  (isPullback_morphismRestrict (pullback.fst f g) U).paste_vert
    (IsPullback.of_hasPullback f g)

end Hartshorne

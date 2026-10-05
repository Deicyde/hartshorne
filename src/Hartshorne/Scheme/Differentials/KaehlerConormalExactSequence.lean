/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Kaehler.Basic

/-!
# The conormal exact sequence

Hartshorne, *Algebraic Geometry*, II.8, Proposition 8.4A (p. 173).

For a tower of commutative rings `A → B → C` in which `B → C` is
surjective, the canonical sequence

`ker(B → C) / ker(B → C)² → C ⊗[B] Ω[B⁄A] → Ω[C⁄A] → 0`

is right exact. Taking `C = B/I` gives the usual sequence for a quotient by
an ideal `I`. No injectivity assertion is made at the left end.

## Main result

* `Hartshorne.kaehlerConormal_rightExact`
-/

namespace Hartshorne

noncomputable section

/-- **Hartshorne II.8, Proposition 8.4A.** For a surjective map `B → C`, the
conormal sequence is exact at `C ⊗[B] Ω[B⁄A]` and surjective onto
`Ω[C⁄A]`. In particular this applies to `C = B/I`. -/
theorem kaehlerConormal_rightExact
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (h : Function.Surjective (algebraMap B C)) :
    Function.Exact
        (KaehlerDifferential.kerCotangentToTensor A B C)
        (KaehlerDifferential.mapBaseChange A B C) ∧
      Function.Surjective (KaehlerDifferential.mapBaseChange A B C) :=
  ⟨KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange A B C h,
    KaehlerDifferential.mapBaseChange_surjective A B C h⟩

end

end Hartshorne

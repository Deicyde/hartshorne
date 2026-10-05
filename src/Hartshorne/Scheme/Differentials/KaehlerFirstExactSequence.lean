/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Kaehler.Basic

/-!
# The first exact sequence for Kahler differentials

Hartshorne, *Algebraic Geometry*, II.8, Proposition 8.3A (p. 173).

For a tower of commutative rings `A -> B -> C`, the natural sequence

`C ⊗[B] Ω[B⁄A] → Ω[C⁄A] → Ω[C⁄B] → 0`

is exact.
-/

namespace Hartshorne

universe u v w

/-- **Hartshorne II.8, Proposition 8.3A.** The first exact sequence for Kahler
differentials is right exact. -/
theorem kaehlerFirstExactSequence
    (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [IsScalarTower A B C] :
    Function.Exact
        (KaehlerDifferential.mapBaseChange A B C)
        (KaehlerDifferential.map A B C C) ∧
      Function.Surjective (KaehlerDifferential.map A B C C) :=
  ⟨KaehlerDifferential.exact_mapBaseChange_map A B C,
    KaehlerDifferential.map_surjective A B C⟩

end Hartshorne

/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Affine.Zariski

/-!
# The vanishing ideal

Hartshorne, *Algebraic Geometry*, I.1, Proposition 1.2 (p. 3).

Mathlib supplies `MvPolynomial.vanishingIdeal` together with parts (a), (b) and
the Galois connection between `Z` and `I`; see `zeroLocus_anti_mono`,
`vanishingIdeal_anti_mono` and `zeroLocus_vanishingIdeal_galoisConnection`. Part
(d), `I(Z(𝔞)) = √𝔞`, is the Nullstellensatz and is handled separately.

What is left, and what needs the Zariski topology from the previous file, is
part (c) and part (e): `I` turns unions into intersections, and `Z ∘ I` is the
closure operator.

## Main results

* `Hartshorne.vanishingIdeal_union` : Hartshorne 1.2(c).
* `Hartshorne.zeroLocus_vanishingIdeal_eq_closure` : Hartshorne 1.2(e).
-/

namespace Hartshorne

open MvPolynomial

variable {k : Type*} [Field k] {σ : Type*}

/-- Zero loci of ideals are Zariski closed. -/
theorem isClosed_zeroLocus (I : Ideal (MvPolynomial σ k)) :
    IsClosed (zeroLocus k I) :=
  isClosed_iff_isAlgebraicSet.2 (isAlgebraicSet_iff_exists_ideal.2 ⟨I, rfl⟩)

/-- Hartshorne 1.2(c): `I(Y₁ ∪ Y₂) = I(Y₁) ∩ I(Y₂)`. -/
theorem vanishingIdeal_union (Y₁ Y₂ : Set (σ → k)) :
    vanishingIdeal k (Y₁ ∪ Y₂) = vanishingIdeal k Y₁ ⊓ vanishingIdeal k Y₂ := by
  ext f
  simp only [mem_vanishingIdeal_iff, Ideal.mem_inf, Set.mem_union]
  exact ⟨fun h => ⟨fun x hx => h x (Or.inl hx), fun x hx => h x (Or.inr hx)⟩,
    fun ⟨h₁, h₂⟩ x hx => hx.elim (h₁ x) (h₂ x)⟩

/-- Hartshorne 1.2(e): `Z(I(Y))` is the Zariski closure of `Y`.

So `Z ∘ I` is the closure operator of the topology, and the algebraic sets are
exactly its fixed points. -/
theorem zeroLocus_vanishingIdeal_eq_closure (Y : Set (σ → k)) :
    zeroLocus k (vanishingIdeal k Y) = closure Y := by
  refine le_antisymm ?_ (closure_minimal (zeroLocus_vanishingIdeal_le Y)
    (isClosed_zeroLocus _))
  calc zeroLocus k (vanishingIdeal k Y)
      ≤ zeroLocus k (vanishingIdeal k (closure Y)) :=
        zeroLocus_anti_mono (vanishingIdeal_anti_mono subset_closure)
    _ = closure Y :=
        (isClosed_iff_isAlgebraicSet.1 isClosed_closure).zeroLocus_vanishingIdeal

/-- An algebraic set is closed and equals the zero locus of its own vanishing
ideal, so the closure operator fixes it. -/
theorem IsAlgebraicSet.closure_eq {Y : Set (σ → k)} (h : IsAlgebraicSet Y) :
    closure Y = Y := by
  rw [← zeroLocus_vanishingIdeal_eq_closure, h.zeroLocus_vanishingIdeal]

end Hartshorne

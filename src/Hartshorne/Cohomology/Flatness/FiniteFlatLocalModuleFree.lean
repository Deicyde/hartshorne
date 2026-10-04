/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.LocalRing.Module

/-!
# Finite flat modules over local rings

Hartshorne, *Algebraic Geometry*, III.9, Proposition 9.1A(f) (p. 254).

For a Noetherian local ring, a finite module is flat if and only if it is free.
-/

namespace Hartshorne

universe u v

/-- **Hartshorne III.9, Proposition 9.1A(f).** A finite module over a Noetherian local ring is
flat if and only if it is free. -/
theorem finiteFlat_iff_free
    (R : Type u) (M : Type v)
    [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Module.Flat R M ↔ Module.Free R M := by
  constructor
  · intro h
    let _ : Module.Flat R M := h
    exact Module.free_of_flat_of_isLocalRing
  · intro h
    let _ : Module.Free R M := h
    exact Module.Flat.of_free

end Hartshorne

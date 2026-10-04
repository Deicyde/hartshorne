/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Flat.Localization

/-!
# Flatness is local on prime localizations

Hartshorne, *Algebraic Geometry*, III.9, Proposition 9.1A(d) (pp. 253–254).

This file records the source-shaped equivalence between flatness of a module
and flatness of all its localizations at prime ideals.
-/

namespace Hartshorne

/-- **Hartshorne III.9, Proposition 9.1A(d).** An `R`-module is flat if and only
if its localization at every prime ideal is flat over the corresponding
localized ring. -/
theorem flat_iff_localizedModule_atPrime
    {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] :
    Module.Flat R M ↔
      ∀ (p : Ideal R) [p.IsPrime],
        Module.Flat (Localization.AtPrime p) (LocalizedModule p.primeCompl M) := by
  constructor
  · intro h p hp
    exact @Module.Flat.localizedModule R M _ _ _ h p.primeCompl
  · intro h
    apply Module.flat_of_localized_maximal
    intro p
    exact (Module.flat_iff_of_isLocalization
      (Localization.AtPrime p) p.primeCompl (LocalizedModule p.primeCompl M)).mp (h p)

end Hartshorne

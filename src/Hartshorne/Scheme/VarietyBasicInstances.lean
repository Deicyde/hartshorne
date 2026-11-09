/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.FiniteType
import Hartshorne.Scheme.Regular
import Hartshorne.Scheme.RegularLocalFactorial

/-!
# Basic properties of schemes over a field

A scheme of finite type over a field is Noetherian; a scheme separated over a field is separated;
a regular scheme is locally factorial.
-/

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace Hartshorne

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- A scheme of finite type over a field is Noetherian. -/
theorem isNoetherian_of_finiteType (p : X ⟶ Spec (.of k)) (hp : FiniteType p) :
    IsNoetherian X := by
  have := hp.1
  have := hp.2
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  exact {}

/-- A scheme separated over a field is separated. -/
theorem isSeparated_of_isSeparated_spec (p : X ⟶ Spec (.of k)) [IsSeparated p] : X.IsSeparated :=
  ⟨by rw [← terminal.comp_from p]; infer_instance⟩

/-- A regular scheme is locally factorial. -/
theorem isLocallyFactorial_of_isRegular (hreg : X.IsRegular) : X.IsLocallyFactorial :=
  X.isLocallyFactorial_of_isRegularLocalRing hreg.2

end Hartshorne

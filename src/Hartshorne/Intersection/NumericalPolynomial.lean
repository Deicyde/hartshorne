/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Order.Filter.AtTopBot.Defs

/-!
# Numerical polynomials

Hartshorne, *Algebraic Geometry*, I.7, definition before Proposition 7.3
(p. 49).

A rational polynomial is numerical when its value at every sufficiently large
integer is an integer. The quantifier over sufficiently large integers is
represented by the `atTop` filter on `ℤ`.
-/

namespace Hartshorne

open scoped Polynomial

/-- A polynomial over `ℚ` is numerical when it takes integer values at all
sufficiently large integers. -/
def IsNumericalPolynomial (P : ℚ[X]) : Prop :=
  ∀ᶠ n : ℤ in Filter.atTop, ∃ m : ℤ, P.eval (n : ℚ) = (m : ℚ)

end Hartshorne

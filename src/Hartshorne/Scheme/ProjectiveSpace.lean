/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Projective space as a scheme

Hartshorne, *Algebraic Geometry*, II.2, Example 2.5.1 (p. 77).

This file defines projective `n`-space over a commutative ring as the projective
spectrum of the polynomial ring in `n + 1` variables with its standard
total-degree grading.  The name is deliberately distinct from
`Hartshorne.ProjectiveSpace`, the project's type of classical projective points
over a field.
-/

namespace Hartshorne

universe u

/-- Projective `n`-space over a commutative ring `A`, as the scheme
`Proj A[x₀, ..., xₙ]` with the standard total-degree grading. -/
noncomputable def projectiveSpaceScheme (A : Type u) [CommRing A] (n : ℕ) :
    AlgebraicGeometry.Scheme.{u} :=
  letI := MvPolynomial.gradedAlgebra (σ := Fin (n + 1)) (R := A)
  AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)

end Hartshorne

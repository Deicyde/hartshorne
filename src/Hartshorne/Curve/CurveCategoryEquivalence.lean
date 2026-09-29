/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Curve.ProjectiveQuasiProjectiveCurveEquivalence
import Hartshorne.Curve.QuasiProjectiveCurveFunctionFieldEquivalence

/-!
# Projective curves and one-dimensional function fields

Hartshorne, *Algebraic Geometry*, I.6, Corollary 6.12 (pp. 45--46).

Passing from a nonsingular projective curve to its quasi-projective
presentation and then taking its function field gives the contravariant
equivalence with one-dimensional function fields.  The forward functor is the
canonical pullback on function fields; the quasi-inverse is not fixed
definitionally.
-/

namespace Hartshorne

open CategoryTheory

noncomputable section

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- **Hartshorne I.6, Corollary 6.12.** Nonsingular projective curves with
dominant morphisms are contravariantly equivalent to one-dimensional function
fields with `k`-homomorphisms. -/
noncomputable def projectiveCurveFunctionFieldEquivalence :
    (ProjectiveNonsingularCurveCat k)ᵒᵖ ≌ OneDimensionalFunctionFieldCat k :=
  (projectiveQuasiProjectiveCurveEquivalence (k := k)).op.trans
    (quasiProjectiveCurveFunctionFieldEquivalence (k := k))

end

end Hartshorne

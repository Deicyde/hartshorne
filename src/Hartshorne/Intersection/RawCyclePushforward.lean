/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.ResidueField
import Hartshorne.Intersection.CodimensionCycles

/-!
# Raw pushforward of cycles (partial)

Hartshorne, *Algebraic Geometry*, Appendix A.1 (pp. 425–426).

Cycles are represented as in `Hartshorne.codimensionCycles`: an irreducible closed subset `Y` of a
scheme is recorded by its generic point `x`, so `Y = closure {x}`. For a morphism `f : X ⟶ X'`,
the closure of `f(Y)` is then `closure {f x}`, and its function field, like that of `Y`, is the
residue field at its generic point (the stalk of the reduced induced structure at the generic point
is the residue field). Hence `[K(Y) : K(closure f(Y))]` is the degree of the residue field
extension `κ(f x) → κ(x)`, which is `Hom.residueDegree f x`.

This file contains the generator-level definition and the linear extension to finitely supported
cycles of a fixed codimension, with values in all algebraic cycles of the target. The codimension
reindexing `r ↦ r + dim X' - dim X` of the target is not yet formalized.
-/

namespace Hartshorne

open AlgebraicGeometry

variable {X X' : Scheme}

open scoped Classical in
/-- The coefficient of `f_*[Y]` for `Y = closure {x}`: zero if the closure of `f(Y)` has smaller
dimension than `Y`, and otherwise the degree `[κ(x) : κ(f x)]` of the function field extension. -/
noncomputable def rawCyclePushforwardCoeff (f : X ⟶ X') (x : X) : ℤ :=
  if topologicalKrullDim (closure (f.base '' closure ({x} : Set X))) <
      topologicalKrullDim (closure ({x} : Set X)) then 0
  else f.residueDegree x

/-- The closure of the image of `closure {x}` is the closure of `{f x}`. -/
lemma rawCyclePushforward_closure_image_eq (f : X ⟶ X') (x : X) :
    closure (f.base '' closure ({x} : Set X)) = closure {f.base x} := by
  rw [closure_image_closure f.base.hom.continuous, Set.image_singleton]

open scoped Classical in
/-- The raw pushforward `f_*[Y]` of the cycle of `Y = closure {x}`: the coefficient
`rawCyclePushforwardCoeff f x` times the cycle of `closure {f x}`. -/
noncomputable def rawCyclePushforwardGenerator (f : X ⟶ X') (x : X) : AlgebraicCycle X' ℤ :=
  Function.locallyFinsuppWithin.single (f.base x) (rawCyclePushforwardCoeff f x)

/-- A finitely supported codimension-`r` cycle viewed as a finitely supported function. -/
noncomputable def codimensionCyclesToFinsupp (r : ℕ) : codimensionCycles X r →+ (X →₀ ℤ) where
  toFun c := Finsupp.ofSupportFinite (c : AlgebraicCycle X ℤ) c.2.1
  map_zero' := by ext; rfl
  map_add' _ _ := by ext; rfl

/-- The raw pushforward of codimension-`r` cycles, extended linearly from
`rawCyclePushforwardGenerator`, with values in all algebraic cycles of the target. -/
noncomputable def rawCyclePushforwardUngraded (f : X ⟶ X') (r : ℕ) :
    codimensionCycles X r →+ AlgebraicCycle X' ℤ :=
  (Finsupp.liftAddHom fun x => zmultiplesHom _ (rawCyclePushforwardGenerator f x)).comp
    (codimensionCyclesToFinsupp r)

lemma rawCyclePushforwardUngraded_apply (f : X ⟶ X') (r : ℕ) (c : codimensionCycles X r) :
    rawCyclePushforwardUngraded f r c =
      ∑ x ∈ c.2.1.toFinset, (c : AlgebraicCycle X ℤ) x • rawCyclePushforwardGenerator f x := by
  simp only [rawCyclePushforwardUngraded, AddMonoidHom.comp_apply, Finsupp.liftAddHom_apply]
  rfl

end Hartshorne

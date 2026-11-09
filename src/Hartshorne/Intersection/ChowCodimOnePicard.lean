/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.ChowGroups
import Hartshorne.Intersection.RationalEquivalenceCodimOne
import Hartshorne.Scheme.LocallyFactorialClassPicard
import Hartshorne.Scheme.Regular
import Hartshorne.Scheme.RegularLocalFactorial
import Hartshorne.Scheme.VarietyBasicInstances

/-!
# Codimension-one Chow classes are the Picard group

Hartshorne, *Algebraic Geometry*, Appendix A.2, A8 (p. 428).

Let `X` be a nonsingular variety over a field `k` (an integral regular scheme, separated and of
finite type over `k`). Then the divisor-to-line-bundle map induces an isomorphism
`A^1(X) ≅ Pic X`. Hartshorne states this for quasi-projective `X`; the argument does not use
quasi-projectivity.

## Proof

`X` is normal, so codimension-one rational equivalence is linear equivalence and
`A^1(X) ≅ Cl X`; `X` is regular, hence locally factorial, so `Cl X ≅ Pic X` by
`D ↦ O_X(D)` (Corollary II.6.16).

## Main results

* `Hartshorne.chowGroupOneEquivPicard`: `A^1(X) ≃+ Pic X` (written additively).
* `Hartshorne.chowGroupOneEquivPicard_mk`: the class of a Weil divisor `D` goes to the class of
  `O_X(D)`.
-/

universe u

open AlgebraicGeometry CategoryTheory Limits Hartshorne.Ringed

namespace Hartshorne

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- **Hartshorne, Appendix A.2, A8.** On a nonsingular variety `X` over a field `k` (an integral
regular scheme, separated and of finite type over `k`, of dimension `n`), the divisor-to-line-bundle
map induces an isomorphism `A^1(X) ≅ Pic X`, written additively. Hartshorne assumes `X`
quasi-projective; the construction does not use it. -/
def chowGroupOneEquivPicard (p : X ⟶ Spec (.of k)) [IsIntegral X] (hp : FiniteType p)
    [IsSeparated p] {n : ℕ} (hn : topologicalKrullDim X = n) (hreg : X.IsRegular) :
    chowGroup p hp hn 1 ≃+ Additive (Pic X.sheaf) :=
  have := finiteType_isNoetherian p hp
  have := isSeparated_of_isSeparated_spec p
  have := Scheme.isNormal_of_isLocallyFactorial (isLocallyFactorial_of_isRegular hreg)
  (codimOneCycleClassEquivWeilClassGroup p hp hn).trans
    (Scheme.weilClassEquivPicard (isLocallyFactorial_of_isRegular hreg))

/-- The isomorphism `A^1(X) ≅ Pic X` sends the class of a Weil divisor `D`, viewed as a
codimension-one cycle, to the class of `O_X(D)`, where `D` is viewed as a Cartier divisor. -/
theorem chowGroupOneEquivPicard_mk (p : X ⟶ Spec (.of k)) [IsIntegral X] (hp : FiniteType p)
    [IsSeparated p] {n : ℕ} (hn : topologicalKrullDim X = n) (hreg : X.IsRegular)
    (D : X.WeilDivisor) :
    have := finiteType_isNoetherian p hp
    have := isSeparated_of_isSeparated_spec p
    have := Scheme.isNormal_of_isLocallyFactorial (isLocallyFactorial_of_isRegular hreg)
    chowGroupOneEquivPicard p hp hn hreg
        (weilDivisorToCodimOneCycles (satisfiesConditionStar_of_isNormal_of_finiteType p hp) D :
          chowGroup p hp hn 1) =
      X.cartierDivisorToPicard
        (Scheme.weilCartierEquiv (isLocallyFactorial_of_isRegular hreg) D) := by
  intro _ _ _
  rw [chowGroupOneEquivPicard, AddEquiv.trans_apply, codimOneCycleClassEquivWeilClassGroup_mk]
  exact Scheme.weilClassEquivPicard_weilDivisorClassHom _ D

end

end Hartshorne

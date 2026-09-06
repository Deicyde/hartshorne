/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.GlobalRegularFunctionField
import Hartshorne.Morphism.ProjFunctionField

/-!
# Reading a global regular function on a chart

Toward Hartshorne, *Algebraic Geometry*, I.3, Theorem 3.4(a).

For `Y` projective meeting the chart `Uᵢ`, the image of a global regular
function in `K(Y)` lies in the image of `A(Yᵢ)`.

This is the sentence "`f` is regular on `Yᵢ`, so `f ∈ A(Yᵢ)`" that Hartshorne's
proof of 3.4(a) opens with. Formally it is a chase along the three isomorphisms
that identify `K(Y)` with the function field of the affine chart, checking at
each step that a global regular function stays a global regular function.

Nothing here is deep, and nothing here was available from parts (b) and (c):
they moved *one* ring across the chart isomorphism, whereas this moves an
element and has to know where it lands.

## Main results

* `Hartshorne.exists_coordToRational_eq_of_globalRegular`
-/

namespace Hartshorne

open MvPolynomial TopologicalSpace

variable {k : Type*} [Field k] [IsAlgClosed k] {σ : Type*} [Finite σ] [DecidableEq σ]
  [Nonempty σ] {Y : Set (ProjectiveSpace k σ)} (hY : IsProjVariety Y) (i : σ)
  (hne : (Y ∩ standardChart i).Nonempty)

omit [IsAlgClosed k] [Finite σ] [DecidableEq σ] [Nonempty σ] in
/-- Restriction to the chart piece sends a global regular function to one. -/
theorem restrictFunctionFieldEquiv_globalToFunctionField
    (f : (Variety.ofQuasiProjective hY.isQuasiProjVariety).globalRegular) :
    restrictFunctionFieldEquiv hY i hne (Variety.globalToFunctionField _ f)
      = Variety.globalToFunctionField _
        ((inclHom hY.isQuasiProjVariety
          (isQuasiProjVariety_inter_standardChart k i hY.isQuasiProjVariety hne)
          Set.inter_subset_left).globalPullback f) :=
  VarietyHom.functionFieldHom_globalToFunctionField _ _ f

/-- And so does transport backwards along the chart isomorphism, because the
inverse morphism pulls it back. -/
theorem chartFunctionFieldEquiv_symm_globalToFunctionField
    (g : (Variety.ofQuasiProjective
      (isQuasiProjVariety_inter_standardChart k i hY.isQuasiProjVariety hne)).globalRegular) :
    (chartFunctionFieldEquiv hY i hne).symm (Variety.globalToFunctionField _ g)
      = Variety.globalToFunctionField _
        ((chartInvHom k i hY.isQuasiProjVariety hne).globalPullback g) := by
  rw [RingEquiv.symm_apply_eq, chartFunctionFieldEquiv_apply,
    VarietyHom.functionFieldHom_globalToFunctionField,
    ← VarietyHom.globalPullback_comp, chartInvHom_comp_chartHom]
  rfl

include hY hne in
/-- **A global regular function is read on the chart as an element of
`A(Yᵢ)`.**

The three steps are: restrict to `Yᵢ`, pull back along the inverse chart map,
and read the resulting global regular function on the affine chart through
Theorem 3.2(a). Each step keeps a global regular function global, which is the
only thing that needs checking. -/
theorem exists_coordToRational_eq_of_globalRegular
    (f : (Variety.ofQuasiProjective hY.isQuasiProjVariety).globalRegular) :
    ∃ a : coordinateRing (chartMap i '' (Y ∩ standardChart i)),
      coordToRational
          (isQuasiAffineVariety_chartMap_image i hY.isQuasiProjVariety hne).isIrreducible a
        = projFunctionFieldEquiv hY i hne (Variety.globalToFunctionField _ f) := by
  refine ⟨(coordinateRingEquivRegularTop
    (isAffineVariety_chartMap_image i hY hne)).symm
      ((chartInvHom k i hY.isQuasiProjVariety hne).globalPullback
        ((inclHom hY.isQuasiProjVariety
          (isQuasiProjVariety_inter_standardChart k i hY.isQuasiProjVariety hne)
          Set.inter_subset_left).globalPullback f)), ?_⟩
  rw [projFunctionFieldEquiv_apply, restrictFunctionFieldEquiv_globalToFunctionField,
    chartFunctionFieldEquiv_symm_globalToFunctionField]
  refine (coordToRational_eq_globalToFunctionField
    (isAffineVariety_chartMap_image i hY hne) _).trans ?_
  exact congrArg _ (congrArg _ (AlgEquiv.apply_symm_apply _ _))

end Hartshorne

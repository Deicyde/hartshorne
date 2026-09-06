/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.GlobalRegularFunctionField
import Hartshorne.Morphism.ChartIso
import Hartshorne.Morphism.OpenSubvariety
import Hartshorne.Projective.Homogenize

/-!
# A global regular function is a ratio of forms on each chart

Toward Hartshorne, *Algebraic Geometry*, I.3, Theorem 3.4(a).

For `Y` projective meeting the chart `Uᵢ` and `f` a global regular function on
`Y`, there are `N` and a form `g` of degree `N` with

`f(P) · xᵢ(P)^N = g(P)` for every `P ∈ Y ∩ Uᵢ`.

This is a *pointwise* statement, and that is the point of it. The same fact was
proved earlier as a statement inside the function field, but there it was phrased
through the identification `K(Y) ≅ S(Y)_((0))`, which is built one chart at a
time; readings on different charts were then incomparable, which is exactly what
Theorem 3.4(a) needs to do. Pointwise there is nothing to compare: the values of
`f` are what they are.

The route is short. Theorem 3.2(a) on the affine chart says the transported
function is `p` for a polynomial `p` in the affine coordinates, and
`eval_homogenize` converts that into a homogeneous statement upstairs, the
factor `xᵢ^N` being exactly the discrepancy between evaluating a polynomial and
its homogenisation.

## Main results

* `Hartshorne.exists_homogeneous_repr_of_globalRegular`
-/

namespace Hartshorne

open MvPolynomial TopologicalSpace

variable {k : Type*} [Field k] [IsAlgClosed k] {σ : Type*} [Finite σ] [DecidableEq σ]
  [Nonempty σ] {Y : Set (ProjectiveSpace k σ)}

omit [DecidableEq σ] [Nonempty σ] in
/-- Theorem 3.2(a) computes pointwise: the global regular function attached to a
polynomial class is evaluation at the point. -/
theorem coordinateRingEquivRegularTop_apply {i : σ} {Z : Set ({j : σ // j ≠ i} → k)}
    (hZ : IsAffineVariety Z) (a : coordinateRing Z)
    (z : (⊤ : Opens Z)) :
    (coordinateRingEquivRegularTop hZ a).1 z = evalAt Z z.1 a :=
  coordinateToRegular_apply a z.1

/-- **A global regular function is a ratio of forms on each chart.** -/
theorem exists_homogeneous_repr_of_globalRegular (hY : IsProjVariety Y) (i : σ)
    (hne : (Y ∩ standardChart i).Nonempty)
    (f : (Variety.ofQuasiProjective hY.isQuasiProjVariety).globalRegular) :
    ∃ (N : ℕ) (g : MvPolynomial σ k), g.IsHomogeneous N ∧
      ∀ (P : ProjectiveSpace k σ) (hPY : P ∈ Y), P ∈ standardChart i →
        f.1 ⟨⟨P, hPY⟩, trivial⟩ * P.rep i ^ N = eval P.rep g := by
  have hW' := isAffineVariety_chartMap_image i hY hne
  set fW := (chartInvHom k i hY.isQuasiProjVariety hne).globalPullback
    ((inclHom hY.isQuasiProjVariety
      (isQuasiProjVariety_inter_standardChart k i hY.isQuasiProjVariety hne)
      Set.inter_subset_left).globalPullback f) with hfW
  obtain ⟨p, hp⟩ :=
    Ideal.Quotient.mk_surjective ((coordinateRingEquivRegularTop hW').symm fW)
  refine ⟨p.totalDegree, homogenize i p, homogenize_isHomogeneous i p, ?_⟩
  intro P hPY hPc
  have hi : P.rep i ≠ 0 := rep_ne_zero_of_mem_standardChart hPc
  rw [eval_homogenize i p hi, mul_comm]
  congr 1
  -- The value of `f` at `P` is the value of `p` at `φᵢ(P)`.
  have hz : chartMap i P ∈ chartMap i '' (Y ∩ standardChart i) := ⟨P, ⟨hPY, hPc⟩, rfl⟩
  have key : evalAt (chartMap i '' (Y ∩ standardChart i)) ⟨chartMap i P, hz⟩
      ((coordinateRingEquivRegularTop hW').symm fW)
      = fW.1 ⟨⟨chartMap i P, hz⟩, trivial⟩ :=
    (coordinateRingEquivRegularTop_apply hW' _ ⟨⟨chartMap i P, hz⟩, trivial⟩).symm.trans
      (congrArg (fun r : (Variety.ofQuasiAffine hW'.isQuasiAffineVariety).globalRegular =>
        r.1 ⟨⟨chartMap i P, hz⟩, trivial⟩)
        ((coordinateRingEquivRegularTop hW').apply_symm_apply fW))
  rw [← hp, evalAt_mk] at key
  rw [show (eval (fun j : {j : σ // j ≠ i} => P.rep j.1 / P.rep i) p)
      = fW.1 ⟨⟨chartMap i P, hz⟩, trivial⟩ from key]
  exact congrArg f.1 (Subtype.ext (Subtype.ext (chartInv_chartMap hPc).symm))

end Hartshorne

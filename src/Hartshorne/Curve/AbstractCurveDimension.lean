/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Curve.AbstractNonsingularCurve
import Hartshorne.Curve.Basic
import Hartshorne.Curve.ValuationSpaceInfinitude

/-!
# Dimension of abstract nonsingular curves

Hartshorne, *Algebraic Geometry*, I.6 (p. 42).

Every abstract nonsingular curve has topological Krull dimension exactly one.
The upper bound follows because an irreducible closed subset of a cofinite
space is either a point or the whole space; infinitude supplies a strict chain
from a point to the whole curve for the lower bound.
-/

namespace Hartshorne

open Set TopologicalSpace

noncomputable section

universe u v

namespace ValuationSpace

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

private theorem topologicalKrullDim_open_eq_one [IsAlgClosed k]
    [Algebra.EssFiniteType k K] (htrdeg : Algebra.trdeg k K = 1)
    (U : Opens (ValuationSpace k K))
    (hU : (U : Set (ValuationSpace k K)).Nonempty) :
    topologicalKrullDim U = 1 := by
  let _ : Infinite U :=
    (infinite_of_isOpen_of_nonempty htrdeg U.isOpen hU).to_subtype
  let _ : IrreducibleSpace U :=
    (abstractNonsingularCurve htrdeg U hU).irreducible
  apply le_antisymm
  · rw [topologicalKrullDim]
    refine Order.krullDim_le_one_iff.mpr fun Z ↦ ?_
    obtain ⟨T, hTclosed, hTZ⟩ :=
      Topology.IsInducing.subtypeVal.isClosed_iff.mp Z.isClosed
    rcases (ValuationSpace.isClosed_iff k K).mp hTclosed with hTuniv | hTfinite
    · right
      have hZuniv : (Z : Set U) = Set.univ := by
        simpa [hTuniv] using hTZ.symm
      intro Y _ y _
      change y ∈ (Z : Set U)
      rw [hZuniv]
      exact Set.mem_univ y
    · left
      have hZfinite : (Z : Set U).Finite := by
        rw [← hTZ]
        exact hTfinite.preimage Subtype.val_injective.injOn
      have hZsubsingleton : (Z : Set U).Subsingleton :=
        hZfinite.isDiscrete.subsingleton_of_isPreirreducible
          Z.isIrreducible.isPreirreducible
      intro Y hYZ z hzZ
      obtain ⟨y, hyY⟩ := Y.isIrreducible.nonempty
      have hyZ : y ∈ (Z : Set U) := hYZ hyY
      have hzy : z = y := hZsubsingleton hzZ hyZ
      simpa [hzy] using hyY
  · rw [topologicalKrullDim]
    apply Order.one_le_krullDim_iff.mpr
    obtain ⟨x, y, hxy⟩ := exists_pair_ne U
    let point : IrreducibleCloseds U := {x}
    let whole : IrreducibleCloseds U :=
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ U, isClosed_univ⟩
    refine ⟨point, whole, lt_of_le_of_ne (Set.subset_univ _) ?_⟩
    intro hpw
    have hcarriers := congrArg (fun Z : IrreducibleCloseds U ↦ (Z : Set U)) hpw
    change ({x} : Set U) = Set.univ at hcarriers
    have hsingleton : ({x} : Set U) = Set.univ := hcarriers
    have hyx : y = x := by
      have : y ∈ ({x} : Set U) := by
        rw [hsingleton]
        exact Set.mem_univ y
      simpa using this
    exact hxy hyx.symm

/-- **Hartshorne I.6.** Every abstract nonsingular curve has topological
dimension exactly one. -/
theorem abstractNonsingularCurve_isCurve [IsAlgClosed k]
    [Algebra.EssFiniteType k K] (htrdeg : Algebra.trdeg k K = 1)
    (U : Opens (ValuationSpace k K))
    (hU : (U : Set (ValuationSpace k K)).Nonempty) :
    (abstractNonsingularCurve htrdeg U hU).IsCurve := by
  exact topologicalKrullDim_open_eq_one htrdeg U hU

end ValuationSpace

end

end Hartshorne

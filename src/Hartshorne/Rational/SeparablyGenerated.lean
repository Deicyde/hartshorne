/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.SeparablyGenerated

/-!
# Separably generated field extensions

The field-theoretic input to Hartshorne, *Algebraic Geometry*, I.4,
Proposition 4.9.  Over a perfect field, an essentially finitely generated field
extension has a finite separating transcendence basis.  The remaining finite
separable extension is simple by the primitive element theorem.

## Main result

* `Hartshorne.exists_separatingTranscendenceBasis_and_primitiveElement`
-/

open IntermediateField

namespace Hartshorne

universe u v

/-- Over a perfect field, an essentially finitely generated field extension
admits a finite separating transcendence basis and is generated over the
ground field by that basis together with one further element. -/
theorem exists_separatingTranscendenceBasis_and_primitiveElement
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    [PerfectField k] [Algebra.EssFiniteType k K] :
    ∃ (s : Finset K) (y : K),
      IsTranscendenceBasis k ((↑) : s → K) ∧
      Algebra.IsSeparable (adjoin k (s : Set K)) K ∧
      FiniteDimensional (adjoin k (s : Set K)) K ∧
      adjoin k (Set.insert y (s : Set K)) = ⊤ ∧
      (s.card : Cardinal) = Algebra.trdeg k K := by
  obtain ⟨s, hs, hsep⟩ :=
    exists_isTranscendenceBasis_and_isSeparable_of_perfectField k K
  let F : IntermediateField k K := adjoin k (s : Set K)
  have hAlg : Algebra.IsAlgebraic F K := by
    dsimp only [F]
    convert hs.isAlgebraic_field <;> simp
  let _ : Algebra.IsAlgebraic F K := hAlg
  let _ : Algebra.EssFiniteType F K := Algebra.EssFiniteType.of_comp k F K
  let hFinite : Module.Finite F K :=
    Algebra.finite_of_essFiniteType_of_isAlgebraic
  obtain ⟨y, hy⟩ := Field.exists_primitive_element F K
  refine ⟨s, y, hs, hsep, hFinite, ?_, ?_⟩
  · have hy' :
        (adjoin F ({y} : Set K)).restrictScalars k =
          (⊤ : IntermediateField k K) := by
      rw [hy, restrictScalars_top]
    rw [show F = adjoin k (s : Set K) by rfl, adjoin_adjoin_left] at hy'
    change adjoin k ({y} ∪ (s : Set K)) = ⊤
    rw [Set.union_comm]
    exact hy'
  · simpa only [Cardinal.mk_coe_finset] using hs.cardinalMk_eq_trdeg

end Hartshorne

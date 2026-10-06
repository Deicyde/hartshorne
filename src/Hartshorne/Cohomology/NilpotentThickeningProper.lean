/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Properness across a nilpotent thickening

Hartshorne, *Algebraic Geometry*, III, Exercise 5.9 (pp. 232--233).

A nilpotent closed immersion is a homeomorphism on underlying spaces.  Consequently properness
over a field is unchanged by passing across the thickening.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hartshorne

open AlgebraicGeometry

universe u

private lemma surjective_of_isNilpotent_ker
    {X₀ X : Scheme.{u}} (i : X₀ ⟶ X) [IsClosedImmersion i]
    (hi : IsNilpotent i.ker) : Surjective i := by
  let _ : IsDominant i := by
    obtain ⟨n, hn⟩ := hi
    rw [isDominant_iff, denseRange_iff_closure_range, ← i.support_ker,
      ← i.ker.support_pow (n + 1) (by simp), pow_succ, hn]
    simp
  infer_instance

/-- **Properness across a nilpotent thickening.**  If `X₀ ↪ X` is the closed immersion cut out
by a nilpotent ideal sheaf and `X` is of finite type over a field, then `X` is proper over the
field exactly when `X₀` is. -/
theorem isProper_iff_nilpotentThickening
    {k : Type u} [Field k] {X₀ X : Scheme.{u}}
    (i : X₀ ⟶ X) [IsClosedImmersion i] (hi : IsNilpotent i.ker)
    (p : X ⟶ Spec (.of k)) (hp : FiniteType p) :
    IsProper p ↔ IsProper (i ≫ p) := by
  constructor
  · intro hp'
    let _ : IsProper p := hp'
    infer_instance
  · intro hpi
    let _ : IsProper (i ≫ p) := hpi
    let _ : Surjective i := surjective_of_isNilpotent_ker i hi
    let _ : UniversallyClosed p := UniversallyClosed.of_comp_surjective i p
    let _ : LocallyOfFiniteType p := hp.1
    let q : pullback (i ≫ p) (i ≫ p) ⟶ pullback p p :=
      pullback.map (i ≫ p) (i ≫ p) p p i i (𝟙 _) (by simp) (by simp)
    let _ : MorphismProperty.IsStableUnderComposition @IsClosedImmersion :=
      (inferInstance : MorphismProperty.IsMultiplicative
        @IsClosedImmersion).toIsStableUnderComposition
    let _ : IsClosedImmersion q := by
      dsimp only [q]
      apply MorphismProperty.pullbackMap (P := @IsClosedImmersion)
      · infer_instance
      · infer_instance
      · rfl
      · rfl
    have hdiag : pullback.diagonal (i ≫ p) ≫ q = i ≫ pullback.diagonal p := by
      apply pullback.hom_ext
      · simp only [q, pullback.map, Category.assoc, pullback.lift_fst]
        rw [← Category.assoc, pullback.diagonal_fst, Category.id_comp]
        rw [pullback.diagonal_fst, Category.comp_id]
      · simp only [q, pullback.map, Category.assoc, pullback.lift_snd]
        rw [← Category.assoc, pullback.diagonal_snd, Category.id_comp]
        rw [pullback.diagonal_snd, Category.comp_id]
    have hrange :
        Set.range (pullback.diagonal p) =
          q '' Set.range (pullback.diagonal (i ≫ p)) := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        obtain ⟨x, rfl⟩ := i.surjective x
        refine ⟨pullback.diagonal (i ≫ p) x, ⟨x, rfl⟩, ?_⟩
        simpa only [Scheme.Hom.comp_apply] using
          congr_arg (fun f : X₀ ⟶ pullback p p => f x) hdiag
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        refine ⟨i x, ?_⟩
        simpa only [Scheme.Hom.comp_apply] using
          (congr_arg (fun f : X₀ ⟶ pullback p p => f x) hdiag).symm
    let _ : IsSeparated p := by
      constructor
      apply IsClosedImmersion.of_isPreimmersion
      rw [hrange]
      exact q.isClosedMap _ (pullback.diagonal (i ≫ p)).isClosedEmbedding.isClosed_range
    exact {}

end Hartshorne

/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.SmoothMorphisms.SmoothnessCriterionReduction
import Hartshorne.Cohomology.SmoothMorphisms.SmoothOverFieldComponentDimension

/-!
# Hartshorne's smoothness conditions for a standard smooth morphism

Hartshorne, *Algebraic Geometry*, III.10, definition on p. 268, compared with the locally
standard smooth predicate.

Let `f : X → Y` be a morphism of schemes of finite type over a field `k` which is smooth of
relative dimension `n` (locally standard smooth of relative dimension `n`). Then

1. `f` is flat;
2. every irreducible component of every scheme-theoretic fibre `X_y` has dimension `n`;
3. `dim_{k(x)} (Ω_{X/Y})_x ⊗ k(x) = n` for every `x ∈ X`.

Clause 2 holds because `X_y → Spec k(y)` is again smooth of relative dimension `n`, and the
irreducible components of a scheme smooth of relative dimension `n` over a field have dimension
`n`. Clause 3 holds because `Ω_{X/Y}` is locally free of rank `n`.

## Main result

* `Hartshorne.flat_and_fiber_dim_and_finrank_of_smoothOfRelativeDimension`
-/

open AlgebraicGeometry CategoryTheory TensorProduct IsLocalRing Module

namespace Hartshorne

universe u

/-- Let `f : X → Y` be a morphism of schemes of finite type over a field `k` that is smooth of
relative dimension `n`. Then `f` is flat, every irreducible component of every fibre `X_y` has
dimension `n`, and `dim_{k(x)} (Ω_{X/Y})_x ⊗ k(x) = n` for every `x ∈ X`. -/
theorem flat_and_fiber_dim_and_finrank_of_smoothOfRelativeDimension {k : Type u} [Field k]
    {X Y : Over (Spec (CommRingCat.of k))}
    (hX : LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom)
    (hY : LocallyOfFiniteType Y.hom ∧ QuasiCompact Y.hom) (f : X ⟶ Y) (n : ℕ)
    [SmoothOfRelativeDimension n f.left] :
    Flat f.left ∧
      (∀ y : Y.left, ∀ Z ∈ irreducibleComponents (f.left.fiber y),
        topologicalKrullDim Z = n) ∧
      ∀ x : X.left, finrank (ResidueField (X.left.presheaf.stalk x))
        (ResidueField (X.left.presheaf.stalk x) ⊗[X.left.presheaf.stalk x]
          (Scheme.relativeDifferentials f.left).presheaf.stalk x) = n := by
  have : LocallyOfFiniteType X.hom := hX.1
  have : LocallyOfFiniteType Y.hom := hY.1
  have : QuasiCompact X.hom := hX.2
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := {}
  have : LocallyOfFiniteType f.left := by
    have : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [Over.w f]; infer_instance
    exact locallyOfFiniteType_of_comp f.left Y.hom
  have hFft : ∀ y : Y.left, FiniteType (f.left.fiberToSpecResidueField y) :=
    fun y => ⟨inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd _ _)),
      inferInstanceAs (QuasiCompact (Limits.pullback.snd _ _))⟩
  obtain ⟨hsm, hrank⟩ :=
    (Scheme.smoothOfRelativeDimension_iff_smooth_and_finrank_fibre f.left n).mp ‹_›
  refine ⟨inferInstance, fun y Z hZ => ?_, hrank⟩
  have := Scheme.smoothOfRelativeDimension_fiberToSpecResidueField f.left n y
  exact topologicalKrullDim_of_mem_irreducibleComponents_of_smoothOfRelativeDimension
    (K := Y.left.residueField y) (f.left.fiberToSpecResidueField y) (hFft y) n hZ

end Hartshorne

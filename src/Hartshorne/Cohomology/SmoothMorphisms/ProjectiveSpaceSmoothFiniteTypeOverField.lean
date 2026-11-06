/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.SmoothMorphisms.ProjectiveSpaceSmooth

/-!
# Projective space is smooth in Hartshorne's setting

Hartshorne, *Algebraic Geometry*, III.10, Example 10.0.1 (p. 268).

Let `k` be a field and `Y` a scheme of finite type over `Spec k`. The projection
`ℙⁿ_k ×_{Spec k} Y ⟶ Y` is the base change of `ℙⁿ_k ⟶ Spec k` along the
structure morphism of `Y`, hence smooth of relative dimension `n`. The canonical
base-change isomorphism `ℙⁿ_k ×_{Spec k} Y ≅ ℙⁿ_Y` lies over `Y`, identifying the
fibre-product projection with the structure morphism `ℙⁿ_Y ⟶ Y`.

The finite-type hypothesis records Hartshorne's standing convention in III.10;
the proof does not use it.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace Hartshorne

/-- **Hartshorne III.10, Example 10.0.1.** Let `k` be a field and `Y` a scheme of finite
type over `Spec k`. The canonical isomorphism `ℙⁿ_k ×_{Spec k} Y ≅ ℙⁿ_Y` lies over `Y`,
and the projection `ℙⁿ_k ×_{Spec k} Y ⟶ Y` is smooth of relative dimension `n`. -/
theorem projectiveSpace_smoothOfRelativeDimension_finiteTypeOverField
    (k : Type u) [Field k] (Y : Over (Spec (CommRingCat.of k)))
    (_hY : LocallyOfFiniteType Y.hom ∧ QuasiCompact Y.hom) (n : ℕ) :
    (projectiveSpaceOverSchemeBaseChangeIso n Y.hom).hom ≫
        projectiveSpaceOverSchemeProjection n Y.left =
      pullback.snd (projectiveSpaceOverSchemeProjection n (Spec (CommRingCat.of k))) Y.hom ∧
    SmoothOfRelativeDimension n
      (pullback.snd (projectiveSpaceOverSchemeProjection n (Spec (CommRingCat.of k)))
        Y.hom) := by
  refine ⟨projectiveSpaceOverSchemeBaseChangeIso_hom_projection n Y.hom, ?_⟩
  have := projectiveSpaceOverSchemeProjection_smoothOfRelativeDimension n
    (Spec (CommRingCat.of k))
  exact smoothOfRelativeDimension_baseChange (IsPullback.of_hasPullback _ _)

end Hartshorne

/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Weil.ProjectiveLineSchemePoints
import Hartshorne.Weil.FiniteRationalPoints
import Hartshorne.Scheme.ProjectiveSpaceProper
import Mathlib.LinearAlgebra.Projectivization.Cardinality

/-!
# The point count of the projective line over a finite field

Hartshorne, *Algebraic Geometry*, Appendix C.1, projective-line example (p. 450): for the
projective line over `𝔽_q`, `N_r(ℙ¹) = q^r + 1` for every `r ≥ 1`.

Here `N_r` is `Hartshorne.pointCountSequence`, the number of morphisms
`Spec 𝔽_{q^r} ⟶ ℙ¹_{𝔽_q}` over `Spec 𝔽_q`, with `ℙ¹_{𝔽_q}` the relative projective line
`projectiveSpaceOverScheme 1 (Spec 𝔽_q)` and its structure morphism.

## Proof

The scheme-valued points of `ℙ¹_k` with values in a field extension `K` are the lines through
the origin in `K²` (`Hartshorne.ProjectiveLinePoints.equivProjectiveSpace`). Over the finite
field `K = 𝔽_{q^r}` there are `#K + 1` such lines, and `#K = q^r`.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Hartshorne

/-- Relative projective space is of finite type over its base, since it is proper. -/
theorem projectiveSpaceOverSchemeProjection_finiteType (n : ℕ) (Y : Scheme.{u}) :
    FiniteType (projectiveSpaceOverSchemeProjection n Y) := by
  let _ : IsProper (projectiveSpaceOverSchemeProjection n Y) :=
    projectiveSpaceOverSchemeProjection_isProper n Y
  exact ⟨inferInstance, inferInstance⟩

/-- Morphisms in the over category from `a : T ⟶ S` to `f : X ⟶ S` are the morphisms
`T ⟶ X` whose composite with `f` is `a`. -/
private def overHomEquivSubtype {S T X : Scheme.{u}} (a : T ⟶ S) (f : X ⟶ S) :
    (Over.mk a ⟶ Over.mk f) ≃ {φ : T ⟶ X // φ ≫ f = a} where
  toFun g := ⟨g.left, Over.w g⟩
  invFun φ := Over.homMk φ.1 φ.2
  left_inv _ := Over.OverMorphism.ext rfl
  right_inv _ := rfl

/-- **The projective line has `q^r + 1` points over `𝔽_{q^r}`** (Hartshorne, Appendix C.1,
p. 450). For a finite field `k` with `q` elements and every `r ≥ 1`, the number of
morphisms `Spec 𝔽_{q^r} ⟶ ℙ¹_k` over `Spec k` is `q^r + 1`. -/
theorem pointCountSequence_projectiveLine (k : Type u) [Field k] [Finite k] (r : ℕ+) :
    pointCountSequence k (projectiveSpaceOverScheme 1 (Spec (.of k)))
        (projectiveSpaceOverSchemeProjection 1 (Spec (.of k)))
        (projectiveSpaceOverSchemeProjection_finiteType 1 (Spec (.of k))) r =
      Nat.card k ^ (r : ℕ) + 1 := by
  let K := finiteFieldExtension k r
  change Nat.card ((Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ⟶
      Over.mk (projectiveSpaceOverSchemeProjection 1 (Spec (.of k)))) = _
  rw [Nat.card_congr ((overHomEquivSubtype _ _).trans
      (ProjectiveLinePoints.equivProjectiveSpace k K)),
    Projectivization.card_of_finrank_two K _ (by simp), finiteFieldExtension_natCard]

end Hartshorne

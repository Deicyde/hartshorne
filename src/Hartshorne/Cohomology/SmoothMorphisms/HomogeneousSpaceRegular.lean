/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.SmoothMorphisms.HomogeneousSpace
import Hartshorne.Scheme.Differentials.DenseNonsingularLocus

/-!
# Homogeneous spaces are nonsingular

Hartshorne, *Algebraic Geometry*, III.10, Remark 10.7.1 and Example 10.7.3 (p. 273).

A homogeneous space `X` for a group variety over an algebraically closed field `k` is smooth over
`k`, hence regular at every point. The smooth locus of `X ⟶ Spec k` is open and dense. If it
missed a point, then, `X` being Jacobson, it would miss a closed point `x`; it contains some closed
point `y`, and a translation sending `x` to `y` is an automorphism of `X` over `k`, which
preserves the smooth locus. A group variety acting on itself by left translation is a homogeneous
space, so it is nonsingular too.
-/

open CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace Hartshorne

open AlgebraicGeometry

universe u

variable {k : Type u} [Field k]

set_option backward.isDefEq.respectTransparency false in
/-- A homogeneous space over an algebraically closed field is smooth over the field. -/
theorem HomogeneousSpace.smooth [IsAlgClosed k] {G : GroupVariety k} (H : HomogeneousSpace k G) :
    Smooth H.toAction.X.hom := by
  have := LocallyOfFiniteType.jacobsonSpace H.toAction.X.hom
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← TopologicalSpace.Opens.coe_eq_univ,
    ← not_ne_iff, ← Set.nonempty_compl]
  intro hne
  obtain ⟨x, hx, hxc⟩ := nonempty_inter_closedPoints hne
    H.toAction.X.hom.smoothLocus.2.isClosed_compl.isLocallyClosed
  obtain ⟨y, hy : y ∈ H.toAction.X.hom.smoothLocus, hyc⟩ := nonempty_inter_closedPoints
    H.toAction.X.hom.dense_smoothLocus_of_perfectField.nonempty
    H.toAction.X.hom.smoothLocus.2.isLocallyClosed
  obtain ⟨g, hg⟩ := HomogeneousSpace.transitive_closedPoints k H ⟨x, hxc⟩ ⟨y, hyc⟩
  let α := AlgebraicGroupAction.translationIso (k := k) H.toAction g
  have hα' : α.hom.left x = y := by
    have h1 := congrArg Subtype.val hg
    rw [AlgebraicGroupAction.actClosedPoint,
      AlgebraicGroupAction.actPoint_eq_comp_translation] at h1
    simpa [rationalPointEquivClosedPoint, rationalPointEquivSchemePoint, pointEquivClosedPoint,
      α] using h1
  rw! [← hα', ← α.hom.left.mem_preimage, Scheme.Hom.preimage_smoothLocus_eq,
    show α.hom.left ≫ H.toAction.X.hom = H.toAction.X.hom from Over.w α.hom] at hy
  exact hx hy

/-- **Homogeneous spaces are nonsingular** (Hartshorne III, Example 10.7.3). A homogeneous space
for a group variety over an algebraically closed field is regular. -/
theorem HomogeneousSpace.isRegular [IsAlgClosed k] {G : GroupVariety k}
    (H : HomogeneousSpace k G) : H.toAction.X.left.IsRegular := by
  have := H.smooth
  exact ⟨LocallyOfFiniteType.isLocallyNoetherian H.toAction.X.hom,
    isRegularAt_of_smooth H.toAction.X.hom⟩

attribute [local instance] ModObj.regular in
/-- A group variety acting on itself by left translation is a homogeneous space. -/
noncomputable def GroupVariety.selfHomogeneousSpace (G : GroupVariety k) :
    HomogeneousSpace k G where
  toAction := ⟨G.obj⟩
  finiteType := G.finiteType
  transitive x y := ⟨y * x⁻¹, by
    change (y * x⁻¹) * x = y
    rw [inv_mul_cancel_right]⟩

/-- **A group variety is nonsingular** (Hartshorne III, Remark 10.7.1 with Example 10.7.3): over
an algebraically closed field, it is a homogeneous space under left translation. -/
theorem GroupVariety.isRegular [IsAlgClosed k] (G : GroupVariety k) : G.obj.left.IsRegular :=
  G.selfHomogeneousSpace.isRegular

end Hartshorne

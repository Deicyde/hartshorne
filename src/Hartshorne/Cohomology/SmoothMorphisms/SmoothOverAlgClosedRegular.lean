/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.SmoothMorphisms.HartshorneSmoothnessCriterion
import Hartshorne.Scheme.Differentials.DifferentialsCharacterizeNonsingular

/-!
# Smoothness and regularity over an algebraically closed field

Hartshorne, *Algebraic Geometry*, III, Example 10.0.3 (p. 268), with II, Theorems 8.8 and 8.15.

Let `X` be a scheme of finite type over an algebraically closed field `k`, all of whose
irreducible components have dimension `n`. Then `X ⟶ Spec k` is smooth of relative dimension `n`
if and only if every local ring of `X` is regular
(`Hartshorne.smoothOfRelativeDimension_iff_forall_isRegularAt`). For irreducible `X` of
dimension `n` this says that smoothness is Hartshorne's nonsingularity
(`Hartshorne.smoothOfRelativeDimension_iff_isRegular`).

## Proof

By Hartshorne's smoothness criterion, `X ⟶ Spec k` is smooth of relative dimension `n` exactly
when it is flat (automatic over a field), its fibre has all irreducible components of dimension
`n` (the fibre over the point of `Spec k` is homeomorphic to `X`), and every fibre
`κ(x) ⊗ Ω_{X/k,x}` has dimension `n`. The last condition is equivalent to regularity of all local
rings of `X` (`Hartshorne.forall_isRegularAt_iff_finrank_fibre`, from the proof of Theorem 8.15).
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Hartshorne

/-- Over a field, the fibre of `X ⟶ Spec k` has all irreducible components of dimension `n` when
`X` does. -/
theorem topologicalKrullDim_irreducibleComponents_fiber {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) {n : ℕ}
    (hC : ∀ C ∈ irreducibleComponents X, topologicalKrullDim C = n) (y : Spec (.of k)) :
    ∀ Z ∈ irreducibleComponents (f.fiber y), topologicalKrullDim Z = n := by
  have hpre : f ⁻¹' {y} = Set.univ :=
    Set.eq_univ_of_forall fun x ↦ Subsingleton.elim (α := Spec (.of k)) _ _
  let e : f.fiber y ≃ₜ X :=
    (f.fiberHomeo y).trans ((Homeomorph.setCongr hpre).trans (Homeomorph.Set.univ X))
  intro Z hZ
  have hZ' : e '' Z ∈ irreducibleComponents X :=
    image_mem_irreducibleComponents_of_isPreirreducible_fiber e e.continuous e.isOpenMap
      (fun x ↦ (Set.subsingleton_singleton.preimage e.injective).isPreirreducible) e.surjective hZ
  rw [← hC _ hZ']
  exact IsHomeomorph.topologicalKrullDim_eq _ (e.image Z).isHomeomorph

/-- **Smoothness and regularity over an algebraically closed field** (Hartshorne III,
Example 10.0.3). Let `X` be a scheme of finite type over an algebraically closed field `k`, all
of whose irreducible components have dimension `n`. Then `X ⟶ Spec k` is smooth of relative
dimension `n` if and only if every local ring of `X` is regular. -/
theorem smoothOfRelativeDimension_iff_forall_isRegularAt {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (hf : FiniteType f) (n : ℕ)
    (hC : ∀ C ∈ irreducibleComponents X, topologicalKrullDim C = n) :
    SmoothOfRelativeDimension n f ↔ ∀ x : X, X.IsRegularAt x := by
  have h := smoothOfRelativeDimension_iff_flat_and_fiber_dim_and_finrank
    (X := Over.mk f) (Y := Over.mk (𝟙 (Spec (.of k)))) ⟨hf.1, hf.2⟩
    ⟨show LocallyOfFiniteType (𝟙 (Spec (.of k))) from inferInstance,
      show QuasiCompact (𝟙 (Spec (.of k))) from inferInstance⟩ (Over.homMk f (by simp)) n
  change SmoothOfRelativeDimension n f ↔ _ at h
  rw [h, forall_isRegularAt_iff_finrank_fibre f hf n hC]
  exact ⟨fun h ↦ h.2.2, fun h ↦ ⟨show Flat f from inferInstance,
    topologicalKrullDim_irreducibleComponents_fiber f hC, h⟩⟩

/-- For an irreducible `X` of finite type over an algebraically closed field `k`, of dimension
`n`, smoothness of relative dimension `n` over `k` is Hartshorne's nonsingularity (II.8): `X` is
regular. -/
theorem smoothOfRelativeDimension_iff_isRegular {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IrreducibleSpace X] (hf : FiniteType f) (n : ℕ)
    (hn : topologicalKrullDim X = n) :
    SmoothOfRelativeDimension n f ↔ X.IsRegular := by
  have : LocallyOfFiniteType f := hf.1
  rw [smoothOfRelativeDimension_iff_forall_isRegularAt f hf n
    (DifferentialsNonsingular.topologicalKrullDim_irreducibleComponent hn)]
  exact ⟨fun h ↦ ⟨LocallyOfFiniteType.isLocallyNoetherian f, h⟩, fun h ↦ h.2⟩

end Hartshorne

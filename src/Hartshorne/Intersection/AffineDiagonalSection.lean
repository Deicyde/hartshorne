/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Affine.Dimension
import Hartshorne.Intersection.AffineProduct
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# The diagonal section of an affine product

Hartshorne, *Algebraic Geometry*, I.7, proof of Proposition 7.1 (p. 48).

If `Y` and `Z` lie in the same affine space, their intersection is
homeomorphic to the section of `Y × Z` cut out by the diagonal equations
`X_(inl i) - X_(inr i)`.  This is the geometric reduction that turns an
arbitrary intersection into a cut by at most `Nat.card σ` equations.

## Main results

* `Hartshorne.affineDiagonalSectionHomeomorph`
* `Hartshorne.dim_affineDiagonalSection`
* `Hartshorne.affineDiagonalSectionIrreducibleComponentsEquiv`
-/

namespace Hartshorne

open MvPolynomial Set TopologicalSpace
open scoped Hartshorne

noncomputable section

variable {k : Type*} [Field k] {σ : Type*}

/-- The equation equating the two copies of the coordinate indexed by `i`. -/
def affineDiagonalPolynomial (i : σ) : MvPolynomial (Sum σ σ) k :=
  X (Sum.inl i) - X (Sum.inr i)

/-- The family of equations cutting out the diagonal in the affine product. -/
def affineDiagonalPolynomials : Set (MvPolynomial (Sum σ σ) k) :=
  Set.range affineDiagonalPolynomial

/-- The common zero set of the diagonal equations. -/
def affineDiagonalZeroSet : Set (Sum σ σ → k) :=
  zeroSet affineDiagonalPolynomials

/-- The diagonal section of `Y × Z`. -/
def affineDiagonalSection (Y Z : Set (σ → k)) : Set (Sum σ σ → k) :=
  affineProduct Y Z ∩ affineDiagonalZeroSet

@[simp]
theorem eval_affineDiagonalPolynomial (z : Sum σ σ → k) (i : σ) :
    eval z (affineDiagonalPolynomial i) = z (Sum.inl i) - z (Sum.inr i) := by
  simp [affineDiagonalPolynomial]

/-- A point satisfies the diagonal equations exactly when its two coordinate
blocks agree. -/
theorem mem_affineDiagonalZeroSet_iff {z : Sum σ σ → k} :
    z ∈ affineDiagonalZeroSet ↔
      (fun i ↦ z (Sum.inl i)) = fun i ↦ z (Sum.inr i) := by
  constructor
  · intro hz
    funext i
    have hi := hz (affineDiagonalPolynomial i) ⟨i, rfl⟩
    exact sub_eq_zero.mp (by simpa using hi)
  · intro hz f hf
    obtain ⟨i, rfl⟩ := hf
    rw [eval_affineDiagonalPolynomial]
    exact sub_eq_zero.mpr (congrFun hz i)

/-- The diagonal equations are a finite family when the ambient affine space
has finitely many coordinates. -/
theorem affineDiagonalPolynomials_finite [Finite σ] :
    (affineDiagonalPolynomials : Set (MvPolynomial (Sum σ σ) k)).Finite :=
  Set.finite_range _

/-- There are at most as many diagonal equations as affine coordinates. -/
theorem natCard_affineDiagonalPolynomials_le [Finite σ] :
    Nat.card (affineDiagonalPolynomials : Set (MvPolynomial (Sum σ σ) k)) ≤
      Nat.card σ :=
  Finite.card_range_le _

/-- Substitute the same affine point into both coordinate blocks. -/
noncomputable def affineDiagonalRingHom :
    MvPolynomial (Sum σ σ) k →ₐ[k] MvPolynomial σ k :=
  MvPolynomial.aeval (Sum.elim (fun i ↦ X i) (fun i ↦ X i))

theorem eval_affineDiagonalRingHom (x : σ → k)
    (f : MvPolynomial (Sum σ σ) k) :
    eval x (affineDiagonalRingHom f) = eval (affineProductPoint x x) f := by
  rw [affineDiagonalRingHom, aeval_def, eval_eval₂]
  have hc : (eval x).comp (algebraMap k (MvPolynomial σ k)) = RingHom.id k := by
    ext c
    simp
  rw [hc, eval₂_id]
  have hfun :
      (fun s : Sum σ σ ↦ eval x (Sum.elim (fun i ↦ X i) (fun i ↦ X i) s)) =
        affineProductPoint x x := by
    funext s
    cases s <;> simp [affineProductPoint]
  rw [hfun]

/-- The diagonal map is continuous for the affine Zariski topologies. -/
theorem continuous_affineDiagonalPoint :
    Continuous (fun x : σ → k ↦ affineProductPoint x x) := by
  rw [continuous_iff_isClosed]
  intro W hW
  obtain ⟨T, rfl⟩ := isClosed_iff_isAlgebraicSet.1 hW
  have heq : (fun x : σ → k ↦ affineProductPoint x x) ⁻¹' zeroSet T =
      zeroSet (affineDiagonalRingHom '' T) := by
    ext x
    constructor
    · intro hx g hg
      obtain ⟨f, hf, rfl⟩ := hg
      rw [eval_affineDiagonalRingHom]
      exact hx f hf
    · intro hx f hf
      rw [← eval_affineDiagonalRingHom]
      exact hx (affineDiagonalRingHom f) ⟨f, hf, rfl⟩
  rw [heq]
  exact isClosed_zeroSet _

/-- Restrict a point in the product affine space to its left coordinate
block. -/
def affineLeftProjection (z : Sum σ σ → k) : σ → k :=
  fun i ↦ z (Sum.inl i)

/-- Coordinate-block projection is continuous for the affine Zariski
topologies. -/
theorem continuous_affineLeftProjection :
    Continuous (affineLeftProjection : (Sum σ σ → k) → (σ → k)) := by
  rw [continuous_iff_isClosed]
  intro W hW
  obtain ⟨T, rfl⟩ := isClosed_iff_isAlgebraicSet.1 hW
  have heq : affineLeftProjection ⁻¹' zeroSet T =
      zeroSet (rename Sum.inl '' T) := by
    ext z
    constructor
    · intro hz g hg
      obtain ⟨f, hf, rfl⟩ := hg
      rw [eval_rename]
      exact hz f hf
    · intro hz f hf
      have := hz (rename Sum.inl f) ⟨f, hf, rfl⟩
      rwa [eval_rename] at this
  rw [heq]
  exact isClosed_zeroSet _

/-- Send a point of `Y ∩ Z` to the corresponding point on the diagonal of
`Y × Z`. -/
def affineDiagonalSectionMap (Y Z : Set (σ → k)) :
    ↥(Y ∩ Z) → ↥(affineDiagonalSection Y Z) :=
  fun x ↦ ⟨affineProductPoint x.1 x.1, by
    refine ⟨⟨x.2.1, x.2.2⟩, ?_⟩
    exact mem_affineDiagonalZeroSet_iff.2 rfl⟩

/-- Restrict a point of the diagonal section to either coordinate block. -/
def affineDiagonalSectionInv (Y Z : Set (σ → k)) :
    ↥(affineDiagonalSection Y Z) → ↥(Y ∩ Z) :=
  fun z ↦ ⟨affineLeftProjection z.1, by
    refine ⟨z.2.1.1, ?_⟩
    have hblocks := mem_affineDiagonalZeroSet_iff.1 z.2.2
    change (fun i ↦ z.1 (Sum.inl i)) ∈ Z
    rw [hblocks]
    exact z.2.1.2⟩

theorem affineDiagonalSectionInv_map (Y Z : Set (σ → k))
    (x : ↥(Y ∩ Z)) :
    affineDiagonalSectionInv Y Z (affineDiagonalSectionMap Y Z x) = x := by
  apply Subtype.ext
  rfl

theorem affineDiagonalSectionMap_inv (Y Z : Set (σ → k))
    (z : ↥(affineDiagonalSection Y Z)) :
    affineDiagonalSectionMap Y Z (affineDiagonalSectionInv Y Z z) = z := by
  apply Subtype.ext
  funext s
  cases s with
  | inl i => rfl
  | inr i =>
      exact congrFun (mem_affineDiagonalZeroSet_iff.1 z.2.2) i

/-- The point-set equivalence underlying the diagonal reduction. -/
noncomputable def affineDiagonalSectionEquiv (Y Z : Set (σ → k)) :
    ↥(Y ∩ Z) ≃ ↥(affineDiagonalSection Y Z) where
  toFun := affineDiagonalSectionMap Y Z
  invFun := affineDiagonalSectionInv Y Z
  left_inv := affineDiagonalSectionInv_map Y Z
  right_inv := affineDiagonalSectionMap_inv Y Z

theorem continuous_affineDiagonalSectionMap (Y Z : Set (σ → k)) :
    Continuous (affineDiagonalSectionMap Y Z) :=
  (continuous_affineDiagonalPoint.comp continuous_subtype_val).subtype_mk _

theorem continuous_affineDiagonalSectionInv (Y Z : Set (σ → k)) :
    Continuous (affineDiagonalSectionInv Y Z) :=
  (continuous_affineLeftProjection.comp continuous_subtype_val).subtype_mk _

/-- **Hartshorne I.7, diagonal reduction.** The intersection `Y ∩ Z` is
canonically homeomorphic to the section of `Y × Z` by the diagonal
equations. -/
noncomputable def affineDiagonalSectionHomeomorph (Y Z : Set (σ → k)) :
    ↥(Y ∩ Z) ≃ₜ ↥(affineDiagonalSection Y Z) :=
  Homeomorph.mk (affineDiagonalSectionEquiv Y Z)
    (continuous_affineDiagonalSectionMap Y Z)
    (continuous_affineDiagonalSectionInv Y Z)

/-- The diagonal reduction preserves dimension. -/
theorem dim_affineDiagonalSection (Y Z : Set (σ → k)) :
    dim (Y ∩ Z) = dim (affineDiagonalSection Y Z) :=
  IsHomeomorph.topologicalKrullDim_eq _
    (affineDiagonalSectionHomeomorph Y Z).isHomeomorph

/-- The diagonal homeomorphism transports irreducible components. -/
noncomputable def affineDiagonalSectionIrreducibleComponentsEquiv
    (Y Z : Set (σ → k)) :
    irreducibleComponents ↥(Y ∩ Z) ≃o
      irreducibleComponents ↥(affineDiagonalSection Y Z) := by
  let e := affineDiagonalSectionHomeomorph Y Z
  exact (irreducibleComponentsEquivOfIsPreirreducibleFiber
    e e.continuous e.isOpenMap
      (fun _ ↦ (subsingleton_singleton.preimage e.injective).isPreirreducible)
      e.surjective).symm

end

end Hartshorne

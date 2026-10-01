/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Affine.Variety

/-!
# Products of affine varieties

Hartshorne, *Algebraic Geometry*, I.3, Exercise 3.15(a) (p. 22).

The product is embedded in affine space on the disjoint union of the two
coordinate types. Closedness is checked by extending the equations of each
factor, and irreducibility uses the closed-fibre argument rather than the
ordinary product topology.

## Main definitions

* `Hartshorne.affineProduct`

## Main results

* `Hartshorne.isAffineVariety_affineProduct`
-/

namespace Hartshorne

open MvPolynomial TopologicalSpace
open scoped Hartshorne

variable {k : Type*} [Field k] {σ τ : Type*}

/-- Join two affine coordinate vectors along a disjoint union of their
coordinate types. -/
def affineProductPoint (x : σ → k) (y : τ → k) : Sum σ τ → k :=
  Sum.elim x y

/-- The affine product of two subsets, embedded in affine space on the
disjoint union of their coordinate types. -/
def affineProduct (X : Set (σ → k)) (Y : Set (τ → k)) : Set (Sum σ τ → k) :=
  {z | (fun i => z (Sum.inl i)) ∈ X ∧ (fun j => z (Sum.inr j)) ∈ Y}

/-- Extend equations on the left factor to the product coordinates. -/
def affineLeftPolynomials (T : Set (MvPolynomial σ k)) :
    Set (MvPolynomial (Sum σ τ) k) :=
  rename Sum.inl '' T

/-- Extend equations on the right factor to the product coordinates. -/
def affineRightPolynomials (T : Set (MvPolynomial τ k)) :
    Set (MvPolynomial (Sum σ τ) k) :=
  rename Sum.inr '' T

/-- A product of affine algebraic sets is affine algebraic. -/
theorem isAlgebraicSet_affineProduct {X : Set (σ → k)} {Y : Set (τ → k)}
    (hX : IsAlgebraicSet X) (hY : IsAlgebraicSet Y) :
    IsAlgebraicSet (affineProduct X Y) := by
  obtain ⟨T, rfl⟩ := hX
  obtain ⟨U, rfl⟩ := hY
  refine ⟨affineLeftPolynomials (τ := τ) T ∪ affineRightPolynomials (σ := σ) U, ?_⟩
  ext z
  constructor
  · rintro ⟨hzT, hzU⟩ f (hf | hf)
    · obtain ⟨g, hg, rfl⟩ := hf
      rw [eval_rename]
      exact hzT g hg
    · obtain ⟨g, hg, rfl⟩ := hf
      rw [eval_rename]
      exact hzU g hg
  · intro hz
    refine ⟨?_, ?_⟩
    · intro f hf
      have := hz (rename Sum.inl f)
        (show rename Sum.inl f ∈ affineLeftPolynomials (τ := τ) T ∪
            affineRightPolynomials (σ := σ) U from Or.inl ⟨f, hf, rfl⟩)
      rwa [eval_rename] at this
    · intro f hf
      have := hz (rename Sum.inr f)
        (show rename Sum.inr f ∈ affineLeftPolynomials (τ := τ) T ∪
            affineRightPolynomials (σ := σ) U from Or.inr ⟨f, hf, rfl⟩)
      rwa [eval_rename] at this

/-- Substitute a fixed right point into polynomials on the product affine
space. -/
noncomputable def affineLeftSliceRingHom (y : τ → k) :
    MvPolynomial (Sum σ τ) k →ₐ[k] MvPolynomial σ k :=
  MvPolynomial.aeval (Sum.elim (fun i => X i) (fun j => C (y j)))

/-- Substitute a fixed left point into polynomials on the product affine
space. -/
noncomputable def affineRightSliceRingHom (x : σ → k) :
    MvPolynomial (Sum σ τ) k →ₐ[k] MvPolynomial τ k :=
  MvPolynomial.aeval (Sum.elim (fun i => C (x i)) (fun j => X j))

theorem eval_affineLeftSliceRingHom (x : σ → k) (y : τ → k)
    (f : MvPolynomial (Sum σ τ) k) :
    eval x (affineLeftSliceRingHom y f) = eval (affineProductPoint x y) f := by
  rw [affineLeftSliceRingHom, aeval_def, eval_eval₂]
  have hc : (eval x).comp (algebraMap k (MvPolynomial σ k)) = RingHom.id k := by
    ext c
    simp
  rw [hc, eval₂_id]
  have hfun :
      (fun s : Sum σ τ => eval x (Sum.elim (fun i => X i) (fun j => C (y j)) s)) =
        affineProductPoint x y := by
    funext s
    cases s <;> simp [affineProductPoint]
  rw [hfun]

theorem eval_affineRightSliceRingHom (x : σ → k) (y : τ → k)
    (f : MvPolynomial (Sum σ τ) k) :
    eval y (affineRightSliceRingHom x f) = eval (affineProductPoint x y) f := by
  rw [affineRightSliceRingHom, aeval_def, eval_eval₂]
  have hc : (eval y).comp (algebraMap k (MvPolynomial τ k)) = RingHom.id k := by
    ext c
    simp
  rw [hc, eval₂_id]
  have hfun :
      (fun s : Sum σ τ => eval y (Sum.elim (fun i => C (x i)) (fun j => X j) s)) =
        affineProductPoint x y := by
    funext s
    cases s <;> simp [affineProductPoint]
  rw [hfun]

/-- Fixing the right factor gives a continuous map for the affine Zariski
topologies. -/
theorem continuous_affineProductPoint_left (y : τ → k) :
    Continuous (fun x : σ → k => affineProductPoint x y) := by
  rw [continuous_iff_isClosed]
  intro Z hZ
  obtain ⟨T, rfl⟩ := isClosed_iff_isAlgebraicSet.1 hZ
  have heq : (fun x : σ → k => affineProductPoint x y) ⁻¹' zeroSet T =
      zeroSet (affineLeftSliceRingHom y '' T) := by
    ext x
    constructor
    · intro hx g hg
      obtain ⟨f, hf, rfl⟩ := hg
      rw [eval_affineLeftSliceRingHom]
      exact hx f hf
    · intro hx f hf
      rw [← eval_affineLeftSliceRingHom]
      exact hx (affineLeftSliceRingHom y f) ⟨f, hf, rfl⟩
  rw [heq]
  exact isClosed_zeroSet _

/-- Fixing the left factor gives a continuous map for the affine Zariski
topologies. -/
theorem continuous_affineProductPoint_right (x : σ → k) :
    Continuous (fun y : τ → k => affineProductPoint x y) := by
  rw [continuous_iff_isClosed]
  intro Z hZ
  obtain ⟨T, rfl⟩ := isClosed_iff_isAlgebraicSet.1 hZ
  have heq : (fun y : τ → k => affineProductPoint x y) ⁻¹' zeroSet T =
      zeroSet (affineRightSliceRingHom x '' T) := by
    ext y
    constructor
    · intro hy g hg
      obtain ⟨f, hf, rfl⟩ := hg
      rw [eval_affineRightSliceRingHom]
      exact hy f hf
    · intro hy f hf
      rw [← eval_affineRightSliceRingHom]
      exact hy (affineRightSliceRingHom x f) ⟨f, hf, rfl⟩
  rw [heq]
  exact isClosed_zeroSet _

private theorem isIrreducible_range_prod_of_separatelyContinuous
    {A B C : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace C] [IrreducibleSpace A] [IrreducibleSpace B]
    (f : A → B → C) (hleft : ∀ b, Continuous fun a => f a b)
    (hright : ∀ a, Continuous fun b => f a b) :
    IsIrreducible (Set.range fun p : A × B => f p.1 p.2) := by
  refine ⟨Set.range_nonempty _, ?_⟩
  rw [isPreirreducible_iff_isClosed_union_isClosed]
  intro C D hC hD hcover
  let AC : Set A := {a | ∀ b, f a b ∈ C}
  let AD : Set A := {a | ∀ b, f a b ∈ D}
  have hAC : IsClosed AC := by
    have hi : IsClosed (⋂ b : B, (fun a => f a b) ⁻¹' C) :=
      isClosed_iInter fun b => hC.preimage (hleft b)
    convert hi using 1
    ext a
    simp [AC]
  have hAD : IsClosed AD := by
    have hi : IsClosed (⋂ b : B, (fun a => f a b) ⁻¹' D) :=
      isClosed_iInter fun b => hD.preimage (hleft b)
    convert hi using 1
    ext a
    simp [AD]
  have hAcover : Set.univ ⊆ AC ∪ AD := by
    intro a ha
    have hBcover : Set.univ ⊆
        (fun b => f a b) ⁻¹' C ∪ (fun b => f a b) ⁻¹' D := by
      intro b hb
      exact hcover ⟨(a, b), rfl⟩
    rcases isPreirreducible_iff_isClosed_union_isClosed.mp
        (PreirreducibleSpace.isPreirreducible_univ (X := B)) _ _
        (hC.preimage (hright a)) (hD.preimage (hright a)) hBcover with h | h
    · exact Or.inl (fun b => h (Set.mem_univ b))
    · exact Or.inr (fun b => h (Set.mem_univ b))
  rcases isPreirreducible_iff_isClosed_union_isClosed.mp
      (PreirreducibleSpace.isPreirreducible_univ (X := A)) AC AD hAC hAD hAcover with h | h
  · left
    rintro _ ⟨⟨a, b⟩, rfl⟩
    exact h (Set.mem_univ a) b
  · right
    rintro _ ⟨⟨a, b⟩, rfl⟩
    exact h (Set.mem_univ a) b

theorem isIrreducible_affineProduct {X : Set (σ → k)} {Y : Set (τ → k)}
    (hX : IsIrreducible X) (hY : IsIrreducible Y) :
    IsIrreducible (affineProduct X Y) := by
  let _ : IrreducibleSpace X := Subtype.irreducibleSpace hX
  let _ : IrreducibleSpace Y := Subtype.irreducibleSpace hY
  have hirr := isIrreducible_range_prod_of_separatelyContinuous
    (fun x : X => fun y : Y => affineProductPoint x.1 y.1)
    (fun y => (continuous_affineProductPoint_left y.1).comp continuous_subtype_val)
    (fun x => (continuous_affineProductPoint_right x.1).comp continuous_subtype_val)
  have hrange :
      Set.range (fun p : X × Y => affineProductPoint p.1.1 p.2.1) = affineProduct X Y := by
    ext z
    constructor
    · rintro ⟨⟨x, y⟩, rfl⟩
      exact ⟨x.2, y.2⟩
    · intro hz
      refine ⟨(⟨(fun i => z (Sum.inl i)), hz.1⟩,
        ⟨(fun j => z (Sum.inr j)), hz.2⟩), ?_⟩
      funext i
      cases i <;> rfl
  rw [hrange] at hirr
  exact hirr

/-- **Exercise 3.15(a)**: the affine product of two affine varieties is an
affine variety in the Zariski topology induced from the ambient affine space. -/
theorem isAffineVariety_affineProduct {X : Set (σ → k)} {Y : Set (τ → k)}
    (hX : IsAffineVariety X) (hY : IsAffineVariety Y) :
    IsAffineVariety (affineProduct X Y) :=
  ⟨isIrreducible_affineProduct hX.isIrreducible hY.isIrreducible,
    isClosed_iff_isAlgebraicSet.2
      (isAlgebraicSet_affineProduct hX.isAlgebraicSet hY.isAlgebraicSet)⟩

end Hartshorne

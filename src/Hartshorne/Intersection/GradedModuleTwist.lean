/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.IntegerPolynomialGrading
import Mathlib.Algebra.Module.GradedModule

/-!
# Twists of integer-graded modules

Hartshorne, *Algebraic Geometry*, I.7, definition before Proposition 7.4
(p. 50).
-/

namespace Hartshorne

open DirectSum

/-- Reindex an integer grading by `l`.  Thus the degree-`d` piece of the
twist is literally the old degree-`d + l` piece. -/
def gradedModuleTwist {S : Type*} (M : ℤ → S) (l : ℤ) : ℤ → S :=
  fun d ↦ M (d + l)

@[simp]
theorem gradedModuleTwist_apply {S : Type*} (M : ℤ → S) (l d : ℤ) :
    gradedModuleTwist M l d = M (d + l) := rfl

@[simp]
theorem gradedModuleTwist_zero {S : Type*} (M : ℤ → S) :
    gradedModuleTwist M 0 = M := by
  funext d
  change M (d + 0) = M d
  rw [add_zero]

@[simp]
theorem gradedModuleTwist_add {S : Type*} (M : ℤ → S) (l m : ℤ) :
    gradedModuleTwist (gradedModuleTwist M l) m =
      gradedModuleTwist M (l + m) := by
  funext d
  change M ((d + m) + l) = M (d + (l + m))
  congr 1
  omega

section Decomposition

variable {M S : Type*} [AddCommMonoid M] [SetLike S M]
  [AddSubmonoidClass S M]

@[reducible]
private def twistIndexEquiv (l : ℤ) : ℤ ≃ ℤ where
  toFun d := d - l
  invFun d := d + l
  left_inv d := by
    change (d - l) + l = d
    omega
  right_inv d := by
    change (d + l) - l = d
    omega

private noncomputable def twistDirectSumAddEquiv (ℳ : ℤ → S) (l : ℤ) :
    (⨁ d : ℤ, ℳ d) ≃+ ⨁ d : ℤ, ↑(gradedModuleTwist ℳ l d) := by
  change (⨁ d : ℤ, ℳ d) ≃+ ⨁ d : ℤ, ↑(ℳ (d + l))
  exact DirectSum.equivCongrLeft (twistIndexEquiv l)

private noncomputable def twistDecomposeAddEquiv (ℳ : ℤ → S) (l : ℤ)
    [DirectSum.Decomposition ℳ] :
    M ≃+ ⨁ d : ℤ, ↑(gradedModuleTwist ℳ l d) :=
  (DirectSum.decomposeAddEquiv ℳ).trans (twistDirectSumAddEquiv ℳ l)

private theorem twistDecompose_recompose (ℳ : ℤ → S) (l : ℤ)
    [DirectSum.Decomposition ℳ]
    (x : ⨁ d : ℤ, ↑(gradedModuleTwist ℳ l d)) :
    twistDecomposeAddEquiv ℳ l
        (DirectSum.coeAddMonoidHom (gradedModuleTwist ℳ l) x) = x := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | of d x =>
      rw [DirectSum.coeAddMonoidHom_of]
      change twistDirectSumAddEquiv ℳ l
          (DirectSum.decompose ℳ (x : M)) = DirectSum.of _ d x
      rw [DirectSum.decompose_of_mem ℳ x.property]
      unfold twistDirectSumAddEquiv
      change DirectSum.equivCongrLeft (twistIndexEquiv l)
          (DirectSum.of (fun i ↦ ↑(ℳ i)) (d + l) ⟨x, x.property⟩) =
        DirectSum.of (fun i ↦ ↑(ℳ (i + l))) d x
      let y : ℳ (d + l) :=
        ⟨x, by simpa only [gradedModuleTwist_apply] using x.property⟩
      convert (DirectSum.equivCongrLeft_of (h := twistIndexEquiv l)
        (β := fun i ↦ ↑(ℳ i)) d y) using 1
      · apply congrArg
        change DirectSum.of (fun i ↦ ↑(ℳ i)) (d + l) ⟨x, x.property⟩ =
          DirectSum.of (fun i ↦ ↑(ℳ i)) (d + l) y
        apply congrArg
        apply Subtype.ext
        rfl
      · change DirectSum.of (fun i ↦ ↑(ℳ (i + l))) d x =
          DirectSum.of (fun i ↦ ↑(ℳ (i + l))) d y
        apply congrArg
        apply Subtype.ext
        rfl

/-- A direct-sum decomposition remains a direct-sum decomposition after an
integer twist. -/
noncomputable instance gradedModuleTwistDecomposition (ℳ : ℤ → S) (l : ℤ)
    [DirectSum.Decomposition ℳ] :
    DirectSum.Decomposition (gradedModuleTwist ℳ l) :=
  DirectSum.Decomposition.ofAddHom (gradedModuleTwist ℳ l)
    (twistDecomposeAddEquiv ℳ l).toAddMonoidHom
    (by
      apply AddMonoidHom.ext
      intro x
      apply (twistDecomposeAddEquiv ℳ l).injective
      change twistDecomposeAddEquiv ℳ l
          (DirectSum.coeAddMonoidHom (gradedModuleTwist ℳ l)
            (twistDecomposeAddEquiv ℳ l x)) =
        twistDecomposeAddEquiv ℳ l x
      exact twistDecompose_recompose ℳ l (twistDecomposeAddEquiv ℳ l x))
    (by
      apply AddMonoidHom.ext
      exact twistDecompose_recompose ℳ l)

end Decomposition

section GradedSMul

variable {A M SA SM : Type*} [SMul A M] [SetLike SA A] [SetLike SM M]

/-- The scalar action on a graded module remains graded after a twist: a
scalar of degree `i` sends the new degree-`j` piece, formerly degree `j + l`,
to the new degree-`i + j` piece. -/
instance gradedModuleTwistGradedSMul (𝓐 : ℤ → SA) (ℳ : ℤ → SM) (l : ℤ)
    [SetLike.GradedSMul 𝓐 ℳ] :
    SetLike.GradedSMul 𝓐 (gradedModuleTwist ℳ l) where
  smul_mem {i j a m} ha hm := by
    change a • m ∈ ℳ ((i + j) + l)
    have h := SetLike.GradedSMul.smul_mem (A := 𝓐) (B := ℳ) ha hm
    change a • m ∈ ℳ (i + (j + l)) at h
    rwa [← add_assoc] at h

end GradedSMul

/-- A graded linear equivalence is an ordinary linear equivalence whose image
on every indexed piece is exactly the corresponding target piece.  The scalar
ring of the linear equivalence need not be the scalar ring used to define the
subobjects; only their underlying sets enter the grading condition. -/
@[ext]
structure GradedLinearEquiv (R : Type*) [Semiring R]
    {M N SM SN : Type*} [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] [SetLike SM M] [SetLike SN N]
    (ℳ : ℤ → SM) (ℴ : ℤ → SN) where
  /-- The underlying ordinary linear equivalence. -/
  toLinearEquiv : M ≃ₗ[R] N
  /-- The underlying equivalence maps every source piece onto the target
  piece with the same index. -/
  map_piece : ∀ d, toLinearEquiv '' (ℳ d : Set M) = (ℴ d : Set N)

namespace GradedLinearEquiv

variable {R : Type*} [Semiring R]
  {M N P SM SN SP : Type*}
  [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
  [Module R M] [Module R N] [Module R P]
  [SetLike SM M] [SetLike SN N] [SetLike SP P]
  {ℳ : ℤ → SM} {ℴ : ℤ → SN} {𝒟 : ℤ → SP}

private theorem image_refl (s : Set M) :
    (LinearEquiv.refl R M) '' s = s := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

instance : CoeFun (GradedLinearEquiv R ℳ ℴ) (fun _ ↦ M → N) :=
  ⟨fun e ↦ e.toLinearEquiv⟩

@[simp]
theorem coe_toLinearEquiv (e : GradedLinearEquiv R ℳ ℴ) :
    ⇑e.toLinearEquiv = e := rfl

/-- A graded linear equivalence carries membership in each piece to
membership in the corresponding target piece. -/
theorem map_mem (e : GradedLinearEquiv R ℳ ℴ) {d : ℤ} {x : M}
    (hx : x ∈ ℳ d) : e x ∈ ℴ d := by
  have himage : e x ∈ e.toLinearEquiv '' (ℳ d : Set M) :=
    ⟨x, hx, rfl⟩
  rw [e.map_piece d] at himage
  exact himage

/-- The identity linear equivalence is graded. -/
def refl (ℳ : ℤ → SM) : GradedLinearEquiv R ℳ ℳ where
  toLinearEquiv := LinearEquiv.refl R M
  map_piece d := image_refl (ℳ d : Set M)

/-- The inverse of a graded linear equivalence is graded. -/
def symm (e : GradedLinearEquiv R ℳ ℴ) : GradedLinearEquiv R ℴ ℳ where
  toLinearEquiv := e.toLinearEquiv.symm
  map_piece d := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [← e.map_piece d] at hy
      rcases hy with ⟨z, hz, rfl⟩
      simpa using hz
    · intro hx
      exact ⟨e.toLinearEquiv x, e.map_mem hx, by simp⟩

/-- The composite of two graded linear equivalences is graded. -/
def trans (e : GradedLinearEquiv R ℳ ℴ) (f : GradedLinearEquiv R ℴ 𝒟) :
    GradedLinearEquiv R ℳ 𝒟 where
  toLinearEquiv := e.toLinearEquiv.trans f.toLinearEquiv
  map_piece d := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      change f.toLinearEquiv (e.toLinearEquiv y) = x at hxy
      rw [← hxy]
      exact f.map_mem (e.map_mem hy)
    · intro hx
      have hx' : x ∈ f.toLinearEquiv '' (ℴ d : Set N) := by
        rw [f.map_piece d]
        exact hx
      rcases hx' with ⟨z, hz, rfl⟩
      have hz' : z ∈ e.toLinearEquiv '' (ℳ d : Set M) := by
        rw [e.map_piece d]
        exact hz
      rcases hz' with ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩

end GradedLinearEquiv

section TwistEquivalences

variable {R M SM : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [SetLike SM M]

/-- The zero twist is graded-linearly equivalent to the original grading by
the identity map. -/
def gradedModuleTwistZeroEquiv (ℳ : ℤ → SM) :
    GradedLinearEquiv R (gradedModuleTwist ℳ 0) ℳ where
  toLinearEquiv := LinearEquiv.refl R M
  map_piece d := by
    change (LinearEquiv.refl R M) '' (ℳ (d + 0) : Set M) = (ℳ d : Set M)
    rw [add_zero]
    exact GradedLinearEquiv.image_refl (ℳ d : Set M)

/-- Successive twists by `l` and `m` are graded-linearly equivalent to the
single twist by `l + m`, again by the identity map on the underlying module. -/
def gradedModuleTwistAddEquiv (ℳ : ℤ → SM) (l m : ℤ) :
    GradedLinearEquiv R
      (gradedModuleTwist (gradedModuleTwist ℳ l) m)
      (gradedModuleTwist ℳ (l + m)) where
  toLinearEquiv := LinearEquiv.refl R M
  map_piece d := by
    change (LinearEquiv.refl R M) '' (ℳ ((d + m) + l) : Set M) =
      (ℳ (d + (l + m)) : Set M)
    rw [show (d + m) + l = d + (l + m) by omega]
    exact GradedLinearEquiv.image_refl (ℳ (d + (l + m)) : Set M)

end TwistEquivalences

end Hartshorne

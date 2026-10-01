/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.GradedModuleTwist
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule

/-!
# Integer-graded submodules and quotients

Hartshorne, *Algebraic Geometry*, I.7, Proposition 7.4 and Theorem 7.5
(pp. 50-51).

A homogeneous submodule inherits the grading by intersection with each
homogeneous piece.  Its quotient inherits the grading by the images of the
pieces.  In each degree the resulting inclusion and quotient maps form an
exact sequence.

## Main result

* `Hartshorne.gradedSubquotient_exact`
-/

namespace Hartshorne

open DirectSum

noncomputable section

variable {R A M : Type*}
  [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
  (𝓐 : ℤ → Submodule R A) [GradedAlgebra 𝓐]
  (ℳ : ℤ → Submodule R M) [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul 𝓐 ℳ]

/-- The degree-`d` piece of a homogeneous submodule, obtained by intersecting
the submodule with the degree-`d` piece of the ambient module. -/
def gradedSubmodulePiece (N : HomogeneousSubmodule 𝓐 ℳ) (d : ℤ) :
    Submodule R N :=
  (ℳ d).comap (N.toSubmodule.subtype.restrictScalars R)

/-- The degree-`d` piece of the quotient by a homogeneous submodule, obtained
as the image of the ambient degree-`d` piece under the quotient map. -/
def gradedQuotientPiece (N : HomogeneousSubmodule 𝓐 ℳ) (d : ℤ) :
    Submodule R (M ⧸ N.toSubmodule) :=
  (ℳ d).map (N.toSubmodule.mkQ.restrictScalars R)

private def gradedSubmodulePieceToAmbient
    (N : HomogeneousSubmodule 𝓐 ℳ) (d : ℤ) :
    gradedSubmodulePiece 𝓐 ℳ N d →+ ℳ d where
  toFun x := ⟨x.1.1, x.2⟩
  map_zero' := by ext; rfl
  map_add' x y := by ext; rfl

private theorem coe_map_gradedSubmodulePieceToAmbient
    (N : HomogeneousSubmodule 𝓐 ℳ)
    (z : ⨁ d, gradedSubmodulePiece 𝓐 ℳ N d) :
    DirectSum.coeAddMonoidHom ℳ
        (DirectSum.map (gradedSubmodulePieceToAmbient 𝓐 ℳ N) z) =
      ((DirectSum.coeAddMonoidHom (gradedSubmodulePiece 𝓐 ℳ N) z : N) : M) := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy =>
      rw [map_add, map_add, hx, hy]
      exact congrArg (fun q : N => (q : M))
        (map_add (DirectSum.coeAddMonoidHom
          (gradedSubmodulePiece 𝓐 ℳ N)) x y).symm
  | of d x =>
      simp only [DirectSum.map_of, DirectSum.coeAddMonoidHom_of]
      rfl

private theorem gradedSubmodulePiece_isInternal
    (N : HomogeneousSubmodule 𝓐 ℳ) :
    DirectSum.IsInternal (gradedSubmodulePiece 𝓐 ℳ N) := by
  classical
  constructor
  · intro x y hxy
    have hmap :
        DirectSum.map (gradedSubmodulePieceToAmbient 𝓐 ℳ N) x =
          DirectSum.map (gradedSubmodulePieceToAmbient 𝓐 ℳ N) y := by
      apply (DirectSum.Decomposition.isInternal (ℳ := ℳ)).injective
      rw [coe_map_gradedSubmodulePieceToAmbient,
        coe_map_gradedSubmodulePieceToAmbient, hxy]
    apply DFinsupp.ext
    intro d
    have hd := DFunLike.congr_fun hmap d
    rw [DirectSum.map_apply, DirectSum.map_apply] at hd
    have hdM : ((x d : N) : M) = ((y d : N) : M) :=
      congrArg (fun q : ℳ d => (q : M)) hd
    exact Subtype.ext (Subtype.ext hdM)
  · intro n
    let v := DirectSum.decompose ℳ (n : M)
    let z : ⨁ d, gradedSubmodulePiece 𝓐 ℳ N d :=
      DFinsupp.mk v.support fun d =>
        ⟨⟨(v d : M), N.isHomogeneous d n.property⟩,
          (v d).property⟩
    have hz : DirectSum.map (gradedSubmodulePieceToAmbient 𝓐 ℳ N) z = v := by
      apply DFinsupp.ext
      intro d
      rw [DirectSum.map_apply, DFinsupp.mk_apply]
      split_ifs with hd
      · rfl
      · have hvd : v d = 0 := DFinsupp.notMem_support_iff.1 hd
        rw [hvd]
        rfl
    refine ⟨z, ?_⟩
    apply Subtype.ext
    rw [← coe_map_gradedSubmodulePieceToAmbient 𝓐 ℳ N z, hz]
    exact (DirectSum.decompose ℳ).symm_apply_apply (n : M)

/-- The intersections of a homogeneous submodule with the ambient graded
pieces form a direct-sum decomposition of the submodule. -/
noncomputable instance gradedSubmodulePieceDecomposition
    (N : HomogeneousSubmodule 𝓐 ℳ) :
    DirectSum.Decomposition (gradedSubmodulePiece 𝓐 ℳ N) :=
  DirectSum.IsInternal.chooseDecomposition
    (gradedSubmodulePiece 𝓐 ℳ N)
    (gradedSubmodulePiece_isInternal 𝓐 ℳ N)

/-- The quotient map restricted to one ambient graded piece. -/
def gradedQuotientPieceHom (N : HomogeneousSubmodule 𝓐 ℳ) (d : ℤ) :
    ℳ d →+ gradedQuotientPiece 𝓐 ℳ N d where
  toFun x := ⟨Submodule.Quotient.mk x, ⟨x, x.2, rfl⟩⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

private theorem gradedQuotientDecompose_wd
    (N : HomogeneousSubmodule 𝓐 ℳ) {a b : M}
    (h : N.toSubmodule.quotientRel a b) :
    DirectSum.map (gradedQuotientPieceHom 𝓐 ℳ N)
        (DirectSum.decompose ℳ a) =
      DirectSum.map (gradedQuotientPieceHom 𝓐 ℳ N)
        (DirectSum.decompose ℳ b) := by
  rw [Submodule.quotientRel_def] at h
  apply DFinsupp.ext
  intro d
  rw [DirectSum.map_apply, DirectSum.map_apply]
  apply Subtype.ext
  show Submodule.Quotient.mk
      (DirectSum.decompose ℳ a d : M) =
    Submodule.Quotient.mk (DirectSum.decompose ℳ b d : M)
  rw [Submodule.Quotient.eq]
  have hd : (DirectSum.decompose ℳ (a - b) d : M) =
      (DirectSum.decompose ℳ a d : M) -
        (DirectSum.decompose ℳ b d : M) := by
    rw [show DirectSum.decompose ℳ (a - b) =
      DirectSum.decompose ℳ a - DirectSum.decompose ℳ b from
        map_sub (DirectSum.decomposeAddEquiv ℳ) a b]
    simp
  have hmem := N.isHomogeneous d h
  rwa [hd] at hmem

private noncomputable def gradedQuotientDecomposeHom
    (N : HomogeneousSubmodule 𝓐 ℳ) :
    (M ⧸ N.toSubmodule) →+ ⨁ d, gradedQuotientPiece 𝓐 ℳ N d :=
  AddMonoidHom.mk'
    (show (M ⧸ N.toSubmodule) →
        ⨁ d, gradedQuotientPiece 𝓐 ℳ N d from
      Quotient.lift
        (fun a => DirectSum.map (gradedQuotientPieceHom 𝓐 ℳ N)
          (DirectSum.decompose ℳ a))
        (fun _ _ h => gradedQuotientDecompose_wd 𝓐 ℳ N h))
    (by
      rintro ⟨a⟩ ⟨b⟩
      show DirectSum.map _ (DirectSum.decompose ℳ (a + b)) = _
      rw [DirectSum.decompose_add, map_add])

private theorem coe_map_gradedQuotientPieceHom
    (N : HomogeneousSubmodule 𝓐 ℳ)
    (z : ⨁ d, ℳ d) :
    DirectSum.coeAddMonoidHom (gradedQuotientPiece 𝓐 ℳ N)
        (DirectSum.map (gradedQuotientPieceHom 𝓐 ℳ N) z) =
      Submodule.Quotient.mk (DirectSum.coeAddMonoidHom ℳ z) := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | of d x => simp [DirectSum.coeAddMonoidHom_of, gradedQuotientPieceHom]

/-- The images of the ambient graded pieces form a direct-sum decomposition
of the quotient by a homogeneous submodule. -/
noncomputable instance gradedQuotientPieceDecomposition
    (N : HomogeneousSubmodule 𝓐 ℳ) :
    DirectSum.Decomposition (gradedQuotientPiece 𝓐 ℳ N) :=
  DirectSum.Decomposition.ofAddHom (gradedQuotientPiece 𝓐 ℳ N)
    (gradedQuotientDecomposeHom 𝓐 ℳ N)
    (by
      apply AddMonoidHom.ext
      rintro ⟨a⟩
      show DirectSum.coeAddMonoidHom _
          (DirectSum.map _ (DirectSum.decompose ℳ a)) = _
      rw [coe_map_gradedQuotientPieceHom]
      change Submodule.Quotient.mk
          (DirectSum.coeAddMonoidHom ℳ (DirectSum.decompose ℳ a)) =
        Submodule.Quotient.mk a
      have hco : DirectSum.coeAddMonoidHom ℳ (DirectSum.decompose ℳ a) = a :=
        (DirectSum.decompose ℳ).symm_apply_apply a
      rw [hco])
    (by
      apply AddMonoidHom.ext
      intro z
      induction z using DirectSum.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy, AddMonoidHom.id_apply]
      | of d y =>
          obtain ⟨a, ha, hay⟩ := y.2
          show gradedQuotientDecomposeHom 𝓐 ℳ N
              (DirectSum.coeAddMonoidHom _ (DirectSum.of _ d y)) = _
          rw [DirectSum.coeAddMonoidHom_of, ← hay]
          show DirectSum.map _ (DirectSum.decompose ℳ a) = _
          rw [DirectSum.decompose_of_mem ℳ ha, DirectSum.map_of]
          exact congrArg (DirectSum.of _ d) (Subtype.ext hay))

/-- The induced grading on a homogeneous submodule is compatible with the
graded scalar action. -/
instance gradedSubmodulePieceGradedSMul
    (N : HomogeneousSubmodule 𝓐 ℳ) :
    SetLike.GradedSMul 𝓐 (gradedSubmodulePiece 𝓐 ℳ N) where
  smul_mem {i j a m} ha hm := by
    change a • (m : M) ∈ ℳ (i + j)
    exact SetLike.GradedSMul.smul_mem (A := 𝓐) (B := ℳ) ha hm

/-- The induced grading on the quotient by a homogeneous submodule is
compatible with the graded scalar action. -/
instance gradedQuotientPieceGradedSMul
    (N : HomogeneousSubmodule 𝓐 ℳ) :
    SetLike.GradedSMul 𝓐 (gradedQuotientPiece 𝓐 ℳ N) where
  smul_mem {i j a q} ha hq := by
    obtain ⟨m, hm, rfl⟩ := hq
    refine ⟨a • m,
      SetLike.GradedSMul.smul_mem (A := 𝓐) (B := ℳ) ha hm, ?_⟩
    simp

/-- The inclusion of the degree-`d` part of a homogeneous submodule into the
ambient degree-`d` piece. -/
def gradedSubmodulePieceInclusion
    (N : HomogeneousSubmodule 𝓐 ℳ) (d : ℤ) :
    gradedSubmodulePiece 𝓐 ℳ N d →ₗ[R] ℳ d where
  toFun x := ⟨x.1.1, x.2⟩
  map_add' x y := by ext; rfl
  map_smul' r x := by ext; rfl

/-- The quotient map from the ambient degree-`d` piece onto the induced
degree-`d` quotient piece. -/
def gradedQuotientPieceMap
    (N : HomogeneousSubmodule 𝓐 ℳ) (d : ℤ) :
    ℳ d →ₗ[R] gradedQuotientPiece 𝓐 ℳ N d where
  toFun x := ⟨Submodule.Quotient.mk x, ⟨x, x.2, rfl⟩⟩
  map_add' x y := by ext; simp
  map_smul' r x := by ext; simp

/-- The componentwise sequence

`0 → N_d → M_d → (M/N)_d → 0`

is short exact: the first map is injective, its range is the kernel of the
second, and the second map is surjective.  The source and target families of
these maps carry the induced direct-sum decompositions and graded scalar-action
instances above. -/
theorem gradedSubquotient_exact
    (N : HomogeneousSubmodule 𝓐 ℳ) (d : ℤ) :
    Function.Injective (gradedSubmodulePieceInclusion 𝓐 ℳ N d) ∧
      LinearMap.range (gradedSubmodulePieceInclusion 𝓐 ℳ N d) =
        LinearMap.ker (gradedQuotientPieceMap 𝓐 ℳ N d) ∧
      Function.Surjective (gradedQuotientPieceMap 𝓐 ℳ N d) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    have hxyM : ((x : N) : M) = ((y : N) : M) :=
      congrArg (fun q : ℳ d => (q : M)) hxy
    exact Subtype.ext (Subtype.ext hxyM)
  · ext x
    constructor
    · rintro ⟨y, rfl⟩
      change gradedQuotientPieceMap 𝓐 ℳ N d
          (gradedSubmodulePieceInclusion 𝓐 ℳ N d y) = 0
      apply Subtype.ext
      change Submodule.Quotient.mk (y.1.1 : M) = 0
      exact (Submodule.Quotient.mk_eq_zero N.toSubmodule).2 y.1.property
    · intro hx
      change gradedQuotientPieceMap 𝓐 ℳ N d x = 0 at hx
      have hxq : Submodule.Quotient.mk (x : M) = 0 :=
        congrArg Subtype.val hx
      have hxN : (x : M) ∈ N :=
        (Submodule.Quotient.mk_eq_zero N.toSubmodule).1 hxq
      refine ⟨⟨⟨(x : M), hxN⟩, x.property⟩, ?_⟩
      rfl
  · intro q
    obtain ⟨m, hm, hmq⟩ := q.property
    refine ⟨⟨m, hm⟩, ?_⟩
    apply Subtype.ext
    exact hmq

end

end Hartshorne

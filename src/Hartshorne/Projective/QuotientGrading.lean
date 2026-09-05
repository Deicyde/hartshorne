/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The grading on a quotient by a homogeneous ideal

Toward Hartshorne, *Algebraic Geometry*, I.3, Theorem 3.4(b) and (c).

If `A` is graded and `I` is a homogeneous ideal, then `A ⧸ I` is graded by the
images of the graded pieces. Mathlib has homogeneous ideals and graded rings but
not this, and it is what `S(Y)_(𝔭)` needs: Hartshorne's `S(Y)` is a quotient of
a polynomial ring by a homogeneous ideal, and the graded localisation of it
cannot be formed until the quotient is graded.

The decomposition is the only real content. It is obtained by pushing the
decomposition of `A` through the quotient map, and the point where homogeneity
of `I` is used is well-definedness: if `a - b ∈ I` then every graded component
of `a - b` lies in `I`, so the components of `a` and `b` agree mod `I`.

## Main definitions

* `Hartshorne.quotGrading`

## Main results

* the `SetLike.GradedMonoid` and `DirectSum.Decomposition` instances on
  `Hartshorne.quotGrading`
-/

namespace Hartshorne

open DirectSum

variable {ι R A : Type*} [DecidableEq ι] [AddMonoid ι] [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (I : HomogeneousIdeal 𝒜)

/-- The grading induced on `A ⧸ I` by a homogeneous ideal: the image of each
graded piece. -/
def quotGrading (i : ι) : Submodule R (A ⧸ I.toIdeal) :=
  (𝒜 i).map (Ideal.Quotient.mkₐ R I.toIdeal).toLinearMap

instance : SetLike.GradedMonoid (quotGrading 𝒜 I) where
  one_mem := ⟨1, SetLike.one_mem_graded 𝒜, rfl⟩
  mul_mem := by
    rintro i j _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, SetLike.mul_mem_graded ha hb, rfl⟩

/-- The quotient map restricted to a graded piece. -/
def quotGradingHom (i : ι) : 𝒜 i →+ quotGrading 𝒜 I i where
  toFun x := ⟨Ideal.Quotient.mk I.toIdeal x, ⟨x, x.2, rfl⟩⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

/-- Homogeneity of `I` is exactly what makes the componentwise quotient map well
defined: the graded components of `a - b` all lie in `I`. -/
theorem quotDecompose_wd {a b : A} (h : (Submodule.quotientRel I.toIdeal) a b) :
    DirectSum.map (quotGradingHom 𝒜 I) (decompose 𝒜 a)
      = DirectSum.map (quotGradingHom 𝒜 I) (decompose 𝒜 b) := by
  rw [Submodule.quotientRel_def] at h
  refine DFinsupp.ext fun i => ?_
  rw [DirectSum.map_apply, DirectSum.map_apply]
  refine Subtype.ext ?_
  show Ideal.Quotient.mk I.toIdeal _ = Ideal.Quotient.mk I.toIdeal _
  rw [Ideal.Quotient.eq]
  have hd : ((decompose 𝒜 (a - b) i : 𝒜 i) : A)
      = ((decompose 𝒜 a i : 𝒜 i) : A) - ((decompose 𝒜 b i : 𝒜 i) : A) := by
    rw [show decompose 𝒜 (a - b) = decompose 𝒜 a - decompose 𝒜 b from
      map_sub (decomposeAddEquiv 𝒜) a b]
    simp
  have hmem := I.isHomogeneous i h
  rwa [hd] at hmem

/-- The decomposition of `A ⧸ I` induced by that of `A`. -/
noncomputable def quotDecomposeHom : (A ⧸ I.toIdeal) →+ ⨁ i, quotGrading 𝒜 I i :=
  AddMonoidHom.mk'
    (show A ⧸ I.toIdeal → ⨁ i, quotGrading 𝒜 I i from
      Quotient.lift (fun a => DirectSum.map (quotGradingHom 𝒜 I) (decompose 𝒜 a))
        (fun _ _ h => quotDecompose_wd 𝒜 I h))
    (by
      rintro ⟨a⟩ ⟨b⟩
      show DirectSum.map _ (decompose 𝒜 (a + b)) = _
      rw [decompose_add, map_add])

theorem coe_map_quotGradingHom (x : ⨁ i, 𝒜 i) :
    DirectSum.coeAddMonoidHom (quotGrading 𝒜 I) (DirectSum.map (quotGradingHom 𝒜 I) x)
      = Ideal.Quotient.mk I.toIdeal (DirectSum.coeAddMonoidHom 𝒜 x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i y => simp [DirectSum.coeAddMonoidHom_of, quotGradingHom]
  | add x y hx hy => simp [hx, hy]

noncomputable instance : DirectSum.Decomposition (quotGrading 𝒜 I) :=
  DirectSum.Decomposition.ofAddHom (quotGrading 𝒜 I) (quotDecomposeHom 𝒜 I)
    (by
      refine AddMonoidHom.ext ?_
      rintro ⟨a⟩
      show DirectSum.coeAddMonoidHom _ (DirectSum.map (quotGradingHom 𝒜 I) (decompose 𝒜 a)) = _
      have hco : DirectSum.coeAddMonoidHom 𝒜 (decompose 𝒜 a) = a :=
        (DirectSum.decompose 𝒜).symm_apply_apply a
      rw [coe_map_quotGradingHom, hco]
      rfl)
    (by
      refine AddMonoidHom.ext fun z => ?_
      induction z using DirectSum.induction_on with
      | zero => simp
      | of i y =>
        obtain ⟨a, ha, hay⟩ := y.2
        show quotDecomposeHom 𝒜 I (DirectSum.coeAddMonoidHom _ (DirectSum.of _ i y)) = _
        rw [DirectSum.coeAddMonoidHom_of, ← hay]
        show DirectSum.map (quotGradingHom 𝒜 I) (decompose 𝒜 a) = _
        rw [DirectSum.decompose_of_mem 𝒜 ha, DirectSum.map_of]
        exact congrArg (DirectSum.of _ i) (Subtype.ext hay)
      | add x y hx hy => simp only [map_add, hx, hy, AddMonoidHom.id_apply])

/-- **`A ⧸ I` is graded** by the images of the graded pieces of `A`. -/
noncomputable instance instGradedAlgebraQuotGrading : GradedAlgebra (quotGrading 𝒜 I) where

end Hartshorne

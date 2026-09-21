/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Smooth.Basic

/-!
# The cotangent space of affine space

Hartshorne, *Algebraic Geometry*, I.5, proof of Theorem 5.1 (p. 32).

For a point `a : σ → k`, the ideal of the point is the kernel of evaluation
at `a`.  Its conormal module `𝑛ₐ/𝑛ₐ²` is linearly equivalent to the
coordinate space `σ → k`.  The equivalence is given by evaluating partial
derivatives at `a`.

## Main results

* `Hartshorne.ambientCotangentEquiv`: the equivalence
  `𝑛ₐ/𝑛ₐ² ≃ₗ[k] (σ → k)` for finite `σ`.
* `Hartshorne.ambientCotangentEquiv_toCotangent`: the equivalence sends a
  polynomial class to its gradient at `a`.
* `Hartshorne.aeval_pderiv_eq_zero_of_mem_affinePointIdeal_sq`: the gradient
  map vanishes on the square of the point ideal.
* `Hartshorne.ambientCotangentEquiv_generator`: the class of `X i - a i`
  maps to the `i`th standard basis vector.
-/

open MvPolynomial

namespace Hartshorne

variable {k σ : Type*} [Field k]

/-- The ideal of a point `a` in affine coordinate space: the kernel of
evaluation at `a`. -/
noncomputable def affinePointIdeal (a : σ → k) : Ideal (MvPolynomial σ k) :=
  RingHom.ker (aeval a)

/-- Polynomial generators presenting `k` by evaluation at the point `a`. -/
private noncomputable def affinePointGenerators (a : σ → k) :
    Algebra.Generators k k σ where
  val := a
  σ' := C
  aeval_val_σ' := by simp

private theorem affinePointGenerators_ker (a : σ → k) :
    (affinePointGenerators a).ker = affinePointIdeal a := by
  exact (affinePointGenerators a).ker_eq_ker_aeval_val

/-- Identify the literal point ideal with the kernel in its polynomial
presentation. -/
private noncomputable def affinePointIdealCotangentEquiv (a : σ → k) :
    (affinePointIdeal a).Cotangent ≃ₗ[k]
      (affinePointGenerators a).ker.Cotangent :=
  (Ideal.Cotangent.equivOfEq _ _ (affinePointGenerators_ker a).symm).restrictScalars k

/-- The conormal-to-differentials map for evaluation at a point is bijective.
Injectivity comes from formal smoothness of the polynomial algebra;
surjectivity comes from the conormal exact sequence and `Ω[k/k] = 0`. -/
private theorem affinePoint_cotangentComplex_bijective (a : σ → k) :
    Function.Bijective
      (affinePointGenerators a).toExtension.cotangentComplex := by
  let : Algebra.FormallySmooth k (affinePointGenerators a).toExtension.Ring :=
    Algebra.instFormallySmoothMvPolynomial σ
  constructor
  · rw [(affinePointGenerators a).toExtension.cotangentComplex_injective_iff]
    infer_instance
  · exact (LinearMap.surjective_iff_eq_zero_of_exact
      (affinePointGenerators a).toExtension.exact_cotangentComplex_toKaehler).2
        (Subsingleton.elim _ _)

/-- The cotangent equivalence before replacing finitely supported functions by
ordinary functions.  This version does not require the coordinate type to be
finite. -/
noncomputable def ambientCotangentEquivFinsupp (a : σ → k) :
    (affinePointIdeal a).Cotangent ≃ₗ[k] (σ →₀ k) :=
  affinePointIdealCotangentEquiv a ≪≫ₗ
    ((affinePointGenerators a).toExtension.cotangentEquivCotangentKer.symm.restrictScalars k) ≪≫ₗ
    LinearEquiv.ofBijective (affinePointGenerators a).toExtension.cotangentComplex
      (affinePoint_cotangentComplex_bijective a) ≪≫ₗ
    (affinePointGenerators a).cotangentSpaceBasis.repr

/-- Under `ambientCotangentEquivFinsupp`, a polynomial in the point ideal maps
to its finitely supported gradient evaluated at the point. -/
@[simp]
theorem ambientCotangentEquivFinsupp_toCotangent (a : σ → k)
    (f : affinePointIdeal a) (i : σ) :
    ambientCotangentEquivFinsupp a (Ideal.toCotangent _ f) i =
      aeval a (pderiv i f.1) := by
  let f' : (affinePointGenerators a).toExtension.ker :=
    LinearEquiv.ofEq _ _ (affinePointGenerators_ker a).symm f
  change (affinePointGenerators a).cotangentSpaceBasis.repr
      ((affinePointGenerators a).toExtension.cotangentComplex
        (Algebra.Extension.Cotangent.mk f')) i = _
  rw [Algebra.Extension.cotangentComplex_mk,
    Algebra.Generators.cotangentSpaceBasis_repr_one_tmul]
  rfl

/-- The gradient-at-`a` map vanishes on the square of the ideal of `a`, so it
factors through the cotangent quotient. -/
theorem aeval_pderiv_eq_zero_of_mem_affinePointIdeal_sq (a : σ → k)
    {f : MvPolynomial σ k} (hf : f ∈ affinePointIdeal a ^ 2) (i : σ) :
    aeval a (pderiv i f) = 0 := by
  let f' : affinePointIdeal a :=
    ⟨f, Ideal.pow_le_self (by decide) hf⟩
  calc
    aeval a (pderiv i f) =
        ambientCotangentEquivFinsupp a (Ideal.toCotangent _ f') i := by
      symm
      exact ambientCotangentEquivFinsupp_toCotangent a f' i
    _ = 0 := by
      rw [((affinePointIdeal a).toCotangent_eq_zero f').2 hf, map_zero]
      rfl

/-- The polynomial `X i - a i`, regarded as an element of the ideal of the
point `a`. -/
noncomputable def affinePointIdealGenerator (a : σ → k) (i : σ) :
    affinePointIdeal a :=
  ⟨X i - C (a i), by
    rw [affinePointIdeal, RingHom.mem_ker]
    simp⟩

/-- The gradient equivalence sends `X i - a i` to the `i`th finitely
supported standard basis vector. -/
@[simp]
theorem ambientCotangentEquivFinsupp_generator (a : σ → k) (i : σ) :
    ambientCotangentEquivFinsupp a
        (Ideal.toCotangent _ (affinePointIdealGenerator a i)) =
      Finsupp.single i 1 := by
  classical
  ext j
  rw [ambientCotangentEquivFinsupp_toCotangent]
  by_cases h : i = j
  · subst j
    simp [affinePointIdealGenerator]
  · simp [affinePointIdealGenerator, MvPolynomial.pderiv, h, Ne.symm h]

/-- **Hartshorne I.5, Theorem 5.1 (ambient-space calculation).** For a point
`a` in a finite-dimensional affine coordinate space, the cotangent quotient
`𝑛ₐ/𝑛ₐ²` is linearly equivalent to the coordinate space. -/
noncomputable def ambientCotangentEquiv [Finite σ] (a : σ → k) :
    (affinePointIdeal a).Cotangent ≃ₗ[k] (σ → k) :=
  ambientCotangentEquivFinsupp a ≪≫ₗ Finsupp.linearEquivFunOnFinite k k σ

/-- The ambient cotangent equivalence is Hartshorne's derivative map: the
class of `f` is sent to the gradient of `f` evaluated at `a`. -/
@[simp]
theorem ambientCotangentEquiv_toCotangent [Finite σ] (a : σ → k)
    (f : affinePointIdeal a) (i : σ) :
    ambientCotangentEquiv a (Ideal.toCotangent _ f) i =
      aeval a (pderiv i f.1) := by
  rw [ambientCotangentEquiv, LinearEquiv.trans_apply]
  rw [Finsupp.linearEquivFunOnFinite_apply,
    ambientCotangentEquivFinsupp_toCotangent]

/-- The class of `X i - a i` maps to the `i`th standard basis vector. -/
@[simp]
theorem ambientCotangentEquiv_generator [Finite σ] (a : σ → k) (i : σ) :
    ambientCotangentEquiv a
        (Ideal.toCotangent _ (affinePointIdealGenerator a i)) =
      Pi.basisFun k σ i := by
  classical
  rw [Pi.basisFun_apply, ambientCotangentEquiv, LinearEquiv.trans_apply,
    ambientCotangentEquivFinsupp_generator,
    Finsupp.linearEquivFunOnFinite_single]

end Hartshorne

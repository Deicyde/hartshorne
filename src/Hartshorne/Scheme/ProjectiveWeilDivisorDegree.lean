/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.NumericalBinomial
import Hartshorne.Intersection.ProjectiveHilbertPolynomial
import Hartshorne.Scheme.WeilDivisor
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# The degree of a Weil divisor on a projective scheme

Hartshorne, *Algebraic Geometry*, preamble of Exercise II.6.2 (p. 146).

Let `k` be algebraically closed and let `ι : X ⟶ ℙⁿ_k` be a closed immersion, where
`ℙⁿ_k = Proj k[x₀, ..., xₙ]` with its standard grading. A point `x` of `ℙⁿ_k` is a relevant
homogeneous prime `𝔭 ⊆ k[x₀, ..., xₙ]`; the closure of `x` corresponds to the classical
projective variety `Z(𝔭)`, and the degree of that closure is the projective degree of `Z(𝔭)` in
the sense of Chapter I, §7. The degree of a prime divisor `Y` of `X` is the degree of the closure
of the image of its generic point, i.e. the degree of `Y` as a projective variety in the fixed
embedding. For a Weil divisor `D = ∑ nᵢ Yᵢ` we set `deg D = ∑ nᵢ deg Yᵢ`.

Projective degree is integral, so these degrees are integers, and `deg` is an additive
homomorphism `Div X → ℤ`. The sum is finite because `X` is quasi-compact, being closed in the
quasi-compact scheme `ℙⁿ_k`; hence the definition needs neither integrality of `X` nor regularity
in codimension one, which Hartshorne assumes only so that `Div X` is the group of his §6.

## Main definitions

* `Hartshorne.projectiveSpectrumPointDegree`: the degree of the closure of a point of `ℙⁿ_k`.
* `Hartshorne.primeDivisorProjectiveDegree`: the degree of a prime divisor in the embedding.
* `Hartshorne.weilDivisorProjectiveDegree`: the degree homomorphism `Div X →+ ℤ`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Hartshorne

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}

/-- Projective degree is an integer: it is the top coefficient of the integral binomial-basis
expansion of the numerical Hilbert polynomial. -/
private theorem exists_intCast_eq_projectiveDegree
    (Y : Set (ProjectiveSpace k (Fin (n + 1)))) :
    ∃ d : ℤ, projectiveDegree Y = (d : ℚ) := by
  obtain ⟨c, _, _, htop⟩ :=
    (isNumericalPolynomial_iff_exists_binomialExpansion (projectiveHilbertPolynomial Y)).mp
      (projectiveHilbertPolynomial_isHilbertPolynomial Y).1
  exact ⟨c (projectiveHilbertPolynomial Y).natDegree, htop⟩

/-- The degree of the closure of a point `x` of `ℙⁿ_k = Proj k[x₀, ..., xₙ]`: the projective
degree of the classical algebraic set `Z(𝔭)` cut out by the homogeneous prime `𝔭` of `x`. -/
def projectiveSpectrumPointDegree
    (x : ProjectiveSpectrum (homogeneousSubmodule (Fin (n + 1)) k)) : ℤ :=
  ⌊projectiveDegree (projZeroSet (x.asHomogeneousIdeal : Set (MvPolynomial (Fin (n + 1)) k)))⌋

/-- The integer degree of a point of `ℙⁿ_k` is the projective degree of its closure. -/
theorem projectiveSpectrumPointDegree_cast
    (x : ProjectiveSpectrum (homogeneousSubmodule (Fin (n + 1)) k)) :
    (projectiveSpectrumPointDegree x : ℚ) =
      projectiveDegree
        (projZeroSet (x.asHomogeneousIdeal : Set (MvPolynomial (Fin (n + 1)) k))) := by
  obtain ⟨d, hd⟩ := exists_intCast_eq_projectiveDegree
    (projZeroSet (x.asHomogeneousIdeal : Set (MvPolynomial (Fin (n + 1)) k)))
  rw [projectiveSpectrumPointDegree, hd, Int.floor_intCast]

variable {X : Scheme.{u}}

/-- The degree of a prime divisor `Y` of `X` in the embedding `ι : X ⟶ ℙⁿ_k`: the projective
degree of the closure in `ℙⁿ_k` of the image of the generic point of `Y`. -/
def primeDivisorProjectiveDegree
    (ι : X ⟶ Proj (homogeneousSubmodule (Fin (n + 1)) k)) (P : X.PrimeDivisor) : ℤ :=
  projectiveSpectrumPointDegree (ι.base P.1)

omit [IsAlgClosed k] in
/-- A closed subscheme of `ℙⁿ_k` is quasi-compact. -/
theorem compactSpace_of_isClosedImmersion_projectiveSpace
    (ι : X ⟶ Proj (homogeneousSubmodule (Fin (n + 1)) k)) [IsClosedImmersion ι] :
    CompactSpace X := by
  let σ := Fin (n + 1)
  let 𝒜 := homogeneousSubmodule σ k
  let _ : IsScalarTower k (𝒜 0) (MvPolynomial σ k) :=
    IsScalarTower.of_algebraMap_eq (R := k) (S := 𝒜 0) (A := MvPolynomial σ k) fun _ ↦ rfl
  let _ : Algebra.FiniteType (𝒜 0) (MvPolynomial σ k) :=
    Algebra.FiniteType.of_restrictScalars_finiteType (R := k) (S := 𝒜 0) (A := MvPolynomial σ k)
  exact QuasiCompact.compactSpace_of_compactSpace (ι ≫ Proj.toSpecZero 𝒜)

omit [IsAlgClosed k] in
/-- A Weil divisor on a closed subscheme of `ℙⁿ_k` has only finitely many nonzero coefficients
at prime divisors. -/
theorem finite_support_primeDivisor_of_isClosedImmersion
    (ι : X ⟶ Proj (homogeneousSubmodule (Fin (n + 1)) k)) [IsClosedImmersion ι]
    (D : X.WeilDivisor) :
    (Function.support fun P : X.PrimeDivisor ↦ D.1 P.1).Finite := by
  have := compactSpace_of_isClosedImmersion_projectiveSpace ι
  have h := D.1.locallyFiniteSupport.finite_inter_support_of_isCompact isCompact_univ
  rw [Set.univ_inter] at h
  exact h.preimage Subtype.val_injective.injOn

/-- **Hartshorne, preamble of Exercise II.6.2.** The degree of Weil divisors on a closed
subscheme `ι : X ⟶ ℙⁿ_k`: the additive homomorphism `Div X → ℤ` sending
`D = ∑ nᵢ Yᵢ` to `∑ nᵢ deg Yᵢ`, where `deg Yᵢ` is the projective degree of `Yᵢ` in the fixed
embedding. -/
def weilDivisorProjectiveDegree
    (ι : X ⟶ Proj (homogeneousSubmodule (Fin (n + 1)) k)) [IsClosedImmersion ι] :
    X.WeilDivisor →+ ℤ where
  toFun D := ∑ᶠ P : X.PrimeDivisor, D.1 P.1 * primeDivisorProjectiveDegree ι P
  map_zero' := by simp
  map_add' D E := by
    have hD := (finite_support_primeDivisor_of_isClosedImmersion ι D).subset
      (Function.support_mul_subset_left (fun P : X.PrimeDivisor ↦ D.1 P.1)
        (primeDivisorProjectiveDegree ι))
    have hE := (finite_support_primeDivisor_of_isClosedImmersion ι E).subset
      (Function.support_mul_subset_left (fun P : X.PrimeDivisor ↦ E.1 P.1)
        (primeDivisorProjectiveDegree ι))
    simp only [AddSubgroup.coe_add, Function.locallyFinsuppWithin.coe_add, Pi.add_apply,
      add_mul]
    exact finsum_add_distrib hD hE

/-- The degree of a Weil divisor is the weighted sum of the degrees of its prime divisors. -/
theorem weilDivisorProjectiveDegree_apply
    (ι : X ⟶ Proj (homogeneousSubmodule (Fin (n + 1)) k)) [IsClosedImmersion ι]
    (D : X.WeilDivisor) :
    weilDivisorProjectiveDegree ι D =
      ∑ᶠ P : X.PrimeDivisor, D.1 P.1 * primeDivisorProjectiveDegree ι P :=
  rfl

/-- On the generator `1 · Y` of `Div X` attached to a prime divisor `Y`, the degree homomorphism
takes the value `deg Y`. -/
theorem weilDivisorProjectiveDegree_of_primeDivisor
    (ι : X ⟶ Proj (homogeneousSubmodule (Fin (n + 1)) k)) [IsClosedImmersion ι]
    (P : X.PrimeDivisor) (D : X.WeilDivisor) (hP : D.1 P.1 = 1)
    (hD : ∀ x, x ≠ P.1 → D.1 x = 0) :
    weilDivisorProjectiveDegree ι D = primeDivisorProjectiveDegree ι P := by
  rw [weilDivisorProjectiveDegree_apply, finsum_eq_single _ P]
  · rw [hP, one_mul]
  · intro Q hQ
    rw [hD Q.1 fun h ↦ hQ (Subtype.ext h), zero_mul]

end Hartshorne

/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.QuadricSurfaceHyperplane

/-!
# The homomorphism `Cl ℙ³ → Cl Q` induced by the quadric surface

Hartshorne, *Algebraic Geometry*, II, Example 6.6.2 (pp. 135–136).

Let `Q ⊆ ℙ³_k` be the split quadric (`Hartshorne.quadricSurfaceι`). The embedding induces a
homomorphism `Cl ℙ³_k → Cl Q` (`Hartshorne.quadricAmbientClassGroupHom`): it sends the class of
a divisor `D` none of whose components contains `Q` to the class of the divisor `D · Q` cut on `Q`
(`Hartshorne.quadricAmbientClassGroupHom_weilDivisorClassHom`), every class of `Cl ℙ³_k` is the
class of such a divisor (`Hartshorne.exists_weilDivisorClassHom_eq_of_quadric`), and the class of
a hyperplane goes to `(1, 1)` (`Hartshorne.quadricSurfaceClassGroupEquiv_quadricAmbientClassGroupHom_hyperplane`).

## Proof

A prime divisor `V` of `ℙ³_k` with equation `F` of degree `d`, not containing `Q`, cuts on `Q` the
divisor `d · ((x = 0) · Q) + div(F / x^d)`: at a point off `X_i = 0` the coefficient of `V · Q` is
the order of `F / X_i^d`, and `F / X_i^d = (F / x^d) (x / X_i)^d`. Since `(x = 0) · Q = L₁ + L₂`
has class `(1, 1)`, the class of `V · Q` is `(d, d)`, and by linearity the class of `D · Q` is
`deg D · (1, 1)`. The homomorphism is therefore `[D] ↦ deg D · (1, 1)` under
`Cl ℙ³_k ≅ ℤ` (Proposition II.6.4) and `Cl Q ≅ ℤ × ℤ`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Order

namespace Hartshorne

universe u

variable (k : Type u) [Field k]

local notation "𝒬" => quadricGrading k

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "𝒮" => MvPolynomial.homogeneousSubmodule (Fin (3 + 1)) k

local notation "hQ" => quadricSurface_satisfiesConditionStar k

local notation "hP" => projectiveSpace_satisfiesConditionStar (k := k) (n := 3)

/-- The image in the coordinate ring of `Q` of a homogeneous polynomial of degree `d`. -/
theorem quadricCoordinateHom_mem_of_isHomogeneous' {F : MvPolynomial (Fin (3 + 1)) k} {d : ℕ}
    (hF : F.IsHomogeneous d) : quadricCoordinateHom k F ∈ 𝒬 d :=
  (quadricCoordinateHom k).map_mem ((MvPolynomial.mem_homogeneousSubmodule d F).mpr hF)

theorem quadricCoordinateHom_X_pow_ne_zero (i : Fin (3 + 1)) (d : ℕ) :
    quadricCoordinateHom k (MvPolynomial.X i ^ d) ≠ 0 := by
  rw [map_pow]
  have : IsDomain (QuadricRing k) := inferInstance
  exact pow_ne_zero _ (quadricCoordinateHom_X_ne_zero k i)

theorem quadricCoordinateHom_X_pow_mem (i : Fin (3 + 1)) (m : ℕ) :
    quadricCoordinateHom k (MvPolynomial.X i) ^ m ∈ 𝒬 m := by
  simpa using SetLike.pow_mem_graded m (quadricCoordinateHom_X_mem k i)

/-- The equation of a prime divisor of `ℙ³_k` not containing `Q` does not vanish on `Q`. -/
theorem quadricCoordinateHom_equation_ne_zero (V : (Proj 𝒮).PrimeDivisor)
    (hV : ¬Set.range (quadricSurfaceι k).base ⊆ closure ({V.1} : Set (Proj 𝒮))) :
    quadricCoordinateHom k (projectivePrimeDivisorEquation V) ≠ 0 := by
  intro h0
  apply hV
  rintro _ ⟨x, rfl⟩
  rw [mem_closure_projectivePrimeDivisor_iff]
  change quadricCoordinateHom k (projectivePrimeDivisorEquation V) ∈ x.asHomogeneousIdeal
  rw [h0]
  exact zero_mem _

set_option backward.isDefEq.respectTransparency false in
/-- **The coefficients of a hypersurface section.** For a prime divisor `V` of `ℙ³_k` with
equation `F` of degree `d`, not containing `Q`, and a point `x` of `Q` off `X_i = 0`, the
coefficient of `V · Q` at `x` is the order at `x` of `F / X_i^d`. -/
theorem quadricHypersurfaceSection_apply (V : (Proj 𝒮).PrimeDivisor)
    (hV : ¬Set.range (quadricSurfaceι k).base ⊆ closure ({V.1} : Set (Proj 𝒮)))
    (x : quadricSurface k) (i : Fin (3 + 1))
    (hi : quadricCoordinateHom k (MvPolynomial.X i) ∉ x.asHomogeneousIdeal) :
    (projectiveIntersectionDivisor (quadricSurfaceι k) hQ V).1 x =
      (quadricSurface k).ord (projHomogeneousFraction 𝒬
        (quadricCoordinateHom_mem_of_isHomogeneous' k
          (projectivePrimeDivisorEquation_isHomogeneous V))
        (quadricCoordinateHom_mem_of_isHomogeneous' k
          (MvPolynomial.isHomogeneous_X_pow i (projectivePrimeDivisorEquationDegree V)))
        (quadricCoordinateHom_X_pow_ne_zero k i _)) x := by
  set d := projectivePrimeDivisorEquationDegree V
  have hx : (quadricSurfaceι k).base x ∈ Proj.basicOpen 𝒮 (MvPolynomial.X i ^ d) := by
    change quadricCoordinateHom k (MvPolynomial.X i ^ d) ∉ x.asHomogeneousIdeal
    rw [map_pow]
    exact fun h ↦ hi (x.isPrime.mem_of_pow_mem d h)
  have hh := isProjectiveHypersurfaceLocalEquation_chartEquation V (MvPolynomial.X i ^ d)
    (MvPolynomial.isHomogeneous_X_pow i d)
  have h := projectiveIntersectionDivisor_apply_eq_ord (quadricSurfaceι k) hQ V hV x _ _ hx hh
  dsimp only at h
  rw [h]
  congr 1
  have : Nonempty ((quadricSurfaceι k) ⁻¹ᵁ Proj.basicOpen 𝒮 (MvPolynomial.X i ^ d)) :=
    ⟨⟨x, hx⟩⟩
  rw [Scheme.algebraMap_germ_eq_germToFunctionField, ← germ_awayToSection_mk]
  have happ := ConcreteCategory.congr_hom (Proj.awayToSection_comp_appLE
    (quadricCoordinateHom k) (irrelevant_le_map_quadricCoordinateHom k)
    ((MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)))
    (HomogeneousLocalization.mk ⟨d, ⟨projectivePrimeDivisorEquation V,
        (MvPolynomial.mem_homogeneousSubmodule d _).mpr
          (projectivePrimeDivisorEquation_isHomogeneous V)⟩,
      ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
        (MvPolynomial.isHomogeneous_X_pow i d)⟩, Submonoid.mem_powers _⟩)
  rw [Scheme.Hom.app_eq_appLE]
  exact congrArg _ happ

/-- The order of `x^m / X_i^m` is `m` times the order of `x / X_i`. -/
theorem ord_quadric_projHomogeneousFraction_pow (i : Fin (3 + 1)) (x : quadricSurface k)
    (m : ℕ) :
    (quadricSurface k).ord (projHomogeneousFraction 𝒬
        (quadricCoordinateHom_X_pow_mem k 0 m)
        (quadricCoordinateHom_X_pow_mem k i m)
        (pow_ne_zero m (quadricCoordinateHom_X_ne_zero k i))) x =
      m * (quadricSurface k).ord (projHomogeneousFraction 𝒬 (quadricCoordinateHom_X_mem k 0)
        (quadricCoordinateHom_X_mem k i) (quadricCoordinateHom_X_ne_zero k i)) x := by
  induction m with
  | zero =>
    rw [projHomogeneousFraction_eq_of_mul_eq 𝒬 _ _ _
      (quadricCoordinateHom_X_pow_mem k i 0) (quadricCoordinateHom_X_pow_mem k i 0)
      (pow_ne_zero 0 (quadricCoordinateHom_X_ne_zero k i)) (by ring),
      projHomogeneousFraction_self, Scheme.ord_one_eq_zero, Nat.cast_zero, zero_mul]
  | succ m ih =>
    have hmul := projHomogeneousFraction_mul 𝒬
      (quadricCoordinateHom_X_pow_mem k 0 m)
      (quadricCoordinateHom_X_pow_mem k i m)
      (pow_ne_zero m (quadricCoordinateHom_X_ne_zero k i)) (quadricCoordinateHom_X_mem k 0)
      (quadricCoordinateHom_X_mem k i) (quadricCoordinateHom_X_ne_zero k i)
    rw [projHomogeneousFraction_eq_of_mul_eq 𝒬 _ _ _ (SetLike.mul_mem_graded
      (quadricCoordinateHom_X_pow_mem k 0 m) (quadricCoordinateHom_X_mem k 0))
      (SetLike.mul_mem_graded (quadricCoordinateHom_X_pow_mem k i m)
        (quadricCoordinateHom_X_mem k i))
      (mul_ne_zero (pow_ne_zero m (quadricCoordinateHom_X_ne_zero k i))
        (quadricCoordinateHom_X_ne_zero k i)) (by ring), ← hmul,
      Scheme.ord_mul (projHomogeneousFraction_ne_zero 𝒬 _ _ _
        (pow_ne_zero m (quadricCoordinateHom_X_ne_zero k 0)))
        (projHomogeneousFraction_ne_zero 𝒬 _ _ _ (quadricCoordinateHom_X_ne_zero k 0)), ih]
    push_cast
    ring

/-- The rational function `F / x^d` on `Q`, for the equation `F` of degree `d` of a prime divisor
of `ℙ³_k` not containing `Q`. -/
def quadricHypersurfaceRatio (V : (Proj 𝒮).PrimeDivisor)
    (hV : ¬Set.range (quadricSurfaceι k).base ⊆ closure ({V.1} : Set (Proj 𝒮))) :
    (quadricSurface k).functionFieldˣ :=
  Units.mk0 (projHomogeneousFraction 𝒬
      (quadricCoordinateHom_mem_of_isHomogeneous' k
        (projectivePrimeDivisorEquation_isHomogeneous V))
      (quadricCoordinateHom_X_pow_mem k 0 (projectivePrimeDivisorEquationDegree V))
      (pow_ne_zero _ (quadricCoordinateHom_X_ne_zero k 0)))
    (projHomogeneousFraction_ne_zero 𝒬 _ _ _ (quadricCoordinateHom_equation_ne_zero k V hV))

/-- **Hypersurface sections.** A prime divisor `V` of `ℙ³_k` of degree `d` not containing `Q` cuts
`V · Q = d · ((x = 0) · Q) + div(F / x^d)`. -/
theorem quadricHypersurfaceSection_eq (V : (Proj 𝒮).PrimeDivisor)
    (hV : ¬Set.range (quadricSurfaceι k).base ⊆ closure ({V.1} : Set (Proj 𝒮))) :
    projectiveIntersectionDivisor (quadricSurfaceι k) hQ V =
      (projectivePrimeDivisorEquationDegree V : ℤ) •
          projectiveIntersectionDivisor (quadricSurfaceι k) hQ (quadricHyperplaneX k) +
        (quadricSurface k).principalDivisor hQ (quadricHypersurfaceRatio k V hV) := by
  apply Scheme.WeilDivisor.ext_apply
  intro x
  simp only [AddSubgroup.coe_add, Function.locallyFinsuppWithin.coe_add, Pi.add_apply,
    AddSubgroup.coe_zsmul, Function.locallyFinsuppWithin.coe_zsmul, Pi.smul_apply, smul_eq_mul]
  rw [Scheme.principalDivisor_apply hQ]
  obtain ⟨i, hi⟩ := quadric_exists_coordinate_notMem k x
  set d := projectivePrimeDivisorEquationDegree V
  rw [quadricHypersurfaceSection_apply k V hV x i hi,
    quadricHyperplaneSection_apply k _ _ x i hi, quadricHypersurfaceRatio, Units.val_mk0,
    ← ord_quadric_projHomogeneousFraction_pow k i x d]
  have h := Scheme.ord_mul (x := x)
    (projHomogeneousFraction_ne_zero 𝒬 (quadricCoordinateHom_mem_of_isHomogeneous' k
        (projectivePrimeDivisorEquation_isHomogeneous V)) (quadricCoordinateHom_X_pow_mem k 0 d)
      (pow_ne_zero d (quadricCoordinateHom_X_ne_zero k 0))
      (quadricCoordinateHom_equation_ne_zero k V hV))
    (projHomogeneousFraction_ne_zero 𝒬 (quadricCoordinateHom_X_pow_mem k 0 d)
      (quadricCoordinateHom_X_pow_mem k i d) (pow_ne_zero d (quadricCoordinateHom_X_ne_zero k i))
      (pow_ne_zero d (quadricCoordinateHom_X_ne_zero k 0)))
  rw [projHomogeneousFraction_mul, projHomogeneousFraction_eq_of_mul_eq 𝒬 _ _ _
    (quadricCoordinateHom_mem_of_isHomogeneous' k
      (projectivePrimeDivisorEquation_isHomogeneous V))
    (quadricCoordinateHom_mem_of_isHomogeneous' k (MvPolynomial.isHomogeneous_X_pow i d))
    (quadricCoordinateHom_X_pow_ne_zero k i d) (by rw [map_pow]; ring)] at h
  rw [h]
  ring

/-- The divisor cut on `Q` by a prime divisor of degree `d` not containing `Q` has class
`(d, d)`. -/
theorem quadricSurfaceClassGroupEquiv_hypersurfaceSection (V : (Proj 𝒮).PrimeDivisor)
    (hV : ¬Set.range (quadricSurfaceι k).base ⊆ closure ({V.1} : Set (Proj 𝒮))) :
    quadricSurfaceClassGroupEquiv k ((quadricSurface k).weilDivisorClassHom hQ
      (projectiveIntersectionDivisor (quadricSurfaceι k) hQ V)) =
      (projectivePrimeDivisorEquationDegree V : ℤ) • (1, 1) := by
  have hcl : (quadricSurface k).weilDivisorClassHom hQ
      (projectiveIntersectionDivisor (quadricSurfaceι k) hQ V) =
      (quadricSurface k).weilDivisorClassHom hQ ((projectivePrimeDivisorEquationDegree V : ℤ) •
        ((quadricLineOneDivisor k).toWeilDivisor + (quadricLineTwoDivisor k).toWeilDivisor)) := by
    refine ((quadricSurface k).weilDivisorClass_eq_iff hQ _ _).mpr
      ⟨quadricHypersurfaceRatio k V hV, ?_⟩
    rw [quadricHypersurfaceSection_eq k V hV, quadricHyperplaneSection_X, add_sub_cancel_left]
  rw [hcl, map_zsmul, map_zsmul, quadricSurfaceClassGroupEquiv_lineOne_add_lineTwo]

/-- The divisor cut on `Q` by a divisor `D` of `ℙ³_k` none of whose components contains `Q` has
class `deg D · (1, 1)`. -/
theorem quadricSurfaceClassGroupEquiv_projectiveIntersectionDivisorHom
    (D : ambientDivisorsNotContaining (quadricSurfaceι k)) :
    quadricSurfaceClassGroupEquiv k ((quadricSurface k).weilDivisorClassHom hQ
      (projectiveIntersectionDivisorHom (quadricSurfaceι k) hQ D)) =
      projectiveSpaceWeilDivisorDegree (D : (Proj 𝒮).WeilDivisor) • (1, 1) := by
  let c : (quadricSurface k).WeilDivisor →+ ℤ × ℤ :=
    (quadricSurfaceClassGroupEquiv k).toAddMonoidHom.comp
      ((quadricSurface k).weilDivisorClassHom hQ)
  have hfin := finite_support_primeDivisor_of_isClosedImmersion (𝟙 (Proj 𝒮))
    (D : (Proj 𝒮).WeilDivisor)
  change c (∑ᶠ V : (Proj 𝒮).PrimeDivisor,
    (D : (Proj 𝒮).WeilDivisor).1 V.1 • projectiveIntersectionDivisor (quadricSurfaceι k) hQ V) = _
  have hfin' : (Function.support fun V : (Proj 𝒮).PrimeDivisor ↦
      (D : (Proj 𝒮).WeilDivisor).1 V.1 •
        projectiveIntersectionDivisor (quadricSurfaceι k) hQ V).Finite :=
    hfin.subset fun V hV h ↦ hV (by simp only [h, zero_smul])
  rw [map_finsum c hfin',
    projectiveSpaceWeilDivisorDegree_apply,
    finsum_smul' (hfin.subset fun V hV ↦ left_ne_zero_of_mul hV)]
  refine finsum_congr fun V ↦ ?_
  dsimp only
  by_cases hDV : (D : (Proj 𝒮).WeilDivisor).1 V.1 = 0
  · simp only [hDV, zero_smul, map_zero, zero_mul]
  · rw [map_zsmul]
    change _ • quadricSurfaceClassGroupEquiv k _ = _
    rw [quadricSurfaceClassGroupEquiv_hypersurfaceSection k V (D.2 V hDV), smul_smul]

/-- **The homomorphism `Cl ℙ³_k → Cl Q` induced by the embedding** (Hartshorne II,
Example 6.6.2): under `Cl ℙ³_k ≅ ℤ` and `Cl Q ≅ ℤ × ℤ` it is `n ↦ (n, n)`; it sends the class of a
divisor none of whose components contains `Q` to the class of the divisor it cuts on `Q`
(`Hartshorne.quadricAmbientClassGroupHom_weilDivisorClassHom`). -/
def quadricAmbientClassGroupHom :
    (Proj 𝒮).WeilClassGroup hP →+ (quadricSurface k).WeilClassGroup hQ :=
  ((quadricSurfaceClassGroupEquiv k).symm.toAddMonoidHom.comp
      (zmultiplesHom (ℤ × ℤ) (1, 1))).comp
    (projectiveSpaceClassGroupEquiv (n := 3) (by norm_num)).toAddMonoidHom

theorem quadricSurfaceClassGroupEquiv_quadricAmbientClassGroupHom
    (c : (Proj 𝒮).WeilClassGroup hP) :
    quadricSurfaceClassGroupEquiv k (quadricAmbientClassGroupHom k c) =
      projectiveSpaceClassGroupEquiv (n := 3) (by norm_num) c • (1, 1) := by
  simp [quadricAmbientClassGroupHom]

/-- **Compatibility with cutting divisors.** The homomorphism `Cl ℙ³_k → Cl Q` sends the class of
a divisor `D` none of whose components contains `Q` to the class of `D · Q`. -/
theorem quadricAmbientClassGroupHom_weilDivisorClassHom
    (D : ambientDivisorsNotContaining (quadricSurfaceι k)) :
    quadricAmbientClassGroupHom k ((Proj 𝒮).weilDivisorClassHom hP D) =
      (quadricSurface k).weilDivisorClassHom hQ
        (projectiveIntersectionDivisorHom (quadricSurfaceι k) hQ D) := by
  apply (quadricSurfaceClassGroupEquiv k).injective
  rw [quadricSurfaceClassGroupEquiv_quadricAmbientClassGroupHom,
    quadricSurfaceClassGroupEquiv_projectiveIntersectionDivisorHom,
    projectiveSpaceClassGroupEquiv_weilDivisorClassHom]

/-- Every class of `Cl ℙ³_k` is the class of a divisor none of whose components contains `Q`. -/
theorem exists_weilDivisorClassHom_eq_of_quadric (c : (Proj 𝒮).WeilClassGroup hP) :
    ∃ D : ambientDivisorsNotContaining (quadricSurfaceι k),
      (Proj 𝒮).weilDivisorClassHom hP D = c := by
  set H := projectiveHyperplanePrimeDivisor (n := 3) (by norm_num)
    (MvPolynomial.isHomogeneous_X k 0) (MvPolynomial.X_ne_zero 0)
  set m := projectiveSpaceClassGroupEquiv (n := 3) (by norm_num) c
  have hmem : m • H.toWeilDivisor ∈ ambientDivisorsNotContaining (quadricSurfaceι k) := by
    intro V hV
    have hVH : V = H := by
      by_contra hne
      apply hV
      change m * H.toWeilDivisor.1 V.1 = 0
      rw [H.toWeilDivisor_apply_of_ne fun h ↦ hne (Subtype.ext h), mul_zero]
    rw [hVH]
    exact quadricSurface_not_subset_hyperplane k (MvPolynomial.isHomogeneous_X k 0)
      (MvPolynomial.X_ne_zero 0)
  refine ⟨⟨_, hmem⟩, (projectiveSpaceClassGroupEquiv (n := 3) (by norm_num)).injective ?_⟩
  change projectiveSpaceClassGroupEquiv (n := 3) (by norm_num)
    ((Proj 𝒮).weilDivisorClassHom hP (m • H.toWeilDivisor)) = m
  rw [map_zsmul, map_zsmul, projectiveSpaceClassGroupEquiv_hyperplane, smul_eq_mul, mul_one]

/-- **The hyperplane class goes to `(1, 1)`** (Hartshorne II, Example 6.6.2): the image in
`Cl Q ≅ ℤ × ℤ` of the class of a hyperplane `H`, which generates `Cl ℙ³_k`, is `(1, 1)`. -/
theorem quadricSurfaceClassGroupEquiv_quadricAmbientClassGroupHom_hyperplane
    {ℓ : MvPolynomial (Fin (3 + 1)) k} (hℓ : ℓ.IsHomogeneous 1) (hℓ0 : ℓ ≠ 0) :
    quadricSurfaceClassGroupEquiv k (quadricAmbientClassGroupHom k
      ((Proj 𝒮).weilDivisorClassHom hP
        (projectiveHyperplanePrimeDivisor (n := 3) (by norm_num) hℓ hℓ0).toWeilDivisor)) =
      (1, 1) := by
  rw [quadricSurfaceClassGroupEquiv_quadricAmbientClassGroupHom,
    projectiveSpaceClassGroupEquiv_hyperplane, one_smul]

end Hartshorne

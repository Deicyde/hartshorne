/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.BirationalBlowupGenericCoefficient
import Hartshorne.Scheme.CartierDivisorPullback
import Hartshorne.Scheme.SegreProductTrivialization

/-!
# The section algebra inside the function field

Hartshorne, *Algebraic Geometry*, II, proof of Theorem 7.17, Steps 4–5 (pp. 167–168).

Let `i : Z ⟶ ℙʳ_X` be a closed immersion of an integral scheme into projective space over an
integral Noetherian scheme `X`, `f = π ∘ i`, `L = i^* 𝒪(1)`, and let `S` be a section-algebra
model of `f` (Theorem 7.17, Steps 1–3): a quasi-coherent graded `𝒪_X`-algebra with `S₀ = 𝒪_X` and
isomorphisms `E : Γ(f⁻¹(U), L^{md}) ≅ S(U)_m` (`m ≥ 1`) that are natural, linear and
multiplicative (`Hartshorne.BirationalBlowup.SectionModel`). Suppose `f` maps the generic point
of `Z` to that of `X` and that the pullback of rational functions `K(X) → K(Z)` has a left inverse
`θ` (for a birational `f` it is bijective).

Fix a trivializing section `e` of `L` over an open set containing the generic point of `Z`. A
section of `L^{n}` over `f⁻¹(U)` then has a generic coefficient in `K(Z)`
(`Hartshorne.GenericCoefficient.genericCoeff`), which `θ` sends to `K(X)`
(`Hartshorne.BirationalBlowup.coeffK`). Over an affine open `U` containing the generic point
of `X`, sending a homogeneous `s ∈ S(U)_m` to `c(s) Tᵐ`, where `c(s)` is the image of `s` in
`K(X)` (the function itself for `m = 0`, the generic coefficient of `E⁻¹(s)` for `m ≥ 1`), is a
ring homomorphism `S(U) → K(X)[T]` (`Hartshorne.BirationalBlowup.sectionToPoly`), injective in
every degree and compatible with restriction. Thus every graded piece of the section algebra is
identified with a sub-`Γ(U, 𝒪_X)`-module of the function field, and the multiplication of `S`
with the multiplication of `K(X)`. Describing this embedding through generic coefficients with
respect to a trivialization of `L` is this formalization's own device.
-/

universe u

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Polynomial DirectSum

namespace Hartshorne

open SectionAlgebraModel

namespace BirationalBlowup

variable {r : ℕ} {X Z : Scheme.{u}} (i : Z ⟶ projectiveSpaceOverScheme r X)

/-- The projective morphism `f = π ∘ i : Z ⟶ X`. -/
abbrev proj : Z ⟶ X := i ≫ projectiveSpaceOverSchemeProjection r X

/-- **A section-algebra model** of `f = π ∘ i` in degree `d` (Hartshorne II, proof of
Theorem 7.17, Steps 1–3): data for relative Proj together with isomorphisms
`E : Γ(f⁻¹(U), L^{md}) ≅ S(U)_m` for `m ≥ 1` and `U` affine, compatible with restriction,
`Γ(U, 𝒪_X)`-linear and multiplicative, and an isomorphism `Proj_X S ≅ Z` over `X`. -/
structure SectionModel [IsNoetherian X] (d : ℕ) where
  /-- The quasi-coherent graded `𝒪_X`-algebra `S` with condition (†). -/
  data : RelativeProjData X
  /-- The comparison isomorphisms `Γ(f⁻¹(U), L^{md}) ≅ S(U)_m`. -/
  E : ∀ (U : X.AffineZariskiSite) {m : ℕ}, 0 < m →
    Γ(tensorPowerL i (m * d), proj i ⁻¹ᵁ U.1) ≃+ data.algebra.grading U m
  /-- `E` is compatible with restriction. -/
  restrict : ∀ (U V : X.AffineZariskiSite) (h : V ⟶ U) {m : ℕ} (hm : 0 < m)
    (s : Γ(tensorPowerL i (m * d), proj i ⁻¹ᵁ U.1)),
    (E V hm ((tensorPowerL i (m * d)).presheaf.map
        (homOfLE ((proj i).preimage_mono (Scheme.AffineZariskiSite.toOpens_mono h.le))).op s) :
        data.algebra.obj.obj (op V)) = data.algebra.obj.map h.op (E U hm s)
  /-- `E` is `Γ(U, 𝒪_X)`-linear. -/
  smul : ∀ (U : X.AffineZariskiSite) {m : ℕ} (hm : 0 < m) (a : Γ(X, U.1))
    (s : Γ(tensorPowerL i (m * d), proj i ⁻¹ᵁ U.1)),
    (E U hm ((proj i).app U.1 a • s) : data.algebra.obj.obj (op U)) =
      data.algebra.structureMap.app (op U) a * E U hm s
  /-- `E` is multiplicative. -/
  mul : ∀ (U : X.AffineZariskiSite) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (s : Γ(tensorPowerL i (a * d), proj i ⁻¹ᵁ U.1))
    (t : Γ(tensorPowerL i (b * d), proj i ⁻¹ᵁ U.1)),
    (E U (pos_add_of_pos ha b) (Scheme.Modules.Hom.app
        (eqToHom (congrArg (tensorPowerL i) (Nat.add_mul a b d).symm)) _
        (tensorPowerMulSection i s t)) : data.algebra.obj.obj (op U)) =
      (E U ha s : data.algebra.obj.obj (op U)) * E U hb t
  /-- The identification `Proj_X S ≅ Z`. -/
  iso : data.relativeProj ≅ Z
  /-- `Proj_X S ≅ Z` is an isomorphism over `X`. -/
  iso_hom : iso.hom ≫ proj i = data.projection

/-! ### Generic coefficients of sections of `L^{n}` over `f⁻¹(U)` -/

section Coefficient

variable [IsIntegral X] [IsIntegral Z] {i}
  (hf : (proj i).base (genericPoint Z) = genericPoint X)
  {θ : Z.functionField →+* X.functionField}
  (hθ : ∀ g, θ ((proj i).genericFunctionFieldMap hf g) = g)
  {W : Z.Opens} {e : Γ((Scheme.Modules.pullback i).obj (projectiveSpaceTwistingSheaf r X 1), W)}
  (he : IsTrivializingSection _ W e) (hW : genericPoint Z ∈ W)

include hf in
theorem genericPoint_mem_proj_preimage {U : X.Opens} (hU : genericPoint X ∈ U) :
    genericPoint Z ∈ proj i ⁻¹ᵁ U :=
  Scheme.genericPoint_mem_preimage_of_mem (proj i) hf hU

variable (θ) in
/-- The rational function on `X` of a section of `L^{n}` over `f⁻¹(U)`: its generic coefficient
with respect to `e^{⊗ n}`, sent to `K(X)` by `θ`. -/
def coeffK (n : ℕ) {U : X.Opens} (hU : genericPoint X ∈ U)
    (s : Γ(tensorPowerL i n, proj i ⁻¹ᵁ U)) : X.functionField :=
  θ (GenericCoefficient.genericCoeff (he.moduleSheafTensorPower n) hW
    (genericPoint_mem_proj_preimage hf hU) s)

theorem coeffK_add (n : ℕ) {U : X.Opens} (hU : genericPoint X ∈ U)
    (s t : Γ(tensorPowerL i n, proj i ⁻¹ᵁ U)) :
    coeffK hf θ he hW n hU (s + t) = coeffK hf θ he hW n hU s + coeffK hf θ he hW n hU t := by
  rw [coeffK, coeffK, coeffK, GenericCoefficient.genericCoeff_add, map_add]

include hθ in
theorem coeffK_smul (n : ℕ) {U : X.Opens} (hU : genericPoint X ∈ U) (a : Γ(X, U))
    (s : Γ(tensorPowerL i n, proj i ⁻¹ᵁ U)) :
    coeffK hf θ he hW n hU ((proj i).app U a • s) =
      X.presheaf.germ U (genericPoint X) hU a * coeffK hf θ he hW n hU s := by
  rw [coeffK, coeffK, GenericCoefficient.genericCoeff_smul, map_mul,
    ← Scheme.genericFunctionFieldMap_germ (proj i) hf hU, hθ]

theorem coeffK_map (n : ℕ) {U V : X.Opens} (h : V ≤ U) (hV : genericPoint X ∈ V)
    (s : Γ(tensorPowerL i n, proj i ⁻¹ᵁ U)) :
    coeffK hf θ he hW n hV
        ((tensorPowerL i n).presheaf.map (homOfLE ((proj i).preimage_mono h)).op s) =
      coeffK hf θ he hW n (h hV) s := by
  rw [coeffK, coeffK, GenericCoefficient.genericCoeff_map]

theorem coeffK_mul {p q : ℕ} {U : X.Opens} (hU : genericPoint X ∈ U)
    (s : Γ(tensorPowerL i p, proj i ⁻¹ᵁ U)) (t : Γ(tensorPowerL i q, proj i ⁻¹ᵁ U)) :
    coeffK hf θ he hW (p + q) hU (tensorPowerMulSection i s t) =
      coeffK hf θ he hW p hU s * coeffK hf θ he hW q hU t := by
  rw [coeffK, coeffK, coeffK, ← map_mul]
  exact congrArg θ (GenericCoefficient.genericCoeff_mulSection he hW _ s t)

theorem coeffK_eqToHom {p q : ℕ} (h : p = q) {U : X.Opens} (hU : genericPoint X ∈ U)
    (s : Γ(tensorPowerL i p, proj i ⁻¹ᵁ U)) :
    coeffK hf θ he hW q hU
        (Scheme.Modules.Hom.app (eqToHom (congrArg (tensorPowerL i) h)) _ s) =
      coeffK hf θ he hW p hU s := by
  subst h
  rfl

theorem coeffK_injective (n : ℕ) {U : X.Opens} (hU : genericPoint X ∈ U) :
    Function.Injective (coeffK hf θ he hW n hU) := by
  have hL : ((Scheme.Modules.pullback i).obj (projectiveSpaceTwistingSheaf r X 1)).IsInvertible :=
    Scheme.Modules.IsInvertible.pullback _ (isInvertible_projectiveSpaceTwistingSheaf r _ 1)
  exact θ.injective.comp (GenericCoefficient.genericCoeff_injective_of_isInvertible _ hW
    (isInvertible_moduleSheafTensorPower hL n) _)

end Coefficient

/-! ### The section algebra inside `K(X)[T]` -/

section Embedding

variable [IsIntegral X] [IsIntegral Z] [IsNoetherian X] {i}
  (hf : (proj i).base (genericPoint Z) = genericPoint X)
  {θ : Z.functionField →+* X.functionField}
  (hθ : ∀ g, θ ((proj i).genericFunctionFieldMap hf g) = g)
  {W : Z.Opens} {e : Γ((Scheme.Modules.pullback i).obj (projectiveSpaceTwistingSheaf r X 1), W)}
  (he : IsTrivializingSection _ W e) (hW : genericPoint Z ∈ W)
  {d : ℕ} (M : SectionModel i d)

/-- `S(U)₀ = Γ(U, 𝒪_X)`. -/
def degZeroEquiv (U : X.AffineZariskiSite) : Γ(X, U.1) ≃+* M.data.algebra.grading U 0 :=
  RingEquiv.ofBijective (M.data.algebra.toZero U).hom (M.data.degreeZero U)

variable (θ) in
/-- The image `c(s) ∈ K(X)` of a homogeneous element `s ∈ S(U)_m`: the germ of the function `s`
for `m = 0`, and the rational function of the section `E⁻¹(s)` of `L^{md}` for `m ≥ 1`. -/
def pieceCoeff (U : X.AffineZariskiSite) (hU : genericPoint X ∈ U.1) :
    (m : ℕ) → M.data.algebra.grading U m →+ X.functionField
  | 0 => (X.presheaf.germ U.1 (genericPoint X) hU).hom.toAddMonoidHom.comp
      (degZeroEquiv M U).symm.toAddEquiv.toAddMonoidHom
  | m + 1 => (AddMonoidHom.mk' (coeffK hf θ he hW ((m + 1) * d) hU)
      (coeffK_add hf he hW _ hU)).comp (M.E U m.succ_pos).symm.toAddMonoidHom

variable (U : X.AffineZariskiSite) (hU : genericPoint X ∈ U.1)

theorem pieceCoeff_zero (y : M.data.algebra.grading U 0) :
    pieceCoeff hf θ he hW M U hU 0 y =
      X.presheaf.germ U.1 (genericPoint X) hU ((degZeroEquiv M U).symm y) :=
  rfl

theorem pieceCoeff_pos {m : ℕ} (hm : 0 < m) (y : M.data.algebra.grading U m) :
    pieceCoeff hf θ he hW M U hU m y = coeffK hf θ he hW (m * d) hU ((M.E U hm).symm y) := by
  obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rfl

theorem pieceCoeff_congr {m m' : ℕ} (h : m = m') (x : M.data.algebra.obj.obj (op U))
    (hx : x ∈ M.data.algebra.grading U m) (hx' : x ∈ M.data.algebra.grading U m') :
    pieceCoeff hf θ he hW M U hU m ⟨x, hx⟩ = pieceCoeff hf θ he hW M U hU m' ⟨x, hx'⟩ := by
  subst h
  rfl

theorem pieceCoeff_toZero (a : Γ(X, U.1)) :
    pieceCoeff hf θ he hW M U hU 0 (M.data.algebra.toZero U a) =
      X.presheaf.germ U.1 (genericPoint X) hU a := by
  rw [pieceCoeff_zero]
  exact congrArg _ ((degZeroEquiv M U).symm_apply_apply a)

include hθ in
theorem pieceCoeff_structureMap_mul {m : ℕ} (a : Γ(X, U.1)) (y : M.data.algebra.grading U m)
    (h : M.data.algebra.structureMap.app (op U) a * y ∈ M.data.algebra.grading U m) :
    pieceCoeff hf θ he hW M U hU m ⟨M.data.algebra.structureMap.app (op U) a * y, h⟩ =
      X.presheaf.germ U.1 (genericPoint X) hU a * pieceCoeff hf θ he hW M U hU m y := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · obtain ⟨b, rfl⟩ := (M.data.degreeZero U).2 y
    have : (⟨M.data.algebra.structureMap.app (op U) a * (M.data.algebra.toZero U b : _), h⟩ :
        M.data.algebra.grading U 0) = M.data.algebra.toZero U (a * b) :=
      Subtype.ext (map_mul (M.data.algebra.structureMap.app (op U)).hom a b).symm
    rw [this, pieceCoeff_toZero, pieceCoeff_toZero, map_mul]
  · obtain ⟨s, rfl⟩ := (M.E U hm).surjective y
    have : (⟨M.data.algebra.structureMap.app (op U) a * (M.E U hm s : _), h⟩ :
        M.data.algebra.grading U m) = M.E U hm ((proj i).app U.1 a • s) :=
      Subtype.ext (M.smul U hm a s).symm
    rw [this, pieceCoeff_pos hf he hW M U hU hm, pieceCoeff_pos hf he hW M U hU hm,
      AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply, coeffK_smul hf hθ]

include hθ in
theorem pieceCoeff_mul {a b : ℕ} (x : M.data.algebra.grading U a)
    (y : M.data.algebra.grading U b) :
    pieceCoeff hf θ he hW M U hU (a + b) ⟨(x : M.data.algebra.obj.obj (op U)) * y,
        SetLike.mul_mem_graded x.2 y.2⟩ =
      pieceCoeff hf θ he hW M U hU a x * pieceCoeff hf θ he hW M U hU b y := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · obtain ⟨c, rfl⟩ := (M.data.degreeZero U).2 x
    have hxy : M.data.algebra.structureMap.app (op U) c * y ∈ M.data.algebra.grading U b := by
      simpa using SetLike.mul_mem_graded (M.data.algebra.structureMap_mem U c) y.2
    refine (pieceCoeff_congr hf he hW M U hU (zero_add b) _ _ hxy).trans ?_
    rw [pieceCoeff_toZero]
    exact pieceCoeff_structureMap_mul hf hθ he hW M U hU c y hxy
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · obtain ⟨c, rfl⟩ := (M.data.degreeZero U).2 y
    have hxy : M.data.algebra.structureMap.app (op U) c * x ∈ M.data.algebra.grading U a := by
      simpa using SetLike.mul_mem_graded (M.data.algebra.structureMap_mem U c) x.2
    have hxy' : (x : M.data.algebra.obj.obj (op U)) *
        M.data.algebra.structureMap.app (op U) c ∈ M.data.algebra.grading U a := by
      rw [mul_comm]
      exact hxy
    refine (pieceCoeff_congr hf he hW M U hU (add_zero a) _ _ hxy').trans ?_
    rw [pieceCoeff_toZero]
    refine (Eq.trans ?_ (pieceCoeff_structureMap_mul hf hθ he hW M U hU c x hxy)).trans
      (mul_comm _ _)
    exact congrArg _ (Subtype.ext (mul_comm _ _))
  obtain ⟨s, rfl⟩ := (M.E U ha).surjective x
  obtain ⟨t, rfl⟩ := (M.E U hb).surjective y
  have hxy : (⟨((M.E U ha s : M.data.algebra.grading U a) : M.data.algebra.obj.obj (op U)) *
      (M.E U hb t : M.data.algebra.grading U b), SetLike.mul_mem_graded (M.E U ha s).2
        (M.E U hb t).2⟩ : M.data.algebra.grading U (a + b)) =
      M.E U (pos_add_of_pos ha b) (Scheme.Modules.Hom.app
        (eqToHom (congrArg (tensorPowerL i) (Nat.add_mul a b d).symm)) _
        (tensorPowerMulSection i s t)) :=
    Subtype.ext (M.mul U ha hb s t).symm
  rw [hxy, pieceCoeff_pos hf he hW M U hU (pos_add_of_pos ha b), pieceCoeff_pos hf he hW M U hU ha,
    pieceCoeff_pos hf he hW M U hU hb, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply,
    AddEquiv.symm_apply_apply, coeffK_eqToHom hf he hW (Nat.add_mul a b d).symm, coeffK_mul]

theorem pieceCoeff_injective (m : ℕ) : Function.Injective (pieceCoeff hf θ he hW M U hU m) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · intro y y' h
    rw [pieceCoeff_zero, pieceCoeff_zero] at h
    exact (degZeroEquiv M U).symm.injective
      (germ_injective_of_isIntegral X (U := U.1) (genericPoint X) hU h)
  · intro y y' h
    rw [pieceCoeff_pos hf he hW M U hU hm, pieceCoeff_pos hf he hW M U hU hm] at h
    exact (M.E U hm).symm.injective (coeffK_injective hf he hW _ hU h)

theorem pieceCoeff_restrict {V : X.AffineZariskiSite} (g : V ⟶ U) (hV : genericPoint X ∈ V.1)
    {m : ℕ} (y : M.data.algebra.grading U m) :
    pieceCoeff hf θ he hW M V hV m ⟨M.data.algebra.restrict g y, (M.data.algebra.restrict g).map_mem
        y.2⟩ = pieceCoeff hf θ he hW M U hU m y := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · obtain ⟨a, rfl⟩ := (M.data.degreeZero U).2 y
    have h := congr($(M.data.algebra.toZero_comp_restrict g) a)
    have : (⟨M.data.algebra.restrict g (M.data.algebra.toZero U a : _),
        (M.data.algebra.restrict g).map_mem (M.data.algebra.toZero U a).2⟩ :
          M.data.algebra.grading V 0) =
        M.data.algebra.toZero V (X.presheaf.map ((Scheme.AffineZariskiSite.toOpensFunctor X).map
          g).op a) := h
    rw [this, pieceCoeff_toZero, pieceCoeff_toZero]
    exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
  · obtain ⟨s, rfl⟩ := (M.E U hm).surjective y
    have : (⟨M.data.algebra.restrict g (M.E U hm s : _),
        (M.data.algebra.restrict g).map_mem (M.E U hm s).2⟩ : M.data.algebra.grading V m) =
        M.E V hm ((tensorPowerL i (m * d)).presheaf.map
          (homOfLE ((proj i).preimage_mono
            (Scheme.AffineZariskiSite.toOpens_mono g.le))).op s) :=
      Subtype.ext (M.restrict U V g hm s).symm
    rw [this, pieceCoeff_pos hf he hW M V hV hm, pieceCoeff_pos hf he hW M U hU hm,
      AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply,
      coeffK_map hf he hW _ (Scheme.AffineZariskiSite.toOpens_mono g.le)]

variable (θ) in
/-- **The section algebra inside `K(X)[T]`**: the ring homomorphism `S(U) → K(X)[T]` sending a
homogeneous `s ∈ S(U)_m` to `c(s) Tᵐ`, for an affine open `U` containing the generic point. -/
def sectionToPoly : M.data.algebra.obj.obj (op U) →+* X.functionField[X] :=
  (DirectSum.toSemiring (fun m => (monomial m).toAddMonoidHom.comp (pieceCoeff hf θ he hW M U hU m))
      (by
        change monomial 0 (pieceCoeff hf θ he hW M U hU 0 ⟨1, _⟩) = 1
        have : (⟨1, SetLike.GradedOne.one_mem⟩ : M.data.algebra.grading U 0) =
            M.data.algebra.toZero U 1 := Subtype.ext (map_one _).symm
        rw [this, pieceCoeff_toZero, map_one, monomial_zero_one])
      (fun {a b} x y => by
        change monomial (a + b) (pieceCoeff hf θ he hW M U hU (a + b) ⟨(x : _) * y, _⟩) =
          monomial a (pieceCoeff hf θ he hW M U hU a x) *
            monomial b (pieceCoeff hf θ he hW M U hU b y)
        rw [monomial_mul_monomial, pieceCoeff_mul hf hθ])).comp
    (decomposeRingEquiv (M.data.algebra.grading U)).toRingHom

theorem sectionToPoly_of_mem {m : ℕ} {x : M.data.algebra.obj.obj (op U)}
    (hx : x ∈ M.data.algebra.grading U m) :
    sectionToPoly hf θ hθ he hW M U hU x = monomial m (pieceCoeff hf θ he hW M U hU m ⟨x, hx⟩) := by
  simp [sectionToPoly, decomposeRingEquiv, decompose_of_mem _ hx]

theorem sectionToPoly_structureMap (a : Γ(X, U.1)) :
    sectionToPoly hf θ hθ he hW M U hU (M.data.algebra.structureMap.app (op U) a) =
      C (X.presheaf.germ U.1 (genericPoint X) hU a) := by
  rw [sectionToPoly_of_mem hf hθ he hW M U hU (M.data.algebra.structureMap_mem U a),
    monomial_zero_left]
  exact congrArg C (pieceCoeff_toZero hf he hW M U hU a)

theorem coeff_sectionToPoly (x : M.data.algebra.obj.obj (op U)) (m : ℕ) :
    (sectionToPoly hf θ hθ he hW M U hU x).coeff m =
      pieceCoeff hf θ he hW M U hU m (decompose (M.data.algebra.grading U) x m) := by
  classical
  conv_lhs => rw [← sum_support_decompose (M.data.algebra.grading U) x]
  rw [map_sum, finsetSum_coeff]
  simp_rw [sectionToPoly_of_mem hf hθ he hW M U hU (decompose (M.data.algebra.grading U) x _).2,
    coeff_monomial]
  rw [Finset.sum_eq_single m (fun k _ hk => if_neg hk) (fun hm => by
    rw [if_pos rfl, DFinsupp.notMem_support_iff.1 hm, map_zero])]
  simp

theorem sectionToPoly_injective : Function.Injective (sectionToPoly hf θ hθ he hW M U hU) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  apply (decompose (M.data.algebra.grading U)).injective
  ext m : 1
  refine pieceCoeff_injective (θ := θ) hf he hW M U hU m ?_
  rw [← coeff_sectionToPoly hf hθ, hx, coeff_zero, decompose_zero, DirectSum.zero_apply,
    map_zero]

theorem sectionToPoly_restrict {V : X.AffineZariskiSite} (g : V ⟶ U) (hV : genericPoint X ∈ V.1)
    (x : M.data.algebra.obj.obj (op U)) :
    sectionToPoly hf θ hθ he hW M V hV (M.data.algebra.restrict g x) =
      sectionToPoly hf θ hθ he hW M U hU x := by
  have key := SegreProduct.ringHom_ext_of_homogeneous (𝒮 := M.data.algebra.grading U)
    (f := (sectionToPoly hf θ hθ he hW M V hV).comp (M.data.algebra.restrict g).toRingHom)
    (g := sectionToPoly hf θ hθ he hW M U hU) fun m y hy => by
      change sectionToPoly hf θ hθ he hW M V hV (M.data.algebra.restrict g y) = _
      refine (sectionToPoly_of_mem hf hθ he hW M V hV
        ((M.data.algebra.restrict g).map_mem hy)).trans ?_
      rw [sectionToPoly_of_mem hf hθ he hW M U hU hy]
      exact congrArg _ (pieceCoeff_restrict hf he hW M U hU g hV ⟨y, hy⟩)
  exact congr($key x)

end Embedding


end BirationalBlowup

end Hartshorne

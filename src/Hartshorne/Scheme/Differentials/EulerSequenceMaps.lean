/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ProjTwistingSheaf
import Hartshorne.Scheme.TopIsoRestriction
import Hartshorne.Scheme.ProjectiveSpace
import Hartshorne.Scheme.Differentials.RelativeDifferentialsQuasicoherent
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
# The maps of the Euler sequence on projective space

Hartshorne, *Algebraic Geometry*, II.8, Theorem 8.13 (pp. 176–177): the maps of the sequence
`0 → Ω_{X/Y} → 𝒪_X(-1)^{n+1} → 𝒪_X → 0` for `X = ℙ^n_A = Proj A[x_0, …, x_n]` over
`Y = Spec A`.

* The last map `β : 𝒪(-1)^{n+1} ⟶ 𝒪` sends `(s_j)` to `∑ x_j s_j`; its components are
  multiplication by the homogeneous coordinates `x_j : 𝒪(-1) ⟶ 𝒪`.
* The first map `α : Ω ⟶ 𝒪(-1)^{n+1}` sends `d f` to `(∂f/∂x_j)_j`. It is obtained from the
  universal property of `Ω_{X/Y}`: for a local section `f = a / b` of `𝒪_X` (with `a, b`
  homogeneous of the same degree), the quotient rule `∂f/∂x_j = (b ∂a/∂x_j - a ∂b/∂x_j) / b²`
  is a section of `𝒪(-1)`, and `f ↦ ∂f/∂x_j` is a derivation over `A`.
* Euler's identity `∑ x_j ∂f/∂x_j = (deg f) f = 0` for `f` of degree zero gives `α ≫ β = 0`.

On the chart `D₊(x_i)`, `α` sends `d(x_j / x_i)` to `x_i⁻² (x_i e_j - x_j e_i)`, the generator of
the kernel used in Hartshorne's proof; since `α` is a single global morphism, the chartwise maps
agree on overlaps automatically.

The partial derivatives are first extended to localizations of the polynomial ring through the
Kähler differentials (`Hartshorne.EulerSequence.pD`), then to the degree-zero localizations at
the points of `Proj` (`ptD`), and finally to sections (`secD`).
-/

universe u

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

noncomputable section

namespace Hartshorne.EulerSequence

/-! ### Partial derivatives on localizations -/

section Local

variable (A : Type u) [CommRing A] {σ : Type}

/-- The partial derivative `∂/∂x_j` as a linear map out of the Kähler differentials. -/
abbrev pderivLin (j : σ) : Ω[MvPolynomial σ A⁄A] →ₗ[MvPolynomial σ A] MvPolynomial σ A :=
  (MvPolynomial.pderiv j).liftKaehlerDifferential

/-- The partial derivative `∂/∂x_j` extended to a localization of the polynomial ring, by the
quotient rule, with values in the localized module. -/
def pD (j : σ) (x : PrimeSpectrum (MvPolynomial σ A)) :
    Localization.AtPrime x.asIdeal →+ LocalizedModule x.asIdeal.primeCompl (MvPolynomial σ A) :=
  (IsLocalizedModule.map x.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap x.asIdeal.primeCompl _)
    (LocalizedModule.mkLinearMap x.asIdeal.primeCompl _) (pderivLin A j)).toAddMonoidHom.comp
    (SpecKaehler.pointD A x)

theorem pD_mk (j : σ) (x : PrimeSpectrum (MvPolynomial σ A)) (b : MvPolynomial σ A)
    (s : x.asIdeal.primeCompl) :
    pD A j x (Localization.mk b s) =
      LocalizedModule.mk ((s : MvPolynomial σ A) * MvPolynomial.pderiv j b -
        b * MvPolynomial.pderiv j (s : MvPolynomial σ A)) (s * s) := by
  simp only [pD, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, SpecKaehler.pointD_mk,
    IsLocalizedModule.map_LocalizedModules, map_sub, map_smul,
    Derivation.liftKaehlerDifferential_comp_D, smul_eq_mul]

theorem pD_mul (j : σ) (x : PrimeSpectrum (MvPolynomial σ A))
    (y z : Localization.AtPrime x.asIdeal) :
    pD A j x (y * z) = y • pD A j x z + z • pD A j x y := by
  induction y using Localization.induction_on with
  | H y =>
  induction z using Localization.induction_on with
  | H z =>
  obtain ⟨a, s⟩ := y
  obtain ⟨b, t⟩ := z
  rw [Localization.mk_mul, pD_mk, pD_mk, pD_mk, LocalizedModule.mk_smul_mk,
    LocalizedModule.mk_smul_mk, LocalizedModule.mk_add_mk, LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_mul, Derivation.leibniz, smul_eq_mul, one_smul, Submonoid.smul_def]
  ring

/-- `LocalizedModule T B ≃ T⁻¹ B` for a ring `B`. -/
def toLoc {B : Type u} [CommRing B] (T : Submonoid B) : LocalizedModule T B ≃ₗ[B] Localization T :=
  IsLocalizedModule.iso T (Algebra.linearMap B (Localization T))

theorem toLoc_mk {B : Type u} [CommRing B] (T : Submonoid B) (b : B) (t : T) :
    toLoc T (LocalizedModule.mk b t) = Localization.mk b t := by
  rw [← (toLoc T).apply_symm_apply (Localization.mk b t), toLoc,
    IsLocalizedModule.iso_symm_apply' T (Algebra.linearMap B (Localization T)) _ b t]
  rw [Submonoid.smul_def, Localization.smul_mk, Algebra.linearMap_apply,
    ← Localization.mk_one_eq_algebraMap,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp [mul_comm]⟩

theorem toLoc_smul {B : Type u} [CommRing B] (T : Submonoid B) (c : Localization T)
    (w : LocalizedModule T B) : toLoc T (c • w) = c * toLoc T w := by
  induction c using Localization.induction_on with
  | H c =>
  induction w using LocalizedModule.induction_on with
  | h m t =>
  obtain ⟨a, s⟩ := c
  rw [LocalizedModule.mk_smul_mk, toLoc_mk, toLoc_mk, Localization.mk_mul, smul_eq_mul]

theorem toLoc_injective {B : Type u} [CommRing B] (T : Submonoid B) :
    Function.Injective (toLoc T) :=
  (toLoc T).injective

end Local

/-! ### Projective space -/

section Proj

variable (A : Type u) [CommRing A] (n : ℕ)

/-- The standard grading of `S = A[x_0, …, x_n]` by total degree. -/
abbrev grading : ℕ → Submodule A (MvPolynomial (Fin (n + 1)) A) :=
  MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A

attribute [local instance] MvPolynomial.gradedAlgebra

local notation3 "𝒜" => grading A n
local notation3 "S" => MvPolynomial (Fin (n + 1)) A

variable {A n}

/-- The prime ideal of a point of `Proj S`, as a point of `Spec S`. -/
abbrev pt (p : ProjectiveSpectrum 𝒜) : PrimeSpectrum S :=
  ⟨p.asHomogeneousIdeal.toIdeal, p.isPrime⟩

local notation3 "at " p =>
  HomogeneousLocalization.AtPrime (grading A n)
    (HomogeneousIdeal.toIdeal (ProjectiveSpectrum.asHomogeneousIdeal p))

local notation3 "Mt " p =>
  HomogeneousLocalizedModule (grading A n) (gradedTwist (grading A n) (-1))
    (HomogeneousIdeal.toIdeal (ProjectiveSpectrum.asHomogeneousIdeal p)).primeCompl

theorem pderiv_eq_zero_of_mem_zero {a : S} (ha : a ∈ 𝒜 0) (j : Fin (n + 1)) :
    MvPolynomial.pderiv j a = 0 := by
  change a ∈ MvPolynomial.homogeneousSubmodule _ _ 0 at ha
  rw [MvPolynomial.homogeneousSubmodule_zero] at ha
  obtain ⟨r, rfl⟩ := Submodule.mem_one.mp ha
  exact MvPolynomial.pderiv_C

theorem pderiv_mem {k : ℕ} {a : S} (ha : a ∈ 𝒜 k) (j : Fin (n + 1)) :
    MvPolynomial.pderiv j a ∈ 𝒜 (k - 1) :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).2
    (((MvPolynomial.mem_homogeneousSubmodule _ _).1 ha).pderiv)

/-- The numerator `b ∂a - a ∂b` of the quotient rule lies in `S(-1)_{2k}`. -/
theorem quot_mem {k : ℕ} {a b : S} (ha : a ∈ 𝒜 k) (hb : b ∈ 𝒜 k) (j : Fin (n + 1)) :
    b * MvPolynomial.pderiv j a - a * MvPolynomial.pderiv j b ∈
      gradedTwist 𝒜 (-1) ((2 * k : ℕ) : ℤ) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [pderiv_eq_zero_of_mem_zero ha, pderiv_eq_zero_of_mem_zero hb]
    simp only [mul_zero, sub_zero]
    exact zero_mem _
  · refine (mem_gradedTwist_of_eq (k := 2 * k - 1) (by omega)).2 ?_
    have e : 2 * k - 1 = k + (k - 1) := by omega
    rw [e]
    exact sub_mem (SetLike.mul_mem_graded hb (pderiv_mem ha j))
      (SetLike.mul_mem_graded ha (pderiv_mem hb j))

/-- `x_j m ∈ S_k` for `m ∈ S(-1)_k`. -/
theorem X_mul_mem {k : ℕ} {m : S} (hm : m ∈ gradedTwist 𝒜 (-1) (k : ℤ)) (j : Fin (n + 1)) :
    MvPolynomial.X j * m ∈ 𝒜 k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [eq_zero_of_mem_gradedTwist hm (by omega), mul_zero]
    exact zero_mem _
  · have hm' := (mem_gradedTwist_of_eq (k := k - 1) (by omega)).1 hm
    have e : k = 1 + (k - 1) := by omega
    rw [e]
    exact SetLike.mul_mem_graded (MvPolynomial.isHomogeneous_X A j) hm'

/-- The partial derivative `∂/∂x_j : S_(𝔭) → S(-1)_(𝔭)` at a point `𝔭` of `Proj S`. -/
def ptD (j : Fin (n + 1)) (p : ProjectiveSpectrum 𝒜) : (at p) →+ (Mt p) where
  toFun y := ⟨pD A j (pt p) y.val, by
    obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective y
    refine ⟨2 * c.deg, _, _, quot_mem c.num.2 c.den.2 j,
      by rw [two_mul]; exact SetLike.mul_mem_graded c.den.2 c.den.2,
      mul_mem c.den_mem c.den_mem, ?_⟩
    rw [HomogeneousLocalization.val_mk, pD_mk]
    rfl⟩
  map_zero' := by
    ext
    change pD A j (pt p) (0 : at p).val = 0
    rw [HomogeneousLocalization.val_zero, map_zero]
  map_add' y z := by
    ext
    change pD A j (pt p) (y + z).val = pD A j (pt p) y.val + pD A j (pt p) z.val
    rw [HomogeneousLocalization.val_add, map_add]

theorem ptD_val (j : Fin (n + 1)) (p : ProjectiveSpectrum 𝒜) (y : at p) :
    (ptD j p y).val = pD A j (pt p) y.val := rfl

theorem ptD_mul (j : Fin (n + 1)) (p : ProjectiveSpectrum 𝒜) (y z : at p) :
    ptD j p (y * z) = y • ptD j p z + z • ptD j p y := by
  ext
  simp only [ptD_val, HomogeneousLocalization.val_mul, HomogeneousLocalizedModule.val_add,
    HomogeneousLocalizedModule.val_smul]
  exact pD_mul A j (pt p) _ _

theorem exists_rep {p : ProjectiveSpectrum 𝒜} (w : Mt p) :
    ∃ (k : ℕ) (m : S) (s : S) (_ : m ∈ gradedTwist 𝒜 (-1) (k : ℤ)) (_ : s ∈ 𝒜 k)
      (hs : s ∈ (HomogeneousIdeal.toIdeal (ProjectiveSpectrum.asHomogeneousIdeal p)).primeCompl),
      w.val = LocalizedModule.mk m ⟨s, hs⟩ :=
  w.2

/-- Multiplication by `x_j : S(-1)_(𝔭) → S_(𝔭)` at a point `𝔭` of `Proj S`. -/
def ptMulFun (j : Fin (n + 1)) (p : ProjectiveSpectrum 𝒜) (w : Mt p) : at p :=
  HomogeneousLocalization.mk
    ⟨(exists_rep w).choose,
      ⟨_, X_mul_mem (exists_rep w).choose_spec.choose_spec.choose_spec.choose j⟩,
      ⟨_, (exists_rep w).choose_spec.choose_spec.choose_spec.choose_spec.choose⟩,
      (exists_rep w).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose⟩

theorem ptMulFun_val (j : Fin (n + 1)) (p : ProjectiveSpectrum 𝒜) (w : Mt p) :
    (ptMulFun j p w).val = algebraMap S _ (MvPolynomial.X j) * toLoc _ w.val := by
  have h := (exists_rep w).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec
  have h' := congrArg (toLoc _) h
  rw [toLoc_mk] at h'
  rw [h', ptMulFun, HomogeneousLocalization.val_mk, ← Localization.mk_one_eq_algebraMap,
    Localization.mk_mul, one_mul]

/-- Multiplication by `x_j`, as an additive map `S(-1)_(𝔭) → S_(𝔭)`. -/
def ptMul (j : Fin (n + 1)) (p : ProjectiveSpectrum 𝒜) : (Mt p) →+ (at p) where
  toFun := ptMulFun j p
  map_zero' := by
    apply HomogeneousLocalization.val_injective
    rw [ptMulFun_val, HomogeneousLocalizedModule.val_zero, map_zero, mul_zero,
      HomogeneousLocalization.val_zero]
  map_add' w z := by
    apply HomogeneousLocalization.val_injective
    rw [ptMulFun_val, HomogeneousLocalizedModule.val_add, map_add, mul_add,
      HomogeneousLocalization.val_add, ptMulFun_val, ptMulFun_val]

theorem ptMul_val (j : Fin (n + 1)) (p : ProjectiveSpectrum 𝒜) (w : Mt p) :
    (ptMul j p w).val = algebraMap S _ (MvPolynomial.X j) * toLoc _ w.val :=
  ptMulFun_val j p w

theorem ptMul_smul (j : Fin (n + 1)) (p : ProjectiveSpectrum 𝒜) (c : at p) (w : Mt p) :
    ptMul j p (c • w) = c * ptMul j p w := by
  apply HomogeneousLocalization.val_injective
  rw [ptMul_val, HomogeneousLocalizedModule.val_smul, toLoc_smul,
    HomogeneousLocalization.val_mul, ptMul_val]
  ring

theorem toLoc_pD_mk (j : Fin (n + 1)) (p : ProjectiveSpectrum 𝒜) (c : NumDenSameDeg 𝒜
    (HomogeneousIdeal.toIdeal (ProjectiveSpectrum.asHomogeneousIdeal p)).primeCompl) :
    toLoc _ (pD A j (pt p) (HomogeneousLocalization.mk c).val) =
      Localization.mk ((c.den : S) * MvPolynomial.pderiv j (c.num : S) -
        (c.num : S) * MvPolynomial.pderiv j (c.den : S))
        ⟨(c.den : S) * c.den, mul_mem c.den_mem c.den_mem⟩ := by
  rw [HomogeneousLocalization.val_mk, pD_mk, toLoc_mk]
  rfl

/-- **Euler's identity** at a point: `∑_j x_j ∂f/∂x_j = 0` for `f ∈ S_(𝔭)` of degree zero. -/
theorem sum_ptMul_ptD (p : ProjectiveSpectrum 𝒜) (y : at p) :
    ∑ j, ptMul j p (ptD j p y) = 0 := by
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective y
  apply HomogeneousLocalization.val_injective
  have hj : ∀ j, (ptMul j p (ptD j p (HomogeneousLocalization.mk c))).val =
      Localization.mk (MvPolynomial.X j * ((c.den : S) * MvPolynomial.pderiv j (c.num : S) -
        (c.num : S) * MvPolynomial.pderiv j (c.den : S)))
        ⟨(c.den : S) * c.den, mul_mem c.den_mem c.den_mem⟩ := by
    intro j
    rw [ptMul_val, ptD_val, toLoc_pD_mk, ← Localization.mk_one_eq_algebraMap, Localization.mk_mul,
      one_mul]
  rw [← HomogeneousLocalization.algebraMap_apply, map_sum, HomogeneousLocalization.val_zero]
  simp only [HomogeneousLocalization.algebraMap_apply, hj]
  rw [← Localization.mk_sum]
  have hnum := ((MvPolynomial.mem_homogeneousSubmodule _ _).1 c.num.2).sum_X_mul_pderiv
  have hden := ((MvPolynomial.mem_homogeneousSubmodule _ _).1 c.den.2).sum_X_mul_pderiv
  have key : ∑ j, MvPolynomial.X j * ((c.den : S) * MvPolynomial.pderiv j (c.num : S) -
        (c.num : S) * MvPolynomial.pderiv j (c.den : S)) = 0 :=
    calc ∑ j, MvPolynomial.X j * ((c.den : S) * MvPolynomial.pderiv j (c.num : S) -
          (c.num : S) * MvPolynomial.pderiv j (c.den : S))
        = (c.den : S) * ∑ j, MvPolynomial.X j * MvPolynomial.pderiv j (c.num : S) -
          (c.num : S) * ∑ j, MvPolynomial.X j * MvPolynomial.pderiv j (c.den : S) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
      _ = 0 := by
          rw [hnum, hden, nsmul_eq_mul, nsmul_eq_mul]
          ring
  rw [key, Localization.mk_zero]

end Proj

/-! ### The sheaf maps -/

section Sheaf

variable {A : Type u} [CommRing A] {n : ℕ}

attribute [local instance] MvPolynomial.gradedAlgebra

local notation3 "𝒜" => grading A n
local notation3 "S" => MvPolynomial (Fin (n + 1)) A

open TopologicalSpace Opposite ProjGradedModuleSheaf

local notation3 "at " p =>
  HomogeneousLocalization.AtPrime (grading A n)
    (HomogeneousIdeal.toIdeal (ProjectiveSpectrum.asHomogeneousIdeal p))

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

variable (A n) in
/-- The twisting sheaf `𝒪(-1)` on `ℙ^n_A = Proj S`. -/
abbrev O1 : (Proj 𝒜).Modules := projTwistingSheaf 𝒜 (-1)

variable (A n) in
/-- The structure sheaf `𝒪_{ℙ^n}` as a module over itself. -/
abbrev O0 : (Proj 𝒜).Modules := SheafOfModules.unit (Proj 𝒜).ringCatSheaf

/-- The section `∂s/∂x_j` of `𝒪(-1)` for a section `s` of `𝒪_{ℙ^n}`, pointwise. -/
def secD (j : Fin (n + 1)) (U : (Proj 𝒜).Opensᵒᵖ) :
    (Proj 𝒜).presheaf.obj U →+ (O1 A n).val.obj U where
  toFun s := (⟨fun x => ptD j x.1 (s.1 x), fun x => by
    obtain ⟨V, mV, i, k, ⟨r, hr⟩, ⟨g, hg⟩, nin, w⟩ := s.2 x
    refine ⟨V, mV, i, 2 * k, _, quot_mem hr hg j, g * g,
      by rw [two_mul]; exact SetLike.mul_mem_graded hg hg,
      fun y hy => nin y ((y.1.isPrime.mem_or_mem hy).elim id id), fun y => ?_⟩
    have wy := w y
    dsimp only at wy
    ext
    erw [ptD_val, wy, HomogeneousLocalization.val_mk, pD_mk]
    rfl⟩ : (sheafInType 𝒜 (gradedTwist 𝒜 (-1))).1.obj U)
  map_zero' := section_ext (U := U) fun x => map_zero (ptD j x.1)
  map_add' a b := section_ext (U := U) fun x => map_add (ptD j x.1) (a.1 x) (b.1 x)

theorem secD_apply (j : Fin (n + 1)) (U : (Proj 𝒜).Opensᵒᵖ) (s : (Proj 𝒜).presheaf.obj U)
    (x : U.unop) :
    ((secD j U s : (O1 A n).val.obj U) : (sheafInType 𝒜 (gradedTwist 𝒜 (-1))).1.obj U).1 x =
      ptD j x.1 (s.1 x) := rfl

theorem secD_mul (j : Fin (n + 1)) (U : (Proj 𝒜).Opensᵒᵖ)
    (a b : (Proj 𝒜).ringCatSheaf.obj.obj U) :
    secD j U (a * b) = a • secD j U b + b • secD j U a :=
  section_ext (U := U) fun x => ptD_mul j x.1 (a.1 x) (b.1 x)

theorem secD_map (j : Fin (n + 1)) {U V : (Proj 𝒜).Opensᵒᵖ} (i : U ⟶ V)
    (s : (Proj 𝒜).presheaf.obj U) :
    secD j V ((Proj 𝒜).presheaf.map i s) = (O1 A n).val.map i (secD j U s) := rfl

/-- Multiplication by `x_j`, `𝒪(-1) ⟶ 𝒪`, on sections. -/
def secMul (j : Fin (n + 1)) (U : (Proj 𝒜).Opensᵒᵖ) :
    (O1 A n).val.obj U →ₗ[(Proj 𝒜).ringCatSheaf.obj.obj U]
      (SheafOfModules.unit (Proj 𝒜).ringCatSheaf).val.obj U where
  toFun s := (⟨fun x => ptMul j x.1
      ((s : (sheafInType 𝒜 (gradedTwist 𝒜 (-1))).1.obj U).1 x), fun x => by
    obtain ⟨V, mV, i, k, m, hm, g, hg, nin, w⟩ :=
      (s : (sheafInType 𝒜 (gradedTwist 𝒜 (-1))).1.obj U).2 x
    refine ⟨V, mV, i, k, ⟨_, X_mul_mem hm j⟩, ⟨g, hg⟩, nin, fun y => ?_⟩
    apply HomogeneousLocalization.val_injective
    refine (ptMul_val j _ _).trans ?_
    have wy := w y
    dsimp only at wy
    erw [wy, HomogeneousLocalizedModule.val_mk, toLoc_mk,
      HomogeneousLocalization.val_mk, ← Localization.mk_one_eq_algebraMap, Localization.mk_mul,
      one_mul]⟩ : (ProjectiveSpectrum.StructureSheaf.structureSheafInType 𝒜).1.obj U)
  map_add' a b := by
    apply Subtype.ext
    funext x
    exact map_add (ptMul j x.1) _ _
  map_smul' r a := by
    apply Subtype.ext
    funext x
    exact ptMul_smul j x.1 _ _

/-- Multiplication by `x_j`, as a morphism of sheaves of modules `𝒪(-1) ⟶ 𝒪`. -/
def mulX (j : Fin (n + 1)) : O1 A n ⟶ O0 A n where
  val := PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom (secMul j U).toAddMonoidHom
      naturality _ _ _ := rfl }
    (fun U r m => (secMul j U).map_smul r m)

theorem mulX_app (j : Fin (n + 1)) (U : (Proj 𝒜).Opensᵒᵖ) (s : (O1 A n).val.obj U) :
    (mulX j).val.app U s = secMul j U s := rfl

variable (A n) in
/-- The structure morphism `ℙ^n_A ⟶ Spec A`. -/
def toBase : Proj 𝒜 ⟶ Spec (CommRingCat.of A) :=
  Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (algebraMap A (𝒜 0)))

@[deprecated Hartshorne.topIso_inv_appTop_presheaf_map (since := "2026-11-09")]
alias topIso_inv_appTop_presheaf_map := Hartshorne.topIso_inv_appTop_presheaf_map

@[deprecated Hartshorne.topIso_inv_appTop_presheaf_map_map (since := "2026-11-09")]
alias topIso_inv_appTop_presheaf_map_map := Hartshorne.topIso_inv_appTop_presheaf_map_map

/-- The global functions coming from `A` are the constants. -/
theorem toBase_appTop_val (a : A) (x : Proj 𝒜) :
    (((toBase A n).appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)).1
      ⟨x, trivial⟩).val = algebraMap S _ (MvPolynomial.C a) := by
  rw [toBase, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  erw [← CommRingCat.comp_apply (Scheme.ΓSpecIso _).inv, ← Scheme.ΓSpecIso_inv_naturality]
  simp only [Proj.toSpecZero, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  erw [← CommRingCat.comp_apply (Scheme.ΓSpecIso _).inv
    (Scheme.Hom.appTop (Spec.map _)), ← Scheme.ΓSpecIso_inv_naturality]
  rw [show Scheme.Hom.appTop (Proj.basicOpenToSpec 𝒜 1) = _ from Proj.basicOpenToSpec_app_top _ 1]
  simp only [CommRingCat.comp_apply]
  simp only [Scheme.isoOfEq_inv, Scheme.homOfLE_appTop, Scheme.Opens.topIso_inv]
  have h1 : (⊤ : (Proj 𝒜).Opens) ≤ Proj.basicOpen 𝒜 1 := by rw [Proj.basicOpen_one]
  erw [Hartshorne.topIso_inv_appTop_presheaf_map_map h1]
  rw [CommRingCat.comp_apply, Iso.inv_hom_id_apply]
  change ((((Proj.awayToSection 𝒜 1).hom' _).1 ⟨x, h1 trivial⟩)).val = _
  change (HomogeneousLocalization.mk ⟨0, algebraMap A (𝒜 0) a, 1, one_mem _⟩).val = _
  rw [HomogeneousLocalization.val_mk, SetLike.GradeZero.coe_algebraMap,
    MvPolynomial.algebraMap_eq, ← Localization.mk_one_eq_algebraMap]
  rfl

theorem ptD_const (j : Fin (n + 1)) (x : ProjectiveSpectrum 𝒜) (y : at x) (a : A)
    (hy : y.val = algebraMap S _ (MvPolynomial.C a)) : ptD j x y = 0 := by
  ext
  rw [ptD_val, hy, ← Localization.mk_one_eq_algebraMap, pD_mk]
  simp only [MvPolynomial.pderiv_C, OneMemClass.coe_one, MvPolynomial.pderiv_one, mul_zero,
    sub_zero]
  exact LocalizedModule.zero_mk _

theorem ptD_eq_zero_of_mul (j : Fin (n + 1)) (x : ProjectiveSpectrum 𝒜) (w u v : at x)
    (hu : IsUnit u) (hu0 : ptD j x u = 0) (hv0 : ptD j x v = 0) (h : w * u = v) :
    ptD j x w = 0 := by
  have e := ptD_mul j x w u
  rw [h, hv0, hu0, smul_zero, zero_add] at e
  exact hu.smul_eq_zero.1 e.symm

/-- Evaluation of a section of `𝒪_{ℙ^n}` at a point, as a ring homomorphism. -/
def evalHom {U : (Proj 𝒜).Opensᵒᵖ} (p : ProjectiveSpectrum 𝒜) (hp : p ∈ U.unop) :
    (Proj 𝒜).presheaf.obj U →+* at p where
  toFun s := s.1 ⟨p, hp⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem secD_kills (j : Fin (n + 1)) (V : (Spec (CommRingCat.of A)).Opens)
    (t : Γ(Spec (CommRingCat.of A), V)) :
    secD j (op (toBase A n ⁻¹ᵁ V)) ((toBase A n).app V t) = 0 := by
  refine section_ext (U := op (toBase A n ⁻¹ᵁ V)) fun x => ?_
  change ptD j x.1 (((toBase A n).app V t).1 x) = 0
  obtain ⟨g, hxg, i, a, hc⟩ := StructureSheaf.exists_const _ t ((toBase A n).base x.1) x.2
  let W : (Spec (CommRingCat.of A)).Opens := PrimeSpectrum.basicOpen g
  have hxW : x.1 ∈ toBase A n ⁻¹ᵁ W := hxg
  have key := congrArg ((toBase A n).app W) (SpecKaehler.const_mul_globalRes (B := A) a g)
  rw [map_mul] at key
  have key' := congrArg (evalHom (U := op (toBase A n ⁻¹ᵁ W)) x.1 hxW) key
  rw [map_mul] at key'
  have hres : ∀ c : A, evalHom (U := op (toBase A n ⁻¹ᵁ W)) x.1 hxW
      ((toBase A n).app W (SpecKaehler.globalRes W c)) =
        ((toBase A n).appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv c)).1 ⟨x.1, trivial⟩ := by
    intro c
    have := ConcreteCategory.congr_hom ((toBase A n).naturality W.leTop.op)
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv c)
    exact congrArg (evalHom (U := op (toBase A n ⁻¹ᵁ W)) x.1 hxW) this
  have ht : evalHom (U := op (toBase A n ⁻¹ᵁ W)) x.1 hxW
      ((toBase A n).app W (SpecKaehler.constSec a g)) = ((toBase A n).app V t).1 x := by
    have := ConcreteCategory.congr_hom ((toBase A n).naturality (homOfLE i).op) t
    rw [show SpecKaehler.constSec a g = (Spec (CommRingCat.of A)).presheaf.map (homOfLE i).op t
      from hc]
    exact congrArg (evalHom (U := op (toBase A n ⁻¹ᵁ W)) x.1 hxW) this
  rw [hres, hres, ht] at key'
  have hunit : IsUnit (((toBase A n).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv g)).1 ⟨x.1, trivial⟩) := by
    rw [← hres]
    have hu : IsUnit (SpecKaehler.globalRes (B := A) W g) := by
      refine IsUnit.of_mul_eq_one (SpecKaehler.constSec 1 g) ?_
      rw [mul_comm, SpecKaehler.const_mul_globalRes]
      change (Spec (CommRingCat.of A)).presheaf.map _ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv 1) = 1
      rw [map_one, map_one]
    exact (hu.map ((toBase A n).app W).hom).map _
  exact ptD_eq_zero_of_mul j x.1 _ _ _ hunit (ptD_const j x.1 _ g (toBase_appTop_val g x.1))
    (ptD_const j x.1 _ a (toBase_appTop_val a x.1)) key'

/-- The relative derivation `∂/∂x_j : 𝒪_{ℙ^n} ⟶ 𝒪(-1)`. -/
def derivD (j : Fin (n + 1)) :
    (O1 A n).val.Derivation' (Scheme.inverseImageStructureSheafMap (toBase A n)).hom :=
  RelDiffLocal.derivationOfKills (toBase A n) (fun {U} => secD j U)
    (fun {U} a b => secD_mul j U a b) (fun i s => secD_map j i s)
    (fun U m h => RelDiffLocal.modules_sep (O1 A n) U m h) (secD_kills j)

theorem derivD_d (j : Fin (n + 1)) (U : (Proj 𝒜).Opensᵒᵖ) (a : (Proj 𝒜).presheaf.obj U) :
    (derivD j).d a = secD j U a := rfl

variable (A n) in
/-- The sheaf of relative differentials `Ω_{ℙ^n_A / A}`. -/
abbrev Ω : (Proj 𝒜).Modules := Scheme.relativeDifferentials (toBase A n)

/-- The component `Ω ⟶ 𝒪(-1)` induced by `∂/∂x_j`. -/
def alphaj (j : Fin (n + 1)) : Ω A n ⟶ O1 A n :=
  (Scheme.relativeDifferentialsHomEquiv (toBase A n) (O1 A n)).symm (derivD j)

theorem alphaj_d (j : Fin (n + 1)) (U : (Proj 𝒜).Opensᵒᵖ) (a : (Proj 𝒜).presheaf.obj U) :
    (alphaj j).val.app U ((Scheme.relativeDifferentialsDerivation (toBase A n)).d a) =
      secD j U a := by
  have h := (Scheme.relativeDifferentialsHomEquiv (toBase A n) (O1 A n)).apply_symm_apply
    (derivD j)
  rw [Scheme.relativeDifferentialsHomEquiv_apply] at h
  exact PresheafOfModules.Derivation.congr_d h a

variable (A n) in
/-- `𝒪(-1)^{n+1}`. -/
abbrev E : (Proj 𝒜).Modules := ⨁ fun _ : Fin (n + 1) => O1 A n

variable (A n) in
/-- The map `Ω ⟶ 𝒪(-1)^{n+1}`, `d f ↦ (∂f/∂x_j)_j`. -/
def alpha : Ω A n ⟶ E A n := Limits.biproduct.lift alphaj

variable (A n) in
/-- The map `𝒪(-1)^{n+1} ⟶ 𝒪` given by the homogeneous coordinates, `(s_j) ↦ ∑ x_j s_j`. -/
def beta : E A n ⟶ O0 A n := Limits.biproduct.desc mulX

theorem sum_val_app {X : Scheme.{u}} {M N : X.Modules} {ι : Type*} (s : Finset ι)
    (f : ι → (M ⟶ N)) (U : X.Opensᵒᵖ) (x : M.val.obj U) :
    (∑ i ∈ s, f i).val.app U x = ∑ i ∈ s, (f i).val.app U x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
    rfl

theorem O0_sum_apply {ι : Type*} (s : Finset ι) {U : (Proj 𝒜).Opensᵒᵖ}
    (f : ι → (O0 A n).val.obj U) (x : U.unop) :
    ((∑ i ∈ s, f i : (O0 A n).val.obj U) : (Proj 𝒜).presheaf.obj U).1 x =
      ∑ i ∈ s, ((f i : (O0 A n).val.obj U) : (Proj 𝒜).presheaf.obj U).1 x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
    rfl

omit [CommRing A] in
/-- Morphisms out of the relative differentials agree if they agree on all `d a`. -/
theorem relDiff_hom_ext {X Y : Scheme.{u}} (f : X ⟶ Y) {M : X.Modules}
    (g₁ g₂ : Scheme.relativeDifferentials f ⟶ M)
    (h : ∀ (U : X.Opensᵒᵖ) (a : X.presheaf.obj U),
      g₁.val.app U ((Scheme.relativeDifferentialsDerivation f).d a) =
        g₂.val.app U ((Scheme.relativeDifferentialsDerivation f).d a)) : g₁ = g₂ := by
  apply (Scheme.relativeDifferentialsHomEquiv f M).injective
  refine (Scheme.relativeDifferentialsHomEquiv_apply _ _ _).trans
    (Eq.trans ?_ (Scheme.relativeDifferentialsHomEquiv_apply _ _ _).symm)
  ext U a
  exact h U a

theorem alphaj_mulX_d (j : Fin (n + 1)) (U : (Proj 𝒜).Opensᵒᵖ) (a : (Proj 𝒜).presheaf.obj U) :
    (alphaj j ≫ mulX j).val.app U ((Scheme.relativeDifferentialsDerivation (toBase A n)).d a) =
      secMul j U (secD j U a) :=
  congrArg (secMul j U) (alphaj_d j U a)

theorem O0_ext {U : (Proj 𝒜).Opensᵒᵖ} (s t : (O0 A n).val.obj U)
    (h : ∀ x, (s : (Proj 𝒜).presheaf.obj U).1 x = (t : (Proj 𝒜).presheaf.obj U).1 x) : s = t :=
  Subtype.ext (funext h)

theorem sum_secMul_secD (U : (Proj 𝒜).Opensᵒᵖ) (a : (Proj 𝒜).presheaf.obj U) :
    ∑ j, secMul j U (secD j U a) = 0 :=
  O0_ext _ _ fun x => (O0_sum_apply _ _ x).trans (sum_ptMul_ptD x.1 (a.1 x))

/-- **The composite `Ω ⟶ 𝒪(-1)^{n+1} ⟶ 𝒪` vanishes** (Euler's identity). -/
theorem alpha_beta : alpha A n ≫ beta A n = 0 := by
  refine relDiff_hom_ext _ _ _ fun U a => ?_
  rw [alpha, beta, Limits.biproduct.lift_desc, sum_val_app,
    Finset.sum_congr rfl fun j _ => alphaj_mulX_d j U a]
  exact sum_secMul_secD U a

end Sheaf

end Hartshorne.EulerSequence

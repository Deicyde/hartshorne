/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Nonsingular.AmbientCotangent
import Hartshorne.Affine.AlgebraicSet
import Hartshorne.Projective.Basic
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Local intersection multiplicity of affine plane curves

Hartshorne, *Algebraic Geometry*, Exercise I.5.4(a), (b) (p. 36), with the multiplicity of a
point on a plane curve from Exercise I.5.3.

For polynomials `f, g` and a point `P` of affine space, `(f · g)_P` is the length of
`𝒪_P ⧸ (f, g)` as an `𝒪_P`-module, where `𝒪_P` is the localization of the polynomial ring at
the maximal ideal of `P` (the local ring of affine space at `P`, Theorem I.3.2(c)).  The
multiplicity `mult_P(f)` is the lowest degree of a monomial of `f(x + P)`.

## Method

* Lengths over `𝒪_P` equal dimensions over `k`, because the residue field of `𝒪_P` is `k`
  (`IsLocalRing.length_restrictScalars`).  This makes lengths invariant under `k`-algebra
  automorphisms of the polynomial ring moving one point to another (translations, renamings,
  affine changes of coordinates).
* If `J ⊇ m_P^N`, then `R ⧸ J → 𝒪_P ⧸ J 𝒪_P` is bijective, and for monomial ideals the
  dimension of `R ⧸ J` counts the monomials outside `J`.
* **Finiteness.**  A prime of `k[x, y]` containing two non-associated irreducible polynomials
  has height two, hence is maximal; so `𝒪_P ⧸ (f, g)` is Artinian.
* **Lower bound.**  Fulton's count: if `f ∈ m^a` and `g ∈ m^b`, the map
  `(A, B) ↦ Af + Bg` from `R/m^b × R/m^a` to `R/m^(a+b)` shows
  `dim R/((f, g) + m^(a+b)) ≥ (a+b)(a+b+1)/2 - a(a+1)/2 - b(b+1)/2 = ab`.
* **Lines.**  An affine change of coordinates moves a line through `P` to the axis `x₀ = 0`
  through the origin, where `(f, x₀) = (x₀, x₁^e · unit)` in `𝒪_0`.  So `(L · f)_P` is the order
  of vanishing of `f` restricted to `L`, which equals `mult_P(f)` unless the direction of `L`
  is a zero of the leading form of `f` at `P`.

## Main definitions and results

* `Hartshorne.affineLocalIntersectionMultiplicity`: the local intersection multiplicity.
* `Hartshorne.planeCurveMultiplicity`: the multiplicity of a point on a plane curve.
* `Hartshorne.affineLocalIntersectionMultiplicity_ne_top_and_ge`: Exercise 5.4(a).
* `Hartshorne.affineLocalIntersectionMultiplicity_planeLineEquation`: intersection with a line.
* `Hartshorne.finite_lines_affineLocalIntersectionMultiplicity_ne`: Exercise 5.4(b).
-/

namespace Hartshorne
open MvPolynomial

noncomputable section
universe u
variable {k : Type u} [Field k] {σ : Type*}

omit [Field k] in
theorem mem_affinePointIdeal_iff {k : Type*} [Field k] {p : σ → k} {f : MvPolynomial σ k} :
    f ∈ affinePointIdeal p ↔ eval p f = 0 := by
  rw [affinePointIdeal, RingHom.mem_ker]
  rfl

instance affinePointIdeal_isMaximal (p : σ → k) : (affinePointIdeal p).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ fun a => ⟨C a, by simp⟩

abbrev affineLocalRing (p : σ → k) : Type _ :=
  Localization.AtPrime (affinePointIdeal p)

def affineLocalIntersectionMultiplicity (f g : MvPolynomial σ k) (p : σ → k) : ℕ∞ :=
  Module.length (affineLocalRing p)
    (affineLocalRing p ⧸ Ideal.span
      {algebraMap (MvPolynomial σ k) (affineLocalRing p) f,
        algebraMap (MvPolynomial σ k) (affineLocalRing p) g})

instance affineLocalRing_isLocalHom (p : σ → k) :
    IsLocalHom (algebraMap k (affineLocalRing p)) where
  map_nonunit a ha := by
    by_cases h0 : a = 0
    · subst h0
      simp at ha
    · exact (Units.mk0 a h0).isUnit

theorem algebraMap_residueField_surjective (p : σ → k) :
    Function.Surjective (algebraMap k (IsLocalRing.ResidueField (affineLocalRing p))) := by
  intro x
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (affinePointIdeal p).primeCompl y
  have hs : eval p (s : MvPolynomial σ k) ≠ 0 := s.2
  refine ⟨eval p a / eval p (s : MvPolynomial σ k), ?_⟩
  have key : ∀ b : MvPolynomial σ k,
      algebraMap (MvPolynomial σ k) (affineLocalRing p) b -
        algebraMap k (affineLocalRing p) (eval p b) ∈
        IsLocalRing.maximalIdeal (affineLocalRing p) := by
    intro b
    rw [← Localization.AtPrime.map_eq_maximalIdeal, IsScalarTower.algebraMap_apply k
      (MvPolynomial σ k), ← map_sub]
    apply Ideal.mem_map_of_mem
    rw [mem_affinePointIdeal_iff]
    simp
  have hr : ∀ b : MvPolynomial σ k,
      IsLocalRing.residue (affineLocalRing p) (algebraMap _ _ b) =
        algebraMap k (IsLocalRing.ResidueField (affineLocalRing p)) (eval p b) := by
    intro b
    rw [IsScalarTower.algebraMap_apply k (affineLocalRing p)]
    exact sub_eq_zero.1 (by
      rw [IsLocalRing.ResidueField.algebraMap_eq, ← map_sub,
        IsLocalRing.residue_eq_zero_iff]
      exact key b)
  have hmul := congrArg (IsLocalRing.residue (affineLocalRing p))
    (IsLocalization.mk'_spec (affineLocalRing p) a s)
  rw [map_mul, hr, hr] at hmul
  have hne : algebraMap k (IsLocalRing.ResidueField (affineLocalRing p))
      (eval p (s : MvPolynomial σ k)) ≠ 0 := by
    rw [map_ne_zero]; exact hs
  rw [map_div₀]
  show _ = IsLocalRing.residue _ (IsLocalization.mk' (affineLocalRing p) a s)
  rw [← hmul, mul_div_assoc, div_self hne, mul_one]


theorem length_eq_length_field (p : σ → k) (M : Type*) [AddCommGroup M]
    [Module (affineLocalRing p) M] [Module k M] [IsScalarTower k (affineLocalRing p) M] :
    Module.length (affineLocalRing p) M = Module.length k M := by
  rw [IsLocalRing.length_restrictScalars k (affineLocalRing p) M]
  have h1 : Module.length (IsLocalRing.ResidueField k)
      (IsLocalRing.ResidueField (affineLocalRing p)) = 1 := by
    rw [Module.length_eq_of_surjective (R := IsLocalRing.ResidueField (affineLocalRing p))]
    · exact Module.length_eq_one _ _
    · intro x
      obtain ⟨a, rfl⟩ := algebraMap_residueField_surjective p x
      exact ⟨IsLocalRing.residue k a, rfl⟩
  rw [h1, mul_one]


theorem affineLocalIntersectionMultiplicity_eq_length_field (f g : MvPolynomial σ k)
    (p : σ → k) :
    affineLocalIntersectionMultiplicity f g p =
      Module.length k (affineLocalRing p ⧸ Ideal.span
        {algebraMap (MvPolynomial σ k) (affineLocalRing p) f,
          algebraMap (MvPolynomial σ k) (affineLocalRing p) g}) :=
  length_eq_length_field p _

theorem affineLocalIntersectionMultiplicity_algEquiv {τ : Type*}
    (e : MvPolynomial σ k ≃ₐ[k] MvPolynomial τ k) (p : σ → k) (q : τ → k)
    (he : ∀ f, eval q (e f) = eval p f) (f g : MvPolynomial σ k) :
    affineLocalIntersectionMultiplicity (e f) (e g) q =
      affineLocalIntersectionMultiplicity f g p := by
  rw [affineLocalIntersectionMultiplicity_eq_length_field,
    affineLocalIntersectionMultiplicity_eq_length_field]
  have H : Submonoid.map e (affinePointIdeal p).primeCompl = (affinePointIdeal q).primeCompl := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [mem_affinePointIdeal_iff, Ideal.primeCompl, he] using hy
    · intro hx
      refine ⟨e.symm x, ?_, by simp⟩
      have := he (e.symm x)
      simp only [AlgEquiv.apply_symm_apply] at this
      simpa [mem_affinePointIdeal_iff, Ideal.primeCompl, ← this] using hx
  let eL : affineLocalRing p ≃ₐ[k] affineLocalRing q :=
    IsLocalization.algEquivOfAlgEquiv _ _ e H
  let eQ := Ideal.quotientEquivAlg (R₁ := k) (Ideal.span
        {algebraMap (MvPolynomial σ k) (affineLocalRing p) f,
          algebraMap (MvPolynomial σ k) (affineLocalRing p) g})
      (Ideal.span
        {algebraMap (MvPolynomial τ k) (affineLocalRing q) (e f),
          algebraMap (MvPolynomial τ k) (affineLocalRing q) (e g)}) eL (by
        rw [Ideal.map_span, Set.image_pair]
        simp only [RingHom.coe_coe]
        rw [IsLocalization.algEquivOfAlgEquiv_eq, IsLocalization.algEquivOfAlgEquiv_eq])
  exact eQ.toLinearEquiv.length_eq.symm


theorem isUnit_quotient_mk_of_pow_le {p : σ → k} {J : Ideal (MvPolynomial σ k)} {N : ℕ}
    (hJ : affinePointIdeal p ^ N ≤ J) {s : MvPolynomial σ k} (hs : eval p s ≠ 0) :
    IsUnit (Ideal.Quotient.mk J s) := by
  have hn : s - C (eval p s) ∈ affinePointIdeal p := by
    simp [mem_affinePointIdeal_iff]
  have hnil : IsNilpotent (Ideal.Quotient.mk J (s - C (eval p s))) :=
    ⟨N, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact hJ (Ideal.pow_mem_pow hn N)⟩
  have hu : IsUnit (Ideal.Quotient.mk J (C (eval p s))) := by
    have : IsUnit (C (eval p s) : MvPolynomial σ k) := (Ne.isUnit hs).map C
    exact this.map _
  have := hnil.isUnit_add_left_of_commute hu (Commute.all _ _)
  rwa [← map_add, add_sub_cancel] at this

/-- The comparison map from `R ⧸ J` to `O_p ⧸ J O_p`. -/
abbrev quotientToLocalQuotient (p : σ → k) (J : Ideal (MvPolynomial σ k)) :
    (MvPolynomial σ k ⧸ J) →ₐ[k] (affineLocalRing p ⧸ J.map
      (algebraMap (MvPolynomial σ k) (affineLocalRing p))) :=
  Ideal.quotientMapₐ _ (IsScalarTower.toAlgHom k (MvPolynomial σ k) (affineLocalRing p))
    Ideal.le_comap_map

theorem quotientToLocalQuotient_bijective {p : σ → k} {J : Ideal (MvPolynomial σ k)} {N : ℕ}
    (hJ : affinePointIdeal p ^ N ≤ J) :
    Function.Bijective (quotientToLocalQuotient p J) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hx' : algebraMap (MvPolynomial σ k) (affineLocalRing p) r ∈
        J.map (algebraMap (MvPolynomial σ k) (affineLocalRing p)) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]; exact hx
    obtain ⟨⟨j, s⟩, hjs⟩ := (IsLocalization.mem_map_algebraMap_iff
      (affinePointIdeal p).primeCompl (affineLocalRing p)).1 hx'
    rw [← map_mul, IsLocalization.eq_iff_exists (affinePointIdeal p).primeCompl] at hjs
    obtain ⟨c, hc⟩ := hjs
    have hcs : eval p ((c : MvPolynomial σ k) * s) ≠ 0 := by
      rw [map_mul]; exact mul_ne_zero c.2 s.2
    have hmem : ((c : MvPolynomial σ k) * s) * r ∈ J := by
      have : (c : MvPolynomial σ k) * (r * s) = c * j := hc
      rw [show ((c : MvPolynomial σ k) * s) * r = c * (r * s) by ring, this]
      exact J.mul_mem_left _ j.2
    have hu := isUnit_quotient_mk_of_pow_le hJ hcs
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul] at hmem
    exact (hu.mul_right_eq_zero).1 hmem
  · intro y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (affinePointIdeal p).primeCompl y
    obtain ⟨u, hu⟩ := (isUnit_quotient_mk_of_pow_le hJ s.2).exists_right_inv
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective u
    refine ⟨Ideal.Quotient.mk J (a * u), ?_⟩
    change Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ (IsLocalization.mk' (affineLocalRing p) a s)
    rw [Ideal.Quotient.eq]
    have hsu : (s : MvPolynomial σ k) * u - 1 ∈ J := by
      rw [← Ideal.Quotient.eq, map_mul, map_one, hu]
    have h1 : algebraMap (MvPolynomial σ k) (affineLocalRing p) (s : MvPolynomial σ k) *
        IsLocalization.mk' (affineLocalRing p) (1 : MvPolynomial σ k) s = 1 := by
      rw [IsLocalization.mul_mk'_eq_mk'_of_mul, mul_one, IsLocalization.mk'_self']
    have h2 : IsLocalization.mk' (affineLocalRing p) a s =
        algebraMap _ _ a * IsLocalization.mk' (affineLocalRing p) (1 : MvPolynomial σ k) s := by
      rw [IsLocalization.mul_mk'_eq_mk'_of_mul, mul_one]
    have : algebraMap (MvPolynomial σ k) (affineLocalRing p) (a * u) -
        IsLocalization.mk' (affineLocalRing p) a s =
        algebraMap _ _ (a * ((s : MvPolynomial σ k) * u - 1)) *
          IsLocalization.mk' (affineLocalRing p) (1 : MvPolynomial σ k) s := by
      simp only [map_mul, map_sub, map_one, h2]
      linear_combination -(algebraMap (MvPolynomial σ k) (affineLocalRing p) a *
        algebraMap (MvPolynomial σ k) (affineLocalRing p) u) * h1
    show algebraMap (MvPolynomial σ k) (affineLocalRing p) (a * u) - _ ∈ _
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (J.mul_mem_left _ hsu))

theorem length_localQuotient_eq {p : σ → k} {J : Ideal (MvPolynomial σ k)} {N : ℕ}
    (hJ : affinePointIdeal p ^ N ≤ J) :
    Module.length (affineLocalRing p) (affineLocalRing p ⧸ J.map
      (algebraMap (MvPolynomial σ k) (affineLocalRing p))) =
      Module.length k (MvPolynomial σ k ⧸ J) := by
  rw [length_eq_length_field]
  exact (LinearEquiv.ofBijective (quotientToLocalQuotient p J).toLinearMap
    (quotientToLocalQuotient_bijective hJ)).length_eq.symm


/-- The length of a quotient of a polynomial ring by a monomial ideal is the number of
monomials outside it. -/
theorem length_quotient_of_restrictScalars_eq {I : Ideal (MvPolynomial σ k)}
    {U : Set (σ →₀ ℕ)} (hI : I.restrictScalars k = MvPolynomial.restrictSupport k U) :
    Module.length k (MvPolynomial σ k ⧸ I) = (Cardinal.mk (Uᶜ : Set (σ →₀ ℕ))).toENat := by
  have hc : IsCompl (MvPolynomial.restrictSupport k U)
      (MvPolynomial.restrictSupport k (Uᶜ : Set (σ →₀ ℕ))) := by
    constructor
    · rw [Submodule.disjoint_def]
      intro x hx hx'
      rw [MvPolynomial.mem_restrictSupport_iff] at hx hx'
      ext m
      by_contra hm
      have hm' : m ∈ x.support := by simpa using hm
      exact hx' hm' (hx hm')
    · rw [codisjoint_iff, MvPolynomial.restrictSupport_eq_span,
        MvPolynomial.restrictSupport_eq_span, ← Submodule.span_union, ← Set.image_union,
        Set.union_compl_self, ← MvPolynomial.restrictSupport_eq_span,
        MvPolynomial.restrictSupport_univ]
  have e1 : (MvPolynomial σ k ⧸ I) ≃ₗ[k]
      (MvPolynomial σ k ⧸ MvPolynomial.restrictSupport k U) :=
    (Submodule.Quotient.restrictScalarsEquiv k I).symm.trans
      (Submodule.quotEquivOfEq _ _ hI)
  rw [e1.length_eq, (Submodule.quotientEquivOfIsCompl _ _ hc).length_eq,
    Module.length_eq_rank, ← Cardinal.toENat_lift.{max u _},
    ← (MvPolynomial.basisRestrictSupport k _).mk_eq_rank, Cardinal.toENat_lift]


theorem ncard_degree_eq_fin_two (d : ℕ) :
    {x : Fin 2 →₀ ℕ | x.degree = d}.ncard = d + 1 := by
  rw [← Nat.card_coe_set_eq]
  change Nat.card {x : Fin 2 →₀ ℕ // x.degree = d} = _
  calc
    Nat.card {x : Fin 2 →₀ ℕ // x.degree = d} = Nat.card (Sym (Fin 2) d) :=
      Nat.card_congr (Sym.equivNatSum (Fin 2) d).symm
    _ = Fintype.card (Sym (Fin 2) d) := Nat.card_eq_fintype_card
    _ = (2 + d - 1).choose d := by simpa using Sym.card_sym_eq_choose (α := Fin 2) d
    _ = d + 1 := by
      rw [show 2 + d - 1 = d + 1 by omega, Nat.choose_succ_self_right]

theorem finite_degree_eq_fin_two (d : ℕ) : {x : Fin 2 →₀ ℕ | x.degree = d}.Finite :=
  Set.finite_of_ncard_pos (by rw [ncard_degree_eq_fin_two]; omega)

theorem finite_degree_lt_fin_two (N : ℕ) : {x : Fin 2 →₀ ℕ | x.degree < N}.Finite := by
  have : {x : Fin 2 →₀ ℕ | x.degree < N} = ⋃ d ∈ Finset.range N, {x | x.degree = d} := by
    ext x; simp
  rw [this]
  exact Set.Finite.biUnion (Finset.finite_toSet _) fun d _ => finite_degree_eq_fin_two d

theorem two_mul_ncard_degree_lt_fin_two (N : ℕ) :
    2 * {x : Fin 2 →₀ ℕ | x.degree < N}.ncard = N * (N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hU : {x : Fin 2 →₀ ℕ | x.degree < N + 1} =
        {x | x.degree < N} ∪ {x | x.degree = N} := by
      ext x; simp only [Set.mem_ofPred_eq, Set.mem_union]; omega
    rw [hU, Set.ncard_union_eq _ (finite_degree_lt_fin_two N) (finite_degree_eq_fin_two N),
      mul_add, ih, ncard_degree_eq_fin_two]
    · ring
    · rw [Set.disjoint_left]
      intro x hx hx'
      simp only [Set.mem_ofPred_eq] at hx hx'
      omega

theorem line_monomials_eq_image (e : ℕ) :
    {x : Fin 2 →₀ ℕ | x 0 = 0 ∧ x 1 < e} =
      (fun j : ℕ => Finsupp.single (1 : Fin 2) j) '' (Finset.range e : Set ℕ) := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_image, Finset.coe_range, Set.mem_Iio]
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨x 1, h1, ?_⟩
    ext i
    fin_cases i <;> simp [h0]
  · rintro ⟨j, hj, rfl⟩
    simp [hj]

theorem ncard_line_monomials (e : ℕ) :
    {x : Fin 2 →₀ ℕ | x 0 = 0 ∧ x 1 < e}.ncard = e := by
  rw [line_monomials_eq_image, Set.ncard_image_of_injective _ (Finsupp.single_injective _),
    Set.ncard_coe_finset, Finset.card_range]

theorem finite_line_monomials (e : ℕ) : {x : Fin 2 →₀ ℕ | x 0 = 0 ∧ x 1 < e}.Finite := by
  rw [line_monomials_eq_image]
  exact (Finset.finite_toSet _).image _

/-- Translation of affine coordinates, `f ↦ f(x + p)`. -/
def affineTranslateEquiv (p : σ → k) : MvPolynomial σ k ≃ₐ[k] MvPolynomial σ k :=
  AlgEquiv.ofAlgHom (aeval fun i => X i + C (p i)) (aeval fun i => X i - C (p i))
    (by apply MvPolynomial.algHom_ext; intro i; simp)
    (by apply MvPolynomial.algHom_ext; intro i; simp)

theorem affineTranslateEquiv_apply (p : σ → k) (f : MvPolynomial σ k) :
    affineTranslateEquiv p f = aeval (fun i => X i + C (p i)) f := rfl

theorem eval_affineTranslateEquiv (p q : σ → k) (f : MvPolynomial σ k) :
    eval q (affineTranslateEquiv p f) = eval (q + p) f := by
  rw [affineTranslateEquiv_apply]
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => simp [hf, hg]
  | mul_X f i hf => simp [hf]

theorem map_affinePointIdeal_of_eval {τ : Type*} (e : MvPolynomial σ k ≃ₐ[k] MvPolynomial τ k)
    {p : σ → k} {q : τ → k} (he : ∀ f, eval q (e f) = eval p f) :
    (affinePointIdeal p).map e = affinePointIdeal q := by
  ext x
  rw [Ideal.mem_map_of_equiv, mem_affinePointIdeal_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [he]; exact mem_affinePointIdeal_iff.1 hy
  · intro hx
    refine ⟨e.symm x, ?_, by simp⟩
    rw [mem_affinePointIdeal_iff, ← he]; simpa using hx

theorem affinePointIdeal_zero : affinePointIdeal (0 : σ → k) = idealOfVars σ k := by
  ext f
  rw [mem_affinePointIdeal_iff, ← pow_one (idealOfVars σ k), mem_pow_idealOfVars_iff',
    eval_zero, constantCoeff_eq]
  constructor
  · intro h x hx
    have : x = 0 := (Finsupp.degree_eq_zero_iff x).1 (by omega)
    simpa [this] using h
  · intro h
    exact h 0 (by simp)

theorem length_quotient_affinePointIdeal_pow (p : Fin 2 → k) (N : ℕ) :
    Module.length k (MvPolynomial (Fin 2) k ⧸ affinePointIdeal p ^ N) =
      {x : Fin 2 →₀ ℕ | x.degree < N}.ncard := by
  have he : ∀ f, eval 0 (affineTranslateEquiv p f) = eval p f := by
    intro f; rw [eval_affineTranslateEquiv, zero_add]
  let e := Ideal.quotientEquivAlg (R₁ := k) (affinePointIdeal p ^ N)
    (idealOfVars (Fin 2) k ^ N) (affineTranslateEquiv p) (by
      rw [Ideal.map_pow]
      erw [map_affinePointIdeal_of_eval (affineTranslateEquiv p) he]
      rw [affinePointIdeal_zero])
  rw [e.toLinearEquiv.length_eq, length_quotient_of_restrictScalars_eq
    (U := {x : Fin 2 →₀ ℕ | N ≤ x.degree})]
  · rw [(finite_degree_lt_fin_two N).cast_ncard_eq]
    have : ({x : Fin 2 →₀ ℕ | N ≤ x.degree}ᶜ : Set (Fin 2 →₀ ℕ)) = {x | x.degree < N} := by
      ext x; simp
    rw [this]
    rfl
  · rw [pow_idealOfVars, restrictScalars_restrictSupportIdeal]
    rfl


/-- Multiplication by `f`, from `R ⧸ m^b` to `R ⧸ m^(a+b)` when `f ∈ m^a`. -/
def mulQuotientPow (m : Ideal (MvPolynomial σ k)) {a : ℕ} (b : ℕ)
    {f : MvPolynomial σ k} (hf : f ∈ m ^ a) :
    (MvPolynomial σ k ⧸ m ^ b) →ₗ[MvPolynomial σ k] (MvPolynomial σ k ⧸ m ^ (a + b)) :=
  (m ^ b).liftQ ((m ^ (a + b)).mkQ ∘ₗ LinearMap.mulRight (MvPolynomial σ k) f) (by
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, LinearMap.mulRight_apply, pow_add, mul_comm (m ^ a)]
    exact Ideal.mul_mem_mul hx hf)

theorem mulQuotientPow_mk (m : Ideal (MvPolynomial σ k)) {a : ℕ} (b : ℕ)
    {f : MvPolynomial σ k} (hf : f ∈ m ^ a) (x : MvPolynomial σ k) :
    mulQuotientPow m b hf (Submodule.Quotient.mk x) = Submodule.Quotient.mk (x * f) := rfl

/-- **Fulton's dimension count.** If `f ∈ m_p^a` and `g ∈ m_p^b`, then
`R ⧸ ((f, g) + m_p^(a+b))` has dimension at least `ab`. -/
theorem mul_le_length_quotient_sup_pow (p : Fin 2 → k) {a b : ℕ}
    {f g : MvPolynomial (Fin 2) k} (hf : f ∈ affinePointIdeal p ^ a)
    (hg : g ∈ affinePointIdeal p ^ b) :
    ((a * b : ℕ) : ℕ∞) ≤ Module.length k (MvPolynomial (Fin 2) k ⧸
      (Ideal.span {f, g} ⊔ affinePointIdeal p ^ (a + b))) := by
  set m := affinePointIdeal p
  set J := Ideal.span {f, g} ⊔ m ^ (a + b)
  have hg' : g ∈ m ^ b := hg
  let ψR : ((MvPolynomial (Fin 2) k ⧸ m ^ b) × (MvPolynomial (Fin 2) k ⧸ m ^ a)) →ₗ[
      MvPolynomial (Fin 2) k] (MvPolynomial (Fin 2) k ⧸ m ^ (a + b)) :=
    (mulQuotientPow m b hf).coprod
      ((Submodule.quotEquivOfEq _ _ (by rw [add_comm])).toLinearMap ∘ₗ mulQuotientPow m a hg')
  let ψ := ψR.restrictScalars k
  let π := (Ideal.Quotient.factorₐ k (show m ^ (a + b) ≤ J from le_sup_right)).toLinearMap
  have hπ : Function.Surjective π :=
    Ideal.Quotient.factor_surjective (show m ^ (a + b) ≤ J from le_sup_right)
  have hker : LinearMap.ker π ≤ LinearMap.range ψ := by
    intro x hx
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hr : r ∈ J := by
      rw [LinearMap.mem_ker] at hx
      change Ideal.Quotient.factor (show m ^ (a + b) ≤ J from le_sup_right)
        (Ideal.Quotient.mk _ r) = 0 at hx
      rwa [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hr
    obtain ⟨u, v, rfl⟩ := Ideal.mem_span_pair.1 hy
    refine ⟨(Submodule.Quotient.mk u, Submodule.Quotient.mk v), ?_⟩
    change (Submodule.Quotient.mk (u * f) + Submodule.Quotient.mk (v * g) :
      MvPolynomial (Fin 2) k ⧸ m ^ (a + b)) = Submodule.Quotient.mk _
    rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
    simpa using (m ^ (a + b)).neg_mem hz
  have hadd := Module.length_eq_add_of_exact (LinearMap.ker π).subtype π
    (Submodule.injective_subtype _) hπ (LinearMap.exact_subtype_ker_map π)
  have hle1 : Module.length k (LinearMap.ker π) ≤ Module.length k (LinearMap.range ψ) :=
    Module.length_le_of_injective (Submodule.inclusion hker) (Submodule.inclusion_injective _)
  have hle2 : Module.length k (LinearMap.range ψ) ≤
      Module.length k ((MvPolynomial (Fin 2) k ⧸ m ^ b) × (MvPolynomial (Fin 2) k ⧸ m ^ a)) :=
    Module.length_le_of_surjective ψ.rangeRestrict ψ.surjective_rangeRestrict
  rw [Module.length_prod, length_quotient_affinePointIdeal_pow,
    length_quotient_affinePointIdeal_pow] at hle2
  rw [length_quotient_affinePointIdeal_pow] at hadd
  have hT := two_mul_ncard_degree_lt_fin_two (a + b)
  have hTa := two_mul_ncard_degree_lt_fin_two a
  have hTb := two_mul_ncard_degree_lt_fin_two b
  set Ta := {x : Fin 2 →₀ ℕ | x.degree < a}.ncard
  set Tb := {x : Fin 2 →₀ ℕ | x.degree < b}.ncard
  set T := {x : Fin 2 →₀ ℕ | x.degree < a + b}.ncard
  have hTeq : T = Tb + Ta + a * b := by
    have : 2 * T = 2 * (Tb + Ta + a * b) := by
      rw [hT, mul_add 2 (Tb + Ta), mul_add 2 Tb, hTa, hTb]; ring
    omega
  have key : ((Tb + Ta : ℕ) : ℕ∞) + ((a * b : ℕ) : ℕ∞) ≤
      ((Tb + Ta : ℕ) : ℕ∞) + Module.length k (MvPolynomial (Fin 2) k ⧸ J) := by
    rw [← Nat.cast_add, ← hTeq, hadd, Nat.cast_add]
    exact add_le_add_left (hle1.trans hle2) _
  exact (ENat.add_le_add_iff_left (ENat.natCast_ne_top _)).1 key


theorem ringKrullDim_mvPolynomial_fin_two :
    ringKrullDim (MvPolynomial (Fin 2) k) = 2 := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

/-- A prime of `k[x, y]` containing two non-associated irreducible polynomials is maximal. -/
theorem isMaximal_of_irreducible_mem {f g : MvPolynomial (Fin 2) k} (hf : Irreducible f)
    (hg : Irreducible g) (hfg : ¬Associated f g) {Q : Ideal (MvPolynomial (Fin 2) k)}
    [hQ : Q.IsPrime] (hfQ : f ∈ Q) (hgQ : g ∈ Q) : Q.IsMaximal := by
  have hdim := ringKrullDim_mvPolynomial_fin_two (k := k)
  have : FiniteRingKrullDim (MvPolynomial (Fin 2) k) := by
    rw [finiteRingKrullDim_iff_ne_bot_and_top, hdim]
    exact ⟨by decide, by decide⟩
  have hle : Q.height ≤ 2 := by
    have := Q.height_le_ringKrullDim_of_isPrime
    rw [hdim] at this
    exact WithBot.coe_le_coe.1 this
  have hfprime : Prime f := UniqueFactorizationMonoid.irreducible_iff_prime.1 hf
  have h0 : Q.height ≠ 0 := by
    rw [Ne, Ideal.height_eq_zero_iff_eq_bot]
    rintro rfl
    exact hf.ne_zero ((Submodule.mem_bot _).1 hfQ)
  have h1 : Q.height ≠ 1 := by
    intro h1
    have hQf := Ideal.eq_span_singleton_of_height_eq_one h1 hfQ hfprime
    rw [hQf, Ideal.mem_span_singleton] at hgQ
    exact hfg (hf.associated_of_dvd hg hgQ)
  have h2 : Q.height = 2 := by
    have hne : Q.height ≠ ⊤ := (lt_of_le_of_lt hle (by decide)).ne
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hne
    rw [← hn] at hle h0 h1 ⊢
    norm_cast at hle h0 h1 ⊢
    omega
  apply Ideal.isMaximal_of_height_eq_ringKrullDim
  rw [h2, hdim]; rfl

/-- For distinct irreducible plane curves, `O_P ⧸ (f, g)` is an Artinian ring. -/
theorem isArtinianRing_localQuotient {f g : MvPolynomial (Fin 2) k} (hf : Irreducible f)
    (hg : Irreducible g) (hfg : ¬Associated f g) (p : Fin 2 → k) :
    IsArtinianRing (affineLocalRing p ⧸ Ideal.span
      {algebraMap (MvPolynomial (Fin 2) k) (affineLocalRing p) f,
        algebraMap (MvPolynomial (Fin 2) k) (affineLocalRing p) g}) := by
  set O := affineLocalRing p
  set I := Ideal.span {algebraMap (MvPolynomial (Fin 2) k) O f,
    algebraMap (MvPolynomial (Fin 2) k) O g}
  have : Ring.KrullDimLE 0 (O ⧸ I) := by
    refine Ring.KrullDimLE.mk₀ fun P hP => ?_
    have hmk : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
    have : (P.comap (Ideal.Quotient.mk I)).IsPrime := Ideal.comap_isPrime _ P
    set J := P.comap (Ideal.Quotient.mk I)
    have : (J.comap (algebraMap (MvPolynomial (Fin 2) k) O)).IsPrime := Ideal.comap_isPrime _ J
    have hIJ : I ≤ J := by
      intro x hx
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hx]
      exact P.zero_mem
    have hQmax : (J.comap (algebraMap (MvPolynomial (Fin 2) k) O)).IsMaximal :=
      isMaximal_of_irreducible_mem hf hg hfg
        (hIJ (Ideal.subset_span (Set.mem_insert _ _)))
        (hIJ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl)))
    have hQle : J.comap (algebraMap (MvPolynomial (Fin 2) k) O) ≤ affinePointIdeal p := by
      have := (IsLocalization.isPrime_iff_isPrime_disjoint (affinePointIdeal p).primeCompl O J).1
        inferInstance
      intro x hx
      by_contra hxp
      exact Set.disjoint_left.1 this.2 hxp hx
    have hQeq := hQmax.eq_of_le (affinePointIdeal_isMaximal p).ne_top hQle
    have hJmax : J = IsLocalRing.maximalIdeal O := by
      rw [← IsLocalization.map_under (affinePointIdeal p).primeCompl O J]
      change Ideal.map _ (J.comap (algebraMap (MvPolynomial (Fin 2) k) O)) = _
      rw [hQeq, Localization.AtPrime.map_eq_maximalIdeal]
    have hJm : J.IsMaximal := hJmax ▸ IsLocalRing.maximalIdeal.isMaximal O
    have hPJ : P = J.map (Ideal.Quotient.mk I) := (Ideal.map_comap_of_surjective _ hmk P).symm
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective _ hmk hJm with h | h
    · exact absurd (hPJ.trans h) hP.ne_top
    · rw [hPJ]; exact h
  exact (isArtinianRing_iff_krullDimLE_zero (R := O ⧸ I)).2 this


/-- **Multiplicity of a point on a plane curve** (Hartshorne I, Exercise 5.3).  After
translating `P` to the origin, `mult_P(f)` is the lowest degree of a monomial occurring in
`f(x + P)`. -/
def planeCurveMultiplicity (f : MvPolynomial (Fin 2) k) (P : Fin 2 → k) : ℕ :=
  sInf (Finsupp.degree '' ((affineTranslateEquiv P f).support : Set (Fin 2 →₀ ℕ)))

theorem mem_affinePointIdeal_pow_planeCurveMultiplicity (f : MvPolynomial (Fin 2) k)
    (P : Fin 2 → k) : f ∈ affinePointIdeal P ^ planeCurveMultiplicity f P := by
  have hmem : affineTranslateEquiv P f ∈ idealOfVars (Fin 2) k ^ planeCurveMultiplicity f P := by
    rw [mem_pow_idealOfVars_iff]
    intro x hx
    exact Nat.sInf_le ⟨x, hx, rfl⟩
  have he : ∀ g, eval P ((affineTranslateEquiv P).symm g) = eval 0 g := by
    intro g
    have := eval_affineTranslateEquiv P 0 ((affineTranslateEquiv P).symm g)
    rw [zero_add, AlgEquiv.apply_symm_apply] at this
    exact this.symm
  have hmap := map_affinePointIdeal_of_eval (affineTranslateEquiv P).symm he
  rw [affinePointIdeal_zero] at hmap
  rw [← hmap, ← Ideal.map_pow]
  have := Ideal.mem_map_of_mem (affineTranslateEquiv P).symm hmem
  simpa using this

theorem le_affineLocalIntersectionMultiplicity_of_mem_pow (p : Fin 2 → k) {a b : ℕ}
    {f g : MvPolynomial (Fin 2) k} (hf : f ∈ affinePointIdeal p ^ a)
    (hg : g ∈ affinePointIdeal p ^ b) :
    ((a * b : ℕ) : ℕ∞) ≤ affineLocalIntersectionMultiplicity f g p := by
  set J := Ideal.span {f, g} ⊔ affinePointIdeal p ^ (a + b)
  refine (mul_le_length_quotient_sup_pow p hf hg).trans ?_
  rw [← length_localQuotient_eq (show affinePointIdeal p ^ (a + b) ≤ J from le_sup_right)]
  have hle : Ideal.span {algebraMap (MvPolynomial (Fin 2) k) (affineLocalRing p) f,
      algebraMap (MvPolynomial (Fin 2) k) (affineLocalRing p) g} ≤
      J.map (algebraMap (MvPolynomial (Fin 2) k) (affineLocalRing p)) := by
    rw [← Set.image_pair, ← Ideal.map_span]
    exact Ideal.map_mono le_sup_left
  exact Module.length_le_of_surjective
    (Ideal.Quotient.factorₐ (affineLocalRing p) hle).toLinearMap
    (Ideal.Quotient.factor_surjective hle)

/-- **Hartshorne I, Exercise 5.4(a).** For distinct affine plane curves `Y = (f = 0)` and
`Z = (g = 0)` and `P ∈ Y ∩ Z`, the local intersection multiplicity `(Y · Z)_P` is finite and at
least `mult_P(Y) · mult_P(Z)`. -/
theorem affineLocalIntersectionMultiplicity_ne_top_and_ge {f g : MvPolynomial (Fin 2) k}
    (hf : Irreducible f) (hg : Irreducible g) (hfg : ¬Associated f g) :
    ∀ P ∈ zeroSet ({f} : Set (MvPolynomial (Fin 2) k)) ∩ zeroSet {g},
      affineLocalIntersectionMultiplicity f g P ≠ ⊤ ∧
        ((planeCurveMultiplicity f P * planeCurveMultiplicity g P : ℕ) : ℕ∞) ≤
          affineLocalIntersectionMultiplicity f g P := by
  rintro P -
  refine ⟨?_, le_affineLocalIntersectionMultiplicity_of_mem_pow P
    (mem_affinePointIdeal_pow_planeCurveMultiplicity f P)
    (mem_affinePointIdeal_pow_planeCurveMultiplicity g P)⟩
  set I := Ideal.span {algebraMap (MvPolynomial (Fin 2) k) (affineLocalRing P) f,
    algebraMap (MvPolynomial (Fin 2) k) (affineLocalRing P) g}
  have := isArtinianRing_localQuotient hf hg hfg P
  rw [affineLocalIntersectionMultiplicity, Module.length_eq_of_surjective
    (R := affineLocalRing P ⧸ I) (by exact Ideal.Quotient.mk_surjective)]
  exact Module.length_ne_top


/-- Restriction of a plane polynomial to the axis `x₀ = 0`, as a polynomial in `t = x₁`. -/
abbrev axisRestrict : MvPolynomial (Fin 2) k →ₐ[k] Polynomial k :=
  aeval ![0, Polynomial.X]

/-- The axis `x₀ = 0` parametrized by `t ↦ (0, t)`, on polynomials: `t ↦ x₁`. -/
abbrev axisSection : Polynomial k →ₐ[k] MvPolynomial (Fin 2) k :=
  Polynomial.aeval (X 1)

theorem sub_axis_mem_span_X (h : MvPolynomial (Fin 2) k) :
    h - axisSection (axisRestrict h) ∈ Ideal.span {(X 0 : MvPolynomial (Fin 2) k)} := by
  induction h using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg =>
    rw [map_add, map_add, add_sub_add_comm]
    exact Ideal.add_mem _ hf hg
  | mul_X f i hf =>
    rw [map_mul, map_mul]
    have hi : (X i : MvPolynomial (Fin 2) k) - axisSection (axisRestrict (X i)) ∈
        Ideal.span {(X 0 : MvPolynomial (Fin 2) k)} := by
      fin_cases i
      · simp
      · simp
    have : f * X i - axisSection (axisRestrict f) *
        axisSection (axisRestrict (X i)) =
        (f - axisSection (axisRestrict f)) * X i +
          axisSection (axisRestrict f) *
            (X i - axisSection (axisRestrict (X i))) := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hf) (Ideal.mul_mem_left _ _ hi)

theorem span_X_X_pow_eq_monomial (e : ℕ) :
    Ideal.span {(X 0 : MvPolynomial (Fin 2) k), X 1 ^ e} =
      Ideal.span ((fun s => monomial s (1 : k)) ''
        {Finsupp.single (0 : Fin 2) 1, Finsupp.single (1 : Fin 2) e}) := by
  rw [Set.image_pair, X, X_pow_eq_monomial]

theorem affinePointIdeal_zero_pow_le_span (e : ℕ) :
    affinePointIdeal (0 : Fin 2 → k) ^ e ≤ Ideal.span {(X 0 : MvPolynomial (Fin 2) k), X 1 ^ e} := by
  intro x hx
  rw [affinePointIdeal_zero, mem_pow_idealOfVars_iff] at hx
  rw [span_X_X_pow_eq_monomial, mem_ideal_span_monomial_image]
  intro y hy
  have hdeg := hx y hy
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hdeg
  by_cases h0 : 1 ≤ y 0
  · exact ⟨_, Set.mem_insert _ _, Finsupp.single_le_iff.2 h0⟩
  · exact ⟨_, Set.mem_insert_of_mem _ rfl, Finsupp.single_le_iff.2 (by omega)⟩

theorem length_quotient_X_X_pow (e : ℕ) :
    Module.length k (MvPolynomial (Fin 2) k ⧸
      Ideal.span {(X 0 : MvPolynomial (Fin 2) k), X 1 ^ e}) = e := by
  have hspan := span_X_X_pow_eq_monomial (k := k) e
  rw [length_quotient_of_restrictScalars_eq (U := {x : Fin 2 →₀ ℕ | 1 ≤ x 0 ∨ e ≤ x 1})]
  · have : ({x : Fin 2 →₀ ℕ | 1 ≤ x 0 ∨ e ≤ x 1}ᶜ : Set (Fin 2 →₀ ℕ)) =
        {x | x 0 = 0 ∧ x 1 < e} := by
      ext x; simp only [Set.mem_compl_iff, Set.mem_ofPred_eq]; omega
    rw [this]
    change ({x : Fin 2 →₀ ℕ | x 0 = 0 ∧ x 1 < e}).encard = e
    rw [← (finite_line_monomials e).cast_ncard_eq, ncard_line_monomials]
  · ext x
    rw [Submodule.restrictScalars_mem, hspan, mem_ideal_span_monomial_image,
      MvPolynomial.mem_restrictSupport_iff, Set.subset_def]
    refine forall₂_congr fun y hy => ?_
    simp [Finsupp.single_le_iff]


/-- **Intersection with the axis `x₀ = 0` at the origin.**  The local intersection
multiplicity of `x₀ = 0` with `h = 0` at the origin is the order of vanishing at `t = 0` of
the restriction `h(0, t)`. -/
theorem affineLocalIntersectionMultiplicity_X_zero (h : MvPolynomial (Fin 2) k)
    (hr : axisRestrict h ≠ 0) :
    affineLocalIntersectionMultiplicity (X 0) h 0 = (axisRestrict h).natTrailingDegree := by
  set r := axisRestrict h
  set O := affineLocalRing (0 : Fin 2 → k)
  set a := algebraMap (MvPolynomial (Fin 2) k) O
  obtain ⟨u, hru, hu⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd r hr 0
  rw [map_zero, sub_zero, Polynomial.rootMultiplicity_eq_natTrailingDegree'] at hru
  rw [map_zero, sub_zero, Polynomial.X_dvd_iff] at hu
  set e := r.natTrailingDegree
  have hθ := sub_axis_mem_span_X h
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.1 hθ
  have hsec : axisSection r = X 1 ^ e * axisSection u := by
    rw [hru, map_mul, map_pow, Polynomial.aeval_X]
  have hunit : IsUnit (a (axisSection u)) := by
    rw [IsLocalization.AtPrime.isUnit_to_map_iff O (affinePointIdeal (0 : Fin 2 → k))]
    change axisSection u ∉ affinePointIdeal (0 : Fin 2 → k)
    have h0 : eval (0 : Fin 2 → k) (axisSection u) = u.coeff 0 := by
      have := Polynomial.aeval_algHom_apply (MvPolynomial.aeval (0 : Fin 2 → k))
        (X 1 : MvPolynomial (Fin 2) k) u
      simp only [aeval_X, Pi.zero_apply] at this
      rw [Polynomial.coeff_zero_eq_eval_zero, ← Polynomial.coe_aeval_eq_eval, this]
      rfl
    rw [mem_affinePointIdeal_iff, h0]
    exact hu
  have hh : a h = a q * a (X 0) + a (X 1 ^ e) * a (axisSection u) := by
    rw [← map_mul, ← map_mul, ← map_add, ← hsec, hq, sub_add_cancel]
  have hspan : Ideal.span {a (X 0), a h} = Ideal.span {a (X 0), a (X 1 ^ e)} := by
    apply le_antisymm
    · rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      refine ⟨Ideal.subset_span (Set.mem_insert _ _), ?_⟩
      rw [SetLike.mem_coe, hh]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _)))
        (Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl)))
    · rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      refine ⟨Ideal.subset_span (Set.mem_insert _ _), ?_⟩
      have : a (X 1 ^ e) = (a h - a q * a (X 0)) * ↑hunit.unit⁻¹ := by
        rw [hh, add_sub_cancel_left, mul_assoc, IsUnit.mul_val_inv, mul_one]
      rw [SetLike.mem_coe, this]
      exact Ideal.mul_mem_right _ _ (Ideal.sub_mem _
        (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _))))
  rw [affineLocalIntersectionMultiplicity]
  change Module.length O (O ⧸ Ideal.span {a (X 0), a h}) = _
  rw [hspan, ← Set.image_pair, ← Ideal.map_span,
    length_localQuotient_eq (affinePointIdeal_zero_pow_le_span e), length_quotient_X_X_pow]


/-- The affine linear polynomial `a x₀ + b x₁ + c`; for `(a, b) ≠ (0, 0)` its zero set is a line
in `𝔸²`. -/
def planeLineEquation (a b c : k) : MvPolynomial (Fin 2) k :=
  C a * X 0 + C b * X 1 + C c

/-- Restriction of a plane polynomial to the parametrized line `t ↦ P + t v`. -/
abbrev lineRestrict (P v : Fin 2 → k) : MvPolynomial (Fin 2) k →ₐ[k] Polynomial k :=
  aeval fun i => Polynomial.C (P i) + Polynomial.C (v i) * Polynomial.X

theorem eval_aeval_mvPolynomial {τ : Type*} (g : σ → MvPolynomial τ k) (q : τ → k)
    (f : MvPolynomial σ k) : eval q (aeval g f) = eval (fun i => eval q (g i)) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => simp [hf, hg]
  | mul_X f i hf => simp [hf]

/-- An affine change of coordinates `x ↦ P + x₀ w + x₁ v` of the plane. -/
def planeAffineChange (P w v : Fin 2 → k) (hdet : w 0 * v 1 - w 1 * v 0 = 1) :
    MvPolynomial (Fin 2) k ≃ₐ[k] MvPolynomial (Fin 2) k :=
  AlgEquiv.ofAlgHom (aeval fun i => C (P i) + X 0 * C (w i) + X 1 * C (v i))
    (aeval ![C (v 1) * (X 0 - C (P 0)) - C (v 0) * (X 1 - C (P 1)),
      C (w 0) * (X 1 - C (P 1)) - C (w 1) * (X 0 - C (P 0))])
    (by
      have hd : C (w 0) * C (v 1) - C (w 1) * C (v 0) = (1 : MvPolynomial (Fin 2) k) := by
        rw [← map_mul, ← map_mul, ← map_sub, hdet, map_one]
      apply MvPolynomial.algHom_ext
      intro i
      fin_cases i
      · simp only [AlgHom.coe_comp, Function.comp_apply, aeval_X, AlgHom.coe_id, id_eq]
        simp
        linear_combination X 0 * hd
      · simp
        linear_combination X 1 * hd)
    (by
      have hd : C (w 0) * C (v 1) - C (w 1) * C (v 0) = (1 : MvPolynomial (Fin 2) k) := by
        rw [← map_mul, ← map_mul, ← map_sub, hdet, map_one]
      apply MvPolynomial.algHom_ext
      intro i
      fin_cases i
      · simp
        linear_combination (X 0 - C (P 0)) * hd
      · simp
        linear_combination (X 1 - C (P 1)) * hd)


theorem planeAffineChange_apply (P w v : Fin 2 → k) (hdet : w 0 * v 1 - w 1 * v 0 = 1)
    (f : MvPolynomial (Fin 2) k) :
    planeAffineChange P w v hdet f = aeval (fun i => C (P i) + X 0 * C (w i) + X 1 * C (v i)) f :=
  rfl

/-- **Intersection with a line.**  If the line `a x₀ + b x₁ + c = 0` passes through `P`, then
its local intersection multiplicity with `f = 0` at `P` is the order of vanishing at `t = 0` of
`f(P + t(-b, a))`, provided this restriction is not identically zero. -/
theorem affineLocalIntersectionMultiplicity_planeLineEquation {a b c : k} (hab : a ≠ 0 ∨ b ≠ 0)
    {P : Fin 2 → k} (hP : a * P 0 + b * P 1 + c = 0) (f : MvPolynomial (Fin 2) k)
    (hr : lineRestrict P ![-b, a] f ≠ 0) :
    affineLocalIntersectionMultiplicity (planeLineEquation a b c) f P =
      (lineRestrict P ![-b, a] f).natTrailingDegree := by
  obtain ⟨w, hw⟩ : ∃ w : Fin 2 → k, a * w 0 + b * w 1 = 1 := by
    rcases hab with ha | hb
    · exact ⟨![a⁻¹, 0], by simp [ha]⟩
    · exact ⟨![0, b⁻¹], by simp [hb]⟩
  have hdet : w 0 * (![-b, a] : Fin 2 → k) 1 - w 1 * (![-b, a] : Fin 2 → k) 0 = 1 := by
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    linear_combination hw
  set T := planeAffineChange P w ![-b, a] hdet
  have he : ∀ g, eval 0 (T g) = eval P g := by
    intro g
    rw [planeAffineChange_apply, eval_aeval_mvPolynomial]
    have : (fun i => eval (0 : Fin 2 → k) (C (P i) + X 0 * C (w i) +
        X 1 * C ((![-b, a] : Fin 2 → k) i))) = P := by
      funext i; simp
    rw [this]
  rw [← affineLocalIntersectionMultiplicity_algEquiv T P 0 he]
  have hTl : T (planeLineEquation a b c) = X 0 := by
    have hw' : C a * C (w 0) + C b * C (w 1) = (1 : MvPolynomial (Fin 2) k) := by
      rw [← map_mul, ← map_mul, ← map_add, hw, map_one]
    have hP' : C a * C (P 0) + C b * C (P 1) + C c = (0 : MvPolynomial (Fin 2) k) := by
      rw [← map_mul, ← map_mul, ← map_add, ← map_add, hP, map_zero]
    rw [planeAffineChange_apply, planeLineEquation]
    simp only [map_add, map_mul, aeval_X, aeval_C, algebraMap_eq, Matrix.cons_val_zero,
      Matrix.cons_val_one, map_neg]
    linear_combination X 0 * hw' + hP'
  have hTf : axisRestrict (T f) = lineRestrict P ![-b, a] f := by
    have hcomp : axisRestrict.comp (aeval fun i => C (P i) + X 0 * C (w i) +
        X 1 * C ((![-b, a] : Fin 2 → k) i)) = lineRestrict P ![-b, a] := by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [AlgHom.coe_comp, Function.comp_apply, aeval_X, map_add, map_mul, aeval_C]
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
          Polynomial.algebraMap_eq]
        ring
      · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
          Polynomial.algebraMap_eq]
        ring
    rw [planeAffineChange_apply, ← AlgHom.comp_apply, hcomp]
  rw [hTl, affineLocalIntersectionMultiplicity_X_zero _ (by rwa [hTf]), hTf]


/-- The restriction of `F` to the line `t ↦ t v` through the origin has `j`-th coefficient
`F_j(v)`, the value at `v` of the degree-`j` homogeneous component. -/
theorem coeff_aeval_smul_X (F : MvPolynomial (Fin 2) k) (v : Fin 2 → k) (j : ℕ) :
    (aeval (fun i => Polynomial.C (v i) * Polynomial.X) F).coeff j =
      eval v (homogeneousComponent j F) := by
  classical
  induction F using MvPolynomial.induction_on' with
  | monomial x c =>
    rw [aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two,
      mul_pow, mul_pow]
    have hprod : algebraMap k (Polynomial k) c * (Polynomial.C (v 0) ^ x 0 *
        Polynomial.X ^ x 0 * (Polynomial.C (v 1) ^ x 1 * Polynomial.X ^ x 1)) =
        Polynomial.C (c * (v 0 ^ x 0 * v 1 ^ x 1)) * Polynomial.X ^ (x 0 + x 1) := by
      simp only [Polynomial.algebraMap_eq, map_mul, map_pow, pow_add]
      ring
    rw [hprod, Polynomial.coeff_C_mul_X_pow]
    have hdeg : x.degree = x 0 + x 1 := by rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
    by_cases hj : j = x 0 + x 1
    · subst hj
      rw [if_pos rfl, homogeneousComponent_of_mem (by
        rw [mem_homogeneousSubmodule]; exact isHomogeneous_monomial _ hdeg), if_pos rfl,
        eval_monomial, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
    · rw [if_neg hj, homogeneousComponent_of_mem (by
        rw [mem_homogeneousSubmodule]; exact isHomogeneous_monomial _ hdeg), if_neg hj,
        map_zero]
  | add p q hp hq => simp [hp, hq]

theorem lineRestrict_eq_aeval_translate (P v : Fin 2 → k) (f : MvPolynomial (Fin 2) k) :
    lineRestrict P v f =
      aeval (fun i => Polynomial.C (v i) * Polynomial.X) (affineTranslateEquiv P f) := by
  rw [affineTranslateEquiv_apply, ← AlgHom.comp_apply]
  congr 1
  apply MvPolynomial.algHom_ext
  intro i
  simp only [aeval_X, AlgHom.coe_comp, Function.comp_apply, map_add, aeval_C,
    Polynomial.algebraMap_eq]
  ring

theorem homogeneousComponent_eq_zero_of_lt_planeCurveMultiplicity (f : MvPolynomial (Fin 2) k)
    (P : Fin 2 → k) {j : ℕ} (hj : j < planeCurveMultiplicity f P) :
    homogeneousComponent j (affineTranslateEquiv P f) = 0 := by
  apply homogeneousComponent_eq_zero'
  intro d hd hdj
  have h1 : planeCurveMultiplicity f P ≤ j := Nat.sInf_le ⟨d, hd, hdj⟩
  omega

theorem homogeneousComponent_planeCurveMultiplicity_ne_zero {f : MvPolynomial (Fin 2) k}
    (hf : f ≠ 0) (P : Fin 2 → k) :
    homogeneousComponent (planeCurveMultiplicity f P) (affineTranslateEquiv P f) ≠ 0 := by
  have hF : affineTranslateEquiv P f ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (affineTranslateEquiv P).injective]
  obtain ⟨d, hd⟩ : (affineTranslateEquiv P f).support.Nonempty :=
    Finset.nonempty_iff_ne_empty.2 (by rwa [Ne, MvPolynomial.support_eq_empty])
  have hmem := Nat.sInf_mem (s := Finsupp.degree '' ((affineTranslateEquiv P f).support :
    Set (Fin 2 →₀ ℕ))) ⟨_, d, hd, rfl⟩
  obtain ⟨x, hx, hxdeg⟩ := hmem
  change x.degree = planeCurveMultiplicity f P at hxdeg
  intro h0
  have := congrArg (coeff x) h0
  rw [coeff_homogeneousComponent, if_pos hxdeg, coeff_zero] at this
  exact (mem_support_iff.1 hx) this

/-- The degree-`0` part of `f(x + P)` is the constant `f(P)`. -/
theorem homogeneousComponent_zero_affineTranslateEquiv (f : MvPolynomial (Fin 2) k)
    (P : Fin 2 → k) :
    homogeneousComponent 0 (affineTranslateEquiv P f) = C (eval P f) := by
  rw [homogeneousComponent_zero, ← constantCoeff_eq, ← MvPolynomial.eval_zero,
    eval_affineTranslateEquiv, zero_add]

/-- A point `P` lies on the plane curve `f = 0` if and only if `mult_P(f) > 0` (Hartshorne I,
Exercise 5.3). -/
theorem planeCurveMultiplicity_pos_iff {f : MvPolynomial (Fin 2) k} (hf : f ≠ 0)
    (P : Fin 2 → k) : 0 < planeCurveMultiplicity f P ↔ eval P f = 0 := by
  constructor
  · intro h
    have h0 := homogeneousComponent_eq_zero_of_lt_planeCurveMultiplicity f P h
    rwa [homogeneousComponent_zero_affineTranslateEquiv, C_eq_zero] at h0
  · intro h
    refine Nat.pos_of_ne_zero fun h0 => ?_
    have hne := homogeneousComponent_planeCurveMultiplicity_ne_zero hf P
    rw [h0, homogeneousComponent_zero_affineTranslateEquiv, h, C_0] at hne
    exact hne rfl

/-- Along a line through `P` whose direction is not a zero of the leading form, the
restriction of `f` vanishes to order exactly `mult_P(f)`. -/
theorem natTrailingDegree_lineRestrict {f : MvPolynomial (Fin 2) k} (P v : Fin 2 → k)
    (hv : eval v (homogeneousComponent (planeCurveMultiplicity f P)
      (affineTranslateEquiv P f)) ≠ 0) :
    lineRestrict P v f ≠ 0 ∧
      (lineRestrict P v f).natTrailingDegree = planeCurveMultiplicity f P := by
  have hcoeff : ∀ j, (lineRestrict P v f).coeff j =
      eval v (homogeneousComponent j (affineTranslateEquiv P f)) := by
    intro j; rw [lineRestrict_eq_aeval_translate, coeff_aeval_smul_X]
  have hm : (lineRestrict P v f).coeff (planeCurveMultiplicity f P) ≠ 0 := by
    rwa [hcoeff]
  have hne : lineRestrict P v f ≠ 0 := fun h => hm (by rw [h, Polynomial.coeff_zero])
  refine ⟨hne, le_antisymm (Polynomial.natTrailingDegree_le_of_ne_zero hm)
    (Polynomial.le_natTrailingDegree hne fun j hj => ?_)⟩
  rw [hcoeff, homogeneousComponent_eq_zero_of_lt_planeCurveMultiplicity f P hj, map_zero]


theorem polynomial_eval_aeval (g : σ → Polynomial k) (s : k) (F : MvPolynomial σ k) :
    (aeval g F).eval s = eval (fun i => (g i).eval s) F := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => simp [hf, hg]
  | mul_X f i hf => simp [hf]

theorem eval_planeLineEquation (a b c : k) (y : Fin 2 → k) :
    eval y (planeLineEquation a b c) = a * y 0 + b * y 1 + c := by
  simp [planeLineEquation]

/-- A nonzero binary form has only finitely many zeros of the form `(1, s)`. -/
theorem finite_setOf_eval_one_eq_zero [Infinite k] {G : MvPolynomial (Fin 2) k} (hG : G ≠ 0)
    {m : ℕ} (hGhom : G.IsHomogeneous m) : {s : k | eval ![1, s] G = 0}.Finite := by
  set ρ : Polynomial k := aeval ![1, Polynomial.X] G
  have hρeval : ∀ s : k, ρ.eval s = eval ![1, s] G := by
    intro s
    rw [polynomial_eval_aeval]
    have : (fun i => (((![1, Polynomial.X] : Fin 2 → Polynomial k)) i).eval s) = ![1, s] := by
      funext i; fin_cases i <;> simp
    rw [this]
  have hρ : ρ ≠ 0 := by
    obtain ⟨v, hv⟩ : ∃ v : Fin 2 → k, eval v (X 0 * G) ≠ 0 := by
      by_contra! h
      exact mul_ne_zero (X_ne_zero 0) hG (MvPolynomial.funext fun v => by simpa using h v)
    rw [map_mul, eval_X] at hv
    have hv0 : v 0 ≠ 0 := left_ne_zero_of_mul hv
    have hv' : eval v G ≠ 0 := right_ne_zero_of_mul hv
    intro h0
    have h1 := hρeval (v 1 / v 0)
    rw [h0, Polynomial.eval_zero] at h1
    have hsmul : v = v 0 • ![1, v 1 / v 0] := by
      funext i; fin_cases i <;> simp [hv0, mul_div_cancel₀]
    rw [hsmul, hGhom.eval_smul, ← h1, mul_zero] at hv'
    exact hv' rfl
  refine (Polynomial.finite_setOfPred_isRoot hρ).subset fun s hs => ?_
  change ρ.IsRoot s
  rw [Polynomial.IsRoot, hρeval]
  exact hs

theorem eval_one_slope_eq_zero {G : MvPolynomial (Fin 2) k} {m : ℕ} (hGhom : G.IsHomogeneous m)
    {a b : k} (hb : b ≠ 0) (hz : eval ![-b, a] G = 0) : eval ![1, -a / b] G = 0 := by
  have hsmul : (![-b, a] : Fin 2 → k) = (-b) • ![1, -a / b] := by
    funext i
    fin_cases i
    · simp
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, Pi.smul_apply,
        smul_eq_mul]
      field_simp
  rw [hsmul, hGhom.eval_smul] at hz
  exact (mul_eq_zero.1 hz).resolve_left (pow_ne_zero _ (neg_ne_zero.2 hb))

theorem zeroSet_planeLineEquation_vertical {a c : k} (ha : a ≠ 0) {P : Fin 2 → k}
    (hP : a * P 0 + 0 * P 1 + c = 0) :
    zeroSet {planeLineEquation a 0 c} = zeroSet {planeLineEquation (1 : k) 0 (-P 0)} := by
  ext y
  simp only [mem_zeroSet_iff, Set.mem_singleton_iff, forall_eq, eval_planeLineEquation]
  constructor
  · intro h
    have : a * (y 0 - P 0) = 0 := by linear_combination h - hP
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd h' ha
    · linear_combination h'
  · intro h
    linear_combination a * h + hP

theorem zeroSet_planeLineEquation_slope {a b c : k} (hb : b ≠ 0) {P : Fin 2 → k}
    (hP : a * P 0 + b * P 1 + c = 0) :
    zeroSet {planeLineEquation a b c} =
      zeroSet {planeLineEquation (-a / b) (-1) (P 1 - -a / b * P 0)} := by
  ext y
  simp only [mem_zeroSet_iff, Set.mem_singleton_iff, forall_eq, eval_planeLineEquation]
  have key : -a / b * y 0 + -1 * y 1 + (P 1 - -a / b * P 0) =
      -(a * y 0 + b * y 1 + c) / b + (a * P 0 + b * P 1 + c) / b := by
    field_simp; ring
  rw [key, hP, zero_div, add_zero, neg_div, neg_eq_zero, div_eq_zero_iff, or_iff_left hb]

/-- **Hartshorne I, Exercise 5.4(b).** For all but finitely many lines `L` through a point `P`
of the plane curve `Y = (f = 0)`, `(L · Y)_P = mult_P(Y)`. -/
theorem finite_lines_affineLocalIntersectionMultiplicity_ne [IsAlgClosed k]
    {f : MvPolynomial (Fin 2) k} (hf : Irreducible f) :
    ∀ P ∈ zeroSet ({f} : Set (MvPolynomial (Fin 2) k)),
      {L : Set (Fin 2 → k) | ∃ a b c : k, (a ≠ 0 ∨ b ≠ 0) ∧
        L = zeroSet {planeLineEquation a b c} ∧ P ∈ L ∧
        affineLocalIntersectionMultiplicity (planeLineEquation a b c) f P ≠
          planeCurveMultiplicity f P}.Finite := by
  rintro P -
  set Fm := homogeneousComponent (planeCurveMultiplicity f P) (affineTranslateEquiv P f)
  have hFmhom : Fm.IsHomogeneous (planeCurveMultiplicity f P) :=
    homogeneousComponent_isHomogeneous _ _
  refine (((finite_setOf_eval_one_eq_zero
    (homogeneousComponent_planeCurveMultiplicity_ne_zero hf.ne_zero P) hFmhom).image
    (fun s : k => zeroSet {planeLineEquation s (-1) (P 1 - s * P 0)})).union
    (Set.finite_singleton (zeroSet {planeLineEquation (1 : k) 0 (-P 0)}))).subset ?_
  rintro L ⟨a, b, c, hab, rfl, hPL, hne⟩
  have hP : a * P 0 + b * P 1 + c = 0 := by
    simpa [eval_planeLineEquation] using hPL
  -- A bad line has direction a zero of the leading form.
  have hz : eval ![-b, a] Fm = 0 := by
    by_contra hv
    obtain ⟨hr, hdeg⟩ := natTrailingDegree_lineRestrict P ![-b, a] hv
    exact hne (by rw [affineLocalIntersectionMultiplicity_planeLineEquation hab hP f hr, hdeg])
  by_cases hb : b = 0
  · subst hb
    exact Or.inr (zeroSet_planeLineEquation_vertical (hab.resolve_right (fun h => h rfl)) hP)
  · exact Or.inl ⟨-a / b, eval_one_slope_eq_zero hFmhom hb hz,
      (zeroSet_planeLineEquation_slope hb hP).symm⟩

end
end Hartshorne

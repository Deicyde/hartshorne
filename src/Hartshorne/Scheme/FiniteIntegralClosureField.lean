/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Finiteness of integral closures over an arbitrary field

Hartshorne, *Algebraic Geometry*, II.5, the normalization input in the proof of Theorem 5.19
(p. 123); Stacks Project, Tag 0335 (finite-type algebras over a field are Nagata, hence
Japanese).

Let `k` be an arbitrary field, `A` a finitely generated `k`-algebra domain with fraction field
`K`, and `L / K` a finite extension. Then the integral closure of `A` in `L` is a finite
`A`-module.

## Proof

By Noether normalization it suffices to treat `P = k[X₁, …, Xₙ]` with fraction field `F`. Let
`M` be the separable closure of `F` in `L`; the integral closure `C` of `P` in `M` is finite over
`P` (trace form), and `L / M` is purely inseparable of some exponent, so `z ↦ z ^ q` maps `L`
into `M`, with `q = p ^ e` a power of the exponential characteristic. For `z` integral over `P`,
`z ^ q` lies in `C`, so its coordinates in a fixed `F`-basis of `M` lie in `d⁻¹ P` for a fixed
`d`. Writing `z` in an `F`-basis of `L` shows that, after clearing denominators, these
coordinates have all their polynomial coefficients in a subfield `k₀ ⊆ k` that is finite over
`k ^ q`: it is generated over `k ^ q` by finitely many coefficients that do not depend on `z`.
Polynomials with coefficients in `k₀` form a finitely generated module over the Frobenius image
`P ^ q`, which is Noetherian, so the `q`-th powers of the integral closure form a finitely
generated `P ^ q`-module. Injectivity of Frobenius then shows that the integral closure is a
finitely generated `P`-module. No perfectness of `k` and no separability of `L / K` is assumed.

## Main results

* `Hartshorne.moduleFinite_integralClosure_mvPolynomial_of_field`: the polynomial case.
* `Hartshorne.moduleFinite_integralClosure_of_finiteType_of_field`: the general statement.
-/

open MvPolynomial

namespace Hartshorne

section Coefficients

variable {k : Type*} [Field k] {σ : Type*}

/-- If `g ≠ 0` and `g * w` have all their coefficients in a subfield `k₀`, then so does `w`.
The proof uses a `k₀`-linear projection `k → k₀` applied coefficientwise. -/
theorem coeff_mem_of_mul_coeff_mem (k0 : Subfield k) {g w : MvPolynomial σ k} (hg0 : g ≠ 0)
    (hg : ∀ α, g.coeff α ∈ k0) (hgw : ∀ α, (g * w).coeff α ∈ k0) : ∀ α, w.coeff α ∈ k0 := by
  classical
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap k0 k)
    (LinearMap.ker_eq_bot.mpr (algebraMap k0 k).injective)
  have hπι : ∀ c : k0, π (c : k) = c := fun c ↦ LinearMap.congr_fun hπ c
  let proj : MvPolynomial σ k → MvPolynomial σ k := fun f ↦
    AddMonoidAlgebra.ofCoeff (Finsupp.mapRange (fun c ↦ ((π c : k0) : k)) (by simp) (AddMonoidAlgebra.coeff f))
  have hcoeff : ∀ f α, (proj f).coeff α = π (f.coeff α) := fun f α ↦ rfl
  have hmul : proj (g * w) = g * proj w := by
    ext α
    rw [hcoeff, coeff_mul, coeff_mul, map_sum, AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [hcoeff]
    have : g.coeff x.1 * w.coeff x.2 = (⟨g.coeff x.1, hg _⟩ : k0) • w.coeff x.2 := rfl
    rw [this, map_smul, smul_eq_mul, Subfield.coe_mul]
  have hfix : proj (g * w) = g * w := by
    ext α
    rw [hcoeff]
    exact congrArg Subtype.val (hπι ⟨_, hgw α⟩)
  have hw : proj w = w := mul_left_cancel₀ hg0 (hmul.symm.trans hfix)
  intro α
  rw [← hw, hcoeff]
  exact (π _).2


/-- Polynomials with coefficients in a subfield, as the range of the coefficient map. -/
theorem mem_range_map_subtype_iff (k0 : Subfield k) {f : MvPolynomial σ k} :
    f ∈ (MvPolynomial.map k0.subtype).range ↔ ∀ α, f.coeff α ∈ k0 := by
  classical
  rw [RingHom.mem_range, ← Set.mem_range, mem_range_map_iff_coeffs_subset]
  constructor
  · intro h α
    by_cases hα : f.coeff α = 0
    · rw [hα]; exact zero_mem _
    · obtain ⟨c, hc⟩ := h (coeff_mem_coeffs α hα)
      rw [← hc]; exact c.2
  · rintro h c hc
    obtain ⟨α, -, rfl⟩ := mem_coeffs_iff.mp hc
    exact ⟨⟨_, h α⟩, rfl⟩

variable (p e : ℕ) [ExpChar k p]

/-- If every `q`-th power lies in `k₀`, then every `q`-th power of a polynomial has its
coefficients in `k₀`. -/
theorem pow_mem_range_map_subtype (k0 : Subfield k) (hk0 : ∀ c : k, c ^ p ^ e ∈ k0)
    (f : MvPolynomial σ k) : f ^ p ^ e ∈ (MvPolynomial.map k0.subtype).range := by
  have : ExpChar (MvPolynomial σ k) p :=
    expChar_of_injective_algebraMap (MvPolynomial.C_injective σ k) p
  induction f using MvPolynomial.induction_on with
  | C a => exact ⟨C ⟨a ^ p ^ e, hk0 a⟩, by simp⟩
  | add f g hf hg => rw [add_pow_expChar_pow]; exact add_mem hf hg
  | mul_X f i hf => rw [mul_pow]; exact mul_mem hf (pow_mem (show X i ∈ (MvPolynomial.map k0.subtype).range from ⟨X i, by simp⟩) _)


/-- A polynomial with coefficients in `k₀` lies in the span, over the Frobenius image of the
polynomial ring, of the monomials `g X^γ` with `g` in a spanning set of `k₀` over `k ^ q` and all
exponents of `γ` less than `q`. -/
theorem mem_span_frobenius_monomials (k0 : Subfield k) (G : Finset k)
    (hG : ∀ c ∈ k0, c ∈ Submodule.span (iterateFrobenius k p e).fieldRange (G : Set k))
    {w : MvPolynomial σ k} (hw : ∀ α, w.coeff α ∈ k0) :
    w ∈ Submodule.span (iterateFrobenius (MvPolynomial σ k) p e).range
      ((fun x : k × (σ →₀ ℕ) ↦ monomial x.2 x.1) ''
        ((G : Set k) ×ˢ {γ : σ →₀ ℕ | ∀ i, γ i < p ^ e})) := by
  classical
  have hq : 0 < p ^ e := expChar_pow_pos k p e
  rw [w.as_sum]
  refine Submodule.sum_mem _ fun α _ ↦ ?_
  obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.mp (hG _ (hw α))
  rw [← hf, map_sum]
  refine Submodule.sum_mem _ fun g hg ↦ ?_
  obtain ⟨μ, hμ⟩ := RingHom.mem_fieldRange.mp (f g).2
  let β : σ →₀ ℕ := Finsupp.mapRange (· / p ^ e) (Nat.zero_div _) α
  let γ : σ →₀ ℕ := Finsupp.mapRange (· % p ^ e) (Nat.zero_mod _) α
  have hα : α = p ^ e • β + γ := by
    ext i; simp [β, γ, Nat.div_add_mod]
  have key : monomial α (f g • g) =
      iterateFrobenius (MvPolynomial σ k) p e (monomial β μ) * monomial γ g := by
    rw [iterateFrobenius_def, monomial_pow, monomial_mul, ← hα, Subfield.smul_def, smul_eq_mul,
      ← hμ, iterateFrobenius_def]
  rw [key]
  have hmem : monomial γ g ∈ (fun x : k × (σ →₀ ℕ) ↦ monomial x.2 x.1) ''
      ((G : Set k) ×ˢ {γ : σ →₀ ℕ | ∀ i, γ i < p ^ e}) :=
    ⟨(g, γ), ⟨hg, fun i ↦ by simpa [γ] using Nat.mod_lt _ hq⟩, rfl⟩
  exact Submodule.smul_mem _ (⟨_, monomial β μ, rfl⟩ :
    (iterateFrobenius (MvPolynomial σ k) p e).range) (Submodule.subset_span hmem)



end Coefficients

open IsLocalization

universe u v w x

/-- Over an arbitrary field `k`, the integral closure of `k[X₁, …, Xₙ]` in a finite extension of
its fraction field is a finite module. -/
theorem moduleFinite_integralClosure_mvPolynomial_of_field
    (k : Type u) [Field k] (n : ℕ)
    (F : Type v) (L : Type w) [Field F] [Field L]
    [Algebra (MvPolynomial (Fin n) k) F] [IsFractionRing (MvPolynomial (Fin n) k) F]
    [Algebra F L] [Algebra (MvPolynomial (Fin n) k) L]
    [IsScalarTower (MvPolynomial (Fin n) k) F L] [FiniteDimensional F L] :
    Module.Finite (MvPolynomial (Fin n) k) (integralClosure (MvPolynomial (Fin n) k) L) := by
  classical
  let P := MvPolynomial (Fin n) k
  let p := ringExpChar k
  have hkP : Function.Injective (algebraMap k P) := MvPolynomial.C_injective _ _
  have : ExpChar P p := expChar_of_injective_algebraMap hkP p
  have hPF : Function.Injective (algebraMap P F) := IsFractionRing.injective P F
  have : ExpChar F p := expChar_of_injective_algebraMap hPF p
  have : ExpChar L p := expChar_of_injective_algebraMap (algebraMap F L).injective p
  let M := separableClosure F L
  let _ : IsScalarTower P M L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let e := IsPurelyInseparable.exponent M L
  let Fr : L →ₛₗ[iterateFrobenius F p e] M :=
    IsPurelyInseparable.iterateFrobeniusₛₗ F M L p le_rfl
  have hFr : ∀ z, algebraMap M L (Fr z) = z ^ p ^ e := fun z ↦
    IsPurelyInseparable.algebraMap_iterateFrobeniusₛₗ F M L p le_rfl z
  have hFr_inj : Function.Injective Fr := by
    intro z₁ z₂ h
    apply iterateFrobenius_inj L p e
    rw [iterateFrobenius_def, iterateFrobenius_def, ← hFr, ← hFr, h]
  -- The separable part.
  let C := integralClosure P M
  have : Module.Finite P C := IsIntegralClosure.finite P F M C
  let r := Module.finrank F M
  let s := Module.finrank F L
  let mB : Module.Basis (Fin r) F M := Module.finBasis F M
  let bB : Module.Basis (Fin s) F L := Module.finBasis F L
  obtain ⟨SC, hSC⟩ := (Module.Finite.fg_top : (⊤ : Submodule P C).FG)
  obtain ⟨d, hd0⟩ := exist_integer_multiples (nonZeroDivisors P) (SC ×ˢ Finset.univ)
    (fun x : C × Fin r ↦ mB.repr (x.1 : M) x.2)
  have hd : ∀ c : C, ∀ l, IsInteger P ((d : P) • mB.repr (c : M) l) := by
    intro c l
    have hc : c ∈ Submodule.span P (SC : Set C) := hSC ▸ Submodule.mem_top
    induction hc using Submodule.span_induction with
    | mem c hc => exact hd0 (c, l) (Finset.mem_product.mpr ⟨hc, Finset.mem_univ _⟩)
    | zero => simpa using isInteger_zero
    | add c₁ c₂ _ _ h₁ h₂ =>
      simpa [smul_add] using isInteger_add h₁ h₂
    | smul a c _ h =>
      have : ((a • c : C) : M) = algebraMap P F a • (c : M) := by
        rw [Subalgebra.coe_smul, algebraMap_smul]
      rw [this, map_smul, Finsupp.smul_apply, smul_comm, algebraMap_smul]
      exact isInteger_smul h
  -- Denominators of the Frobenius images of the basis of `L`.
  let α : Fin s → Fin r → F := fun j l ↦ mB.repr (Fr (bB j)) l
  obtain ⟨b₀, hb₀⟩ := exist_integer_multiples (nonZeroDivisors P) Finset.univ
    (fun x : Fin s × Fin r ↦ α x.1 x.2)
  choose a ha using fun j l ↦ hb₀ (j, l) (Finset.mem_univ _)
  -- The finitely many coefficients that occur.
  let S : Finset k := (d : P).coeffs ∪ (b₀ : P).coeffs ∪
    Finset.univ.biUnion (fun x : Fin s × Fin r ↦ (a x.1 x.2).coeffs)
  let K₀ : Subfield k := (iterateFrobenius k p e).fieldRange
  let k₀' : IntermediateField K₀ k := IntermediateField.adjoin K₀ (S : Set k)
  let k₀ : Subfield k := k₀'.toSubfield
  have hk₀ : ∀ c : k, c ^ p ^ e ∈ k₀ := fun c ↦
    k₀'.algebraMap_mem ⟨c ^ p ^ e, c, rfl⟩
  have hSk₀ : ∀ c ∈ S, c ∈ k₀ := fun c hc ↦ IntermediateField.subset_adjoin K₀ _ hc
  have : FiniteDimensional K₀ k₀' := by
    refine IntermediateField.finiteDimensional_adjoin fun c _ ↦ ?_
    refine ⟨Polynomial.X ^ p ^ e - Polynomial.C ⟨c ^ p ^ e, c, rfl⟩,
      Polynomial.monic_X_pow_sub_C _ (expChar_pow_pos k p e).ne', ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, sub_eq_zero]
    rfl
  obtain ⟨G₀, hG₀⟩ := (Module.Finite.fg_top : (⊤ : Submodule K₀ k₀').FG)
  let G : Finset k := G₀.image (↑)
  have hG : ∀ c ∈ k₀, c ∈ Submodule.span K₀ (G : Set k) := by
    intro c hc
    have h1 : (⟨c, hc⟩ : k₀') ∈ Submodule.span K₀ (G₀ : Set k₀') := hG₀ ▸ Submodule.mem_top
    have h2 := Submodule.mem_map_of_mem (f := k₀'.val.toLinearMap) h1
    rw [Submodule.map_span] at h2
    simpa [G] using h2
  -- The Frobenius image of `P`.
  let R := (iterateFrobenius P p e).range
  have : IsNoetherianRing R := isNoetherianRing_of_ringEquiv P
    (RingEquiv.ofBijective (iterateFrobenius P p e).rangeRestrict
      ⟨fun x y h ↦ iterateFrobenius_inj P p e (congrArg Subtype.val h),
        (iterateFrobenius P p e).rangeRestrict_surjective⟩)
  have hFr_smul : ∀ (a : P) (z : L), Fr (a • z) =
      (⟨iterateFrobenius P p e a, a, rfl⟩ : R) • Fr z := by
    intro a z
    rw [← algebraMap_smul F a z, map_smulₛₗ]
    change _ = (iterateFrobenius P p e a) • Fr z
    rw [← algebraMap_smul F (iterateFrobenius P p e a) (Fr z)]
    congr 1
    simp only [iterateFrobenius_def, map_pow]
  -- The Frobenius image of the integral closure, as an `R`-module.
  let N : Submodule R M :=
    { carrier := Fr '' (integralClosure P L : Set L)
      zero_mem' := ⟨0, zero_mem _, map_zero Fr⟩
      add_mem' := by
        rintro _ _ ⟨z₁, h₁, rfl⟩ ⟨z₂, h₂, rfl⟩
        exact ⟨z₁ + z₂, add_mem h₁ h₂, map_add Fr z₁ z₂⟩
      smul_mem' := by
        rintro ⟨_, a, rfl⟩ _ ⟨z, hz, rfl⟩
        exact ⟨a • z, Subalgebra.smul_mem _ hz a, hFr_smul a z⟩ }
  -- A finitely generated `R`-module containing it.
  let Γ : Set (Fin n →₀ ℕ) := {γ | ∀ i, γ i < p ^ e}
  have hΓ : Γ.Finite := by
    refine (Set.finite_range (fun f : Fin n → Fin (p ^ e) ↦
      Finsupp.equivFunOnFinite.symm (fun i ↦ (f i : ℕ)))).subset ?_
    intro γ hγ
    exact ⟨fun i ↦ ⟨γ i, hγ i⟩, by ext i; simp⟩
  let T : Set M := (fun x : (k × (Fin n →₀ ℕ)) × Fin r ↦
    algebraMap P M (MvPolynomial.monomial x.1.2 x.1.1) *
      ((algebraMap P F (d : P))⁻¹ • mB x.2)) '' (((G : Set k) ×ˢ Γ) ×ˢ Set.univ)
  have hT : T.Finite := (((G.finite_toSet.prod hΓ).prod Set.finite_univ).image _)
  let R₀ := (MvPolynomial.map (σ := Fin n) k₀.subtype).range
  have hR₀ : ∀ f : P, f.coeffs ⊆ S → f ∈ R₀ := by
    intro f hf
    refine (mem_range_map_subtype_iff k₀).mpr fun β ↦ ?_
    by_cases hβ : f.coeff β = 0
    · rw [hβ]; exact zero_mem _
    · exact hSk₀ _ (hf (MvPolynomial.coeff_mem_coeffs β hβ))
  have hdR₀ : (d : P) ∈ R₀ := hR₀ _ fun c hc ↦ by simp [S, hc]
  have hb₀R₀ : (b₀ : P) ∈ R₀ := hR₀ _ fun c hc ↦ by simp [S, hc]
  have haR₀ : ∀ j l, a j l ∈ R₀ := fun j l ↦ hR₀ _ fun c hc ↦ by
    simp only [S, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact Or.inr ⟨(j, l), hc⟩
  have hNW : N ≤ Submodule.span R T := by
    rintro _ ⟨z, hz, rfl⟩
    have hint : Fr z ∈ C := by
      have h1 : IsIntegral P (algebraMap M L (Fr z)) := by
        rw [hFr]; exact (hz : IsIntegral P z).pow _
      exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom P M L)
        (algebraMap M L).injective).mp h1
    let f : Fin s → F := fun j ↦ bB.repr z j
    have hFrz : Fr z = ∑ j, f j ^ p ^ e • Fr (bB j) := by
      conv_lhs => rw [← bB.sum_repr z]
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [map_smulₛₗ, iterateFrobenius_def]
    have hcoord : ∀ l, mB.repr (Fr z) l = ∑ j, f j ^ p ^ e * α j l := by
      intro l
      rw [hFrz, map_sum, Finsupp.finsetSum_apply]
      simp [α]
    obtain ⟨v, hv⟩ := exist_integer_multiples (nonZeroDivisors P) Finset.univ f
    choose u hu using fun j ↦ hv j (Finset.mem_univ _)
    choose w hw using fun l ↦ hd ⟨Fr z, hint⟩ l
    have hdF : algebraMap P F (d : P) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
    have hwR₀ : ∀ l, w l ∈ R₀ := by
      intro l
      have hg0 : (b₀ : P) * (v : P) ^ p ^ e ≠ 0 :=
        mul_ne_zero (nonZeroDivisors.ne_zero b₀.2) (pow_ne_zero _ (nonZeroDivisors.ne_zero v.2))
      have heq : (b₀ : P) * (v : P) ^ p ^ e * w l = (d : P) * ∑ j, u j ^ p ^ e * a j l := by
        apply hPF
        simp only [map_mul, map_sum, map_pow, hw, hu, ha, hcoord, Algebra.smul_def,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        ring
      have hgR₀ : (b₀ : P) * (v : P) ^ p ^ e ∈ R₀ :=
        mul_mem hb₀R₀ (pow_mem_range_map_subtype p e k₀ hk₀ _)
      have hgwR₀ : (b₀ : P) * (v : P) ^ p ^ e * w l ∈ R₀ := by
        rw [heq]
        exact mul_mem hdR₀ (sum_mem fun j _ ↦
          mul_mem (pow_mem_range_map_subtype p e k₀ hk₀ _) (haR₀ j l))
      exact (mem_range_map_subtype_iff k₀).mpr (coeff_mem_of_mul_coeff_mem k₀ hg0
        ((mem_range_map_subtype_iff k₀).mp hgR₀) ((mem_range_map_subtype_iff k₀).mp hgwR₀))
    rw [← mB.sum_repr (Fr z)]
    refine Submodule.sum_mem _ fun l _ ↦ ?_
    have hterm : mB.repr (Fr z) l • mB l =
        algebraMap P M (w l) * ((algebraMap P F (d : P))⁻¹ • mB l) := by
      have : mB.repr (Fr z) l = (algebraMap P F (d : P))⁻¹ * algebraMap P F (w l) := by
        rw [hw, Algebra.smul_def, ← mul_assoc, inv_mul_cancel₀ hdF, one_mul]
      rw [this, mul_comm, mul_smul, algebraMap_smul, Algebra.smul_def]
    rw [hterm]
    have hspanw := mem_span_frobenius_monomials p e k₀ G hG
      ((mem_range_map_subtype_iff k₀).mp (hwR₀ l))
    suffices ∀ x ∈ Submodule.span R ((fun x : k × (Fin n →₀ ℕ) ↦ MvPolynomial.monomial x.2 x.1) ''
        ((G : Set k) ×ˢ Γ)),
        algebraMap P M x * ((algebraMap P F (d : P))⁻¹ • mB l) ∈ Submodule.span R T from
      this _ hspanw
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨g, γ⟩, hgγ, rfl⟩ := hx
      exact Submodule.subset_span ⟨((g, γ), l), ⟨hgγ, Set.mem_univ _⟩, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, add_mul]; exact add_mem hx hy
    | smul c x _ hx =>
      have : algebraMap P M (c • x) * ((algebraMap P F (d : P))⁻¹ • mB l) =
          c • (algebraMap P M x * ((algebraMap P F (d : P))⁻¹ • mB l)) := by
        rw [Algebra.smul_def c x, map_mul, mul_assoc, Algebra.smul_def c]
        rfl
      rw [this]
      exact Submodule.smul_mem _ c hx
  have hNfg : N.FG := Submodule.FG.of_le (Submodule.fg_span hT) hNW
  -- Pull back the generators.
  obtain ⟨Y, hY⟩ := hNfg
  have hYN : ∀ y ∈ Y, ∃ z ∈ integralClosure P L, Fr z = y := by
    intro y hy
    have hyN : y ∈ N := hY ▸ Submodule.subset_span hy
    obtain ⟨z, hz, h⟩ := hyN
    exact ⟨z, hz, h⟩
  choose zf hzf hFrzf using hYN
  let Z : Finset L := Y.attach.image fun y ↦ zf y.1 y.2
  have hspan : Subalgebra.toSubmodule (integralClosure P L) = Submodule.span P (Z : Set L) := by
    apply le_antisymm
    · intro z hz
      have hFz : Fr z ∈ Submodule.span R (Y : Set M) := hY ▸ ⟨z, hz, rfl⟩
      obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.mp hFz
      choose a ha using fun y : M ↦ (c y).2
      have : z = ∑ y ∈ Y.attach, a y.1 • zf y.1 y.2 := by
        apply hFr_inj
        rw [map_sum, ← hc, ← Finset.sum_attach]
        refine Finset.sum_congr rfl fun y _ ↦ ?_
        rw [hFr_smul, hFrzf]
        congr 1
        exact Subtype.ext (ha y.1).symm
      rw [this]
      refine Submodule.sum_mem _ fun y _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_attach _ _))
    · rw [Submodule.span_le]
      intro z hz
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hz
      exact hzf y.1 y.2
  exact Module.Finite.iff_fg.mpr (hspan ▸ Submodule.fg_span Z.finite_toSet)


/-- **General-field finiteness of integral closure.** Let `k` be an arbitrary field, `A` a
finitely generated `k`-algebra domain with fraction field `K`, and `L / K` a finite extension.
Then the integral closure of `A` in `L` is a finite `A`-module. -/
theorem moduleFinite_integralClosure_of_finiteType_of_field
    (k : Type u) [Field k]
    (A : Type v) [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A]
    (K : Type w) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type x) [Field L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [FiniteDimensional K L] :
    Module.Finite A (integralClosure A L) := by
  obtain ⟨n, g, hg, hfinite⟩ := exists_finite_inj_algHom_of_fg k A
  let P := MvPolynomial (Fin n) k
  let _ : Algebra P A := g.toRingHom.toAlgebra
  let _ : Module.Finite P A := hfinite
  let _ : FaithfulSMul P A :=
    (faithfulSMul_iff_algebraMap_injective P A).2 hg
  let _ : Algebra P K :=
    ((algebraMap A K).comp (algebraMap P A)).toAlgebra
  let _ : IsScalarTower P A K := IsScalarTower.of_algebraMap_eq' rfl
  let _ : FaithfulSMul P K := FaithfulSMul.trans P A K
  let _ : Algebra P L :=
    ((algebraMap A L).comp (algebraMap P A)).toAlgebra
  let _ : IsScalarTower P A L := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower P K L := IsScalarTower.to₁₃₄ P A K L
  let F := FractionRing P
  let _ : Algebra F K := FractionRing.liftAlgebra P K
  let _ : IsScalarTower P F K :=
    FractionRing.isScalarTower_liftAlgebra P K
  let _ : Algebra F L :=
    ((algebraMap K L).comp (algebraMap F K)).toAlgebra
  let _ : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower P F L := IsScalarTower.to₁₂₄ P F K L
  let _ : FaithfulSMul P (FractionRing A) :=
    FaithfulSMul.trans P A (FractionRing A)
  let _ : Algebra F (FractionRing A) :=
    FractionRing.liftAlgebra P (FractionRing A)
  let _ : IsScalarTower P F (FractionRing A) :=
    FractionRing.isScalarTower_liftAlgebra P (FractionRing A)
  let _ : FiniteDimensional F (FractionRing A) := inferInstance
  let eAK : FractionRing A ≃ₐ[A] K := FractionRing.algEquiv A K
  have hmaps :
      eAK.toRingEquiv.toRingHom.comp (algebraMap F (FractionRing A)) =
        algebraMap F K := by
    apply IsFractionRing.ringHom_ext (A := P)
    intro p
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [← IsScalarTower.algebraMap_apply P F (FractionRing A),
      IsScalarTower.algebraMap_apply P A (FractionRing A)]
    change eAK (algebraMap A (FractionRing A) (algebraMap P A p)) = _
    rw [eAK.commutes, ← IsScalarTower.algebraMap_apply P A K,
      ← IsScalarTower.algebraMap_apply P F K]
  let e : FractionRing A ≃ₐ[F] K :=
    { eAK.toRingEquiv with
      commutes' := fun z => DFunLike.congr_fun hmaps z }
  let _ : FiniteDimensional F K := Module.Finite.equiv e.toLinearEquiv
  let _ : FiniteDimensional F L := Module.Finite.trans K L
  let B := integralClosure P L
  let _ : Module.Finite P B :=
    moduleFinite_integralClosure_mvPolynomial_of_field k n F L
  let aToB : A →ₐ[P] B := IsIntegralClosure.lift P B L
  let _ : Algebra A B := aToB.toRingHom.toAlgebra
  let _ : IsScalarTower P A B :=
    IsScalarTower.of_algebraMap_eq fun p => (aToB.commutes p).symm
  let _ : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap A L a = algebraMap B L (aToB a)
    exact (IsIntegralClosure.algebraMap_lift P B L a).symm
  let _ : Module.Finite A B :=
    Module.Finite.of_restrictScalars_finite P A B
  let _ : IsIntegralClosure B A L :=
    IsIntegralClosure.tower_top (R := P)
  let eB : B ≃ₐ[A] integralClosure A L :=
    IsIntegralClosure.equiv (R := A) (A := B) (B := L)
      (integralClosure A L)
  exact Module.Finite.equiv eB.toLinearEquiv

end Hartshorne

/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Dimension.FgDomain
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# The incidence dimension count in a chart

Toward Hartshorne, *Algebraic Geometry*, II, Exercise 8.2 (p. 187).

Let `A` be a domain of finite type over a field `k` with `dim A ≤ n`. Consider a family of
elements `a_{j l} ∈ A` (`j ∈ κ`, `l ∈ ι`) such that the columns indexed by an embedding
`σ : κ ↪ ι` form the identity matrix, and suppose `n < #κ`. For `t ∈ k^ι` put
`g_j(t) = ∑_l t_l a_{j l}`. Geometrically, the `a_{j l}` are the coordinates of global sections
`v_l` in a local frame `(v_{σ j})_j` of a vector bundle on `Spec A`, and `g(t)` are the
coordinates of `∑_l t_l v_l`; the incidence `{(x, t) : g(t)(x) = 0}` has fibres of codimension
`#κ` over `Spec A`, so its image in `k^ι` is not dense.

* `Hartshorne.NowhereVanishingSection.exists_ne_zero_forall_span_eq_top`: there is a nonzero
  polynomial `P` on `k^ι` such that `g_1(t), …, g_r(t)` generate the unit ideal of `A` whenever
  `P(t) ≠ 0`.
* `Hartshorne.NowhereVanishingSection.exists_forall_eval_ne_zero`: over an infinite field,
  finitely many nonzero polynomials have a common non-root.

## Proof

The incidence is `Spec A[T_l : l ∈ ι] / (g_j(T))`, and solving the equations `g_j(T) = 0` for
the variables `T_{σ j}` identifies it with `Spec A[T_l : l ∉ σ(κ)]`, of dimension
`dim A + #ι - #κ < #ι`. Concretely, the substitution `T_{σ j} ↦ -∑_{l ∉ σ(κ)} a_{j l} T_l`
defines a `k`-algebra map `k[T_l : l ∈ ι] → A[T_l : l ∉ σ(κ)]`. Its target is a domain of finite
type over `k` whose transcendence degree is its dimension `dim A + #ι - #κ < #ι`, so the map is
not injective; let `P ≠ 0` lie in its kernel. If `P(t) ≠ 0` but the `g_j(t)` lie in a maximal
ideal `𝔪` of `A`, then evaluating the target at `T_l ↦ t_l` modulo `𝔪` gives a ring map whose
composite with the substitution is evaluation at `t`, so `P(t) = 0` in `A/𝔪`, a contradiction.
-/

noncomputable section

open MvPolynomial

namespace Hartshorne

namespace NowhereVanishingSection

universe u

variable {k : Type u} [Field k] {A : Type u} [CommRing A] [IsDomain A] [Algebra k A]
  [Algebra.FiniteType k A]

/-- Over a domain `A` of finite type over `k` with `dim A ≤ n`, a family of `m` elements of the
polynomial ring `A[x_f : f ∈ F]` with `n + #F < m` is algebraically dependent over `k`. -/
theorem not_algebraicIndependent_of_card_lt {ι F : Type} [Fintype ι] [Fintype F] {n : ℕ}
    (hA : ringKrullDim A ≤ n) (hcard : n + Fintype.card F < Fintype.card ι)
    (y : ι → MvPolynomial F A) : ¬ AlgebraicIndependent k y := by
  intro hy
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have : Algebra.FiniteType k (MvPolynomial F A) :=
    Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  obtain ⟨s, hs, htr⟩ :=
    exists_ringKrullDim_eq_trdeg k (MvPolynomial F A) (FractionRing (MvPolynomial F A))
  have hy' : AlgebraicIndependent k (algebraMap (MvPolynomial F A)
      (FractionRing (MvPolynomial F A)) ∘ y) :=
    hy.map' (f := IsScalarTower.toAlgHom k (MvPolynomial F A) (FractionRing (MvPolynomial F A)))
      (IsFractionRing.injective _ _)
  have h1 := hy'.lift_cardinalMk_le_trdeg
  rw [htr, Cardinal.mk_fintype, Cardinal.lift_natCast, Cardinal.lift_natCast] at h1
  have h1' : Fintype.card ι ≤ s := by exact_mod_cast h1
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, Nat.card_eq_fintype_card] at hs
  have h2 : ringKrullDim A + (Fintype.card F : WithBot ℕ∞) ≤
      ((n + Fintype.card F : ℕ) : WithBot ℕ∞) := by
    rw [Nat.cast_add]
    exact add_le_add_left hA _
  rw [hs] at h2
  have h3 : s ≤ n + Fintype.card F := by exact_mod_cast h2
  omega

variable {ι : Type} [Fintype ι] {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **The incidence dimension count in a chart.** Let `A` be a domain of finite type over `k`
with `dim A ≤ n`, and let `a : κ → ι → A` be a matrix whose columns `σ j` form the identity
matrix, where `n < #κ`. Then there is a nonzero polynomial `P` on `k^ι` such that for every
`t ∈ k^ι` with `P(t) ≠ 0`, the elements `∑_l t_l a_{j l}` (`j ∈ κ`) generate the unit ideal
of `A`. -/
theorem exists_ne_zero_forall_span_eq_top (σ : κ ↪ ι) (a : κ → ι → A)
    (ha : ∀ j j', a j (σ j') = if j = j' then 1 else 0) {n : ℕ} (hA : ringKrullDim A ≤ n)
    (hn : n < Fintype.card κ) :
    ∃ P : MvPolynomial ι k, P ≠ 0 ∧ ∀ t : ι → k, eval t P ≠ 0 →
      Ideal.span (Set.range fun j => ∑ l, algebraMap k A (t l) * a j l) = ⊤ := by
  classical
  let F := {l : ι // l ∉ Set.range σ}
  -- the substitution `T_{σ j} ↦ -∑_{l ∉ σ(κ)} a_{j l} T_l`
  let y : ι → MvPolynomial F A := fun l =>
    if h : l ∈ Set.range σ then -∑ f : F, C (a h.choose f.1) * X f else X ⟨l, h⟩
  have hcardF : Fintype.card F + Fintype.card κ = Fintype.card ι := by
    have h1 := Fintype.card_subtype_compl (fun l : ι => l ∈ Set.range σ)
    have h2 : Fintype.card {l : ι // l ∈ Set.range σ} = Fintype.card κ :=
      (Fintype.card_congr (Equiv.ofInjective σ σ.injective)).symm
    have h3 := Fintype.card_subtype_le (fun l : ι => l ∈ Set.range σ)
    change Fintype.card {l : ι // ¬ l ∈ Set.range σ} + _ = _
    rw [h1, h2]
    rw [h2] at h3
    omega
  have hdep : ¬ AlgebraicIndependent k y :=
    not_algebraicIndependent_of_card_lt hA (by omega) y
  rw [algebraicIndependent_iff_injective_aeval, injective_iff_map_eq_zero] at hdep
  push Not at hdep
  obtain ⟨P, hPy, hP⟩ := hdep
  refine ⟨P, hP, fun t ht => ?_⟩
  by_contra hspan
  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hspan
  let mk := Ideal.Quotient.mk 𝔪
  let τ : k →+* A ⧸ 𝔪 := mk.comp (algebraMap k A)
  let ψ : MvPolynomial F A →+* A ⧸ 𝔪 := eval₂Hom mk (fun f => τ (t f.1))
  -- the relation `t_{σ j} = -∑_{l ∉ σ(κ)} t_l a_{j l}` modulo `𝔪`
  have hrel : ∀ j, τ (t (σ j)) = -∑ f : F, mk (a j f.1) * τ (t f.1) := by
    intro j
    have hg : mk (∑ l, algebraMap k A (t l) * a j l) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.subset_span ⟨j, rfl⟩))
    have hsplit : ∑ l, algebraMap k A (t l) * a j l =
        algebraMap k A (t (σ j)) + ∑ f : F, algebraMap k A (t f.1) * a j f.1 := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun l => l ∈ Set.range σ)]
      congr 1
      · have hmap : Finset.univ.filter (fun l => l ∈ Set.range σ) = Finset.univ.map σ := by
          ext l
          simp
        rw [hmap, Finset.sum_map, Finset.sum_eq_single j]
        · simp [ha]
        · intro j' _ hne
          simp [ha, Ne.symm hne]
        · intro h
          exact absurd (Finset.mem_univ j) h
      · exact Finset.sum_subtype _ (fun l => by simp) _
    rw [hsplit, map_add, map_sum] at hg
    rw [eq_neg_iff_add_eq_zero, ← hg]
    congr 1
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [map_mul, mul_comm]
    rfl
  have hψy : ∀ l, ψ (y l) = τ (t l) := by
    intro l
    by_cases h : l ∈ Set.range σ
    · simp only [y, dif_pos h, map_neg, map_sum, map_mul, ψ, coe_eval₂Hom, eval₂_C, eval₂_X]
      conv_rhs => rw [← h.choose_spec]
      rw [hrel]
    · simp only [y, dif_neg h, ψ, coe_eval₂Hom, eval₂_X]
  have hcomp : ψ.comp (aeval y : MvPolynomial ι k →ₐ[k] MvPolynomial F A).toRingHom =
      τ.comp (eval t) := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun l => ?_)
    · simp [ψ, τ, mk]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X,
        eval_X]
      exact hψy l
  have h0 := congrArg (fun φ : MvPolynomial ι k →+* A ⧸ 𝔪 => φ P) hcomp
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hPy, map_zero] at h0
  exact ht (τ.injective (h0.symm.trans (map_zero τ).symm))

/-- Over an infinite field, finitely many nonzero polynomials have a common non-root. -/
theorem exists_forall_eval_ne_zero [Infinite k] {σ α : Type*} (s : Finset α)
    (P : α → MvPolynomial σ k) (hP : ∀ i ∈ s, P i ≠ 0) :
    ∃ t : σ → k, ∀ i ∈ s, eval t (P i) ≠ 0 := by
  by_contra h
  push Not at h
  have hprod : ∏ i ∈ s, P i ≠ 0 := Finset.prod_ne_zero_iff.mpr hP
  apply hprod
  refine MvPolynomial.funext fun t => ?_
  obtain ⟨i, hi, hti⟩ := h t
  rw [map_prod, map_zero]
  exact Finset.prod_eq_zero hi hti

end NowhereVanishingSection

end Hartshorne

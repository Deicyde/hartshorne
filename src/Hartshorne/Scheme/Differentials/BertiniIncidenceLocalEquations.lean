/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.Differentials.BertiniBadHyperplaneIncidence
import Hartshorne.Scheme.Differentials.BertiniJetFrame
import Hartshorne.Scheme.ProjectiveClosedImmersionChartCriterion
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Local equations for the bad hyperplanes

Let `k` be algebraically closed and let `X ⊆ ℙⁿ_k` be a nonsingular closed subvariety of
dimension `r`, embedded by `φ`. For a closed point `x`, the coefficient vectors `a ∈ kⁿ⁺¹` of the
hyperplanes `∑ aⱼ xⱼ = 0` which are bad at `x` form a subspace `K_x` of dimension `n - r`. We show
that these subspaces are cut out, locally on `X`, by `r + 1` linear forms whose coefficients are
regular functions: every closed point `x₀` has an affine neighbourhood `V` with functions
`μ ℓ j ∈ Γ(V, 𝒪_X)` (`ℓ ≤ r`, `j ≤ n`) such that some `(r + 1)`-minor of the matrix `(μ ℓ j)` is a
unit on `V`, and for every closed point `x ∈ V`,
`K_x = {a | ∑ⱼ aⱼ μ ℓ j (x) = 0 for all ℓ}`.

The proof works on an affine chart `U = X_{sᵢ}` with coordinate ring `A`, generated over `k` by
the ratios `fⱼ = sⱼ / sᵢ`. At a closed point `x ∈ U` with maximal ideal `𝔪 ⊆ A`, the vector `a`
lies in `K_x` iff `∑ aⱼ fⱼ ∈ 𝔪²`, and `A / 𝔪² ≅ 𝒪_{X,x} / 𝔪_x²` has dimension `r + 1`. A first
order Taylor expansion shows that the `fⱼ` span `A / 𝔪²`; choosing `r + 1` of them forming a
basis at `x₀`, the local frame of first-order jets (`exists_jet_frame`) provides the functions
`μ ℓ j`, and a dimension count gives the equality of subspaces.

## Main results

* `Hartshorne.BertiniIncidence.exists_jetFrame_incidence_equations`: the algebraic statement on a
  finitely generated `k`-algebra.
* `Hartshorne.BertiniIncidence.exists_local_incidence_equations`: the local equations for the bad
  hyperplanes.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
  IsLocalRing

namespace Hartshorne

universe u

namespace BertiniIncidence

/-! ### Algebra of first-order jets -/

section JetAlgebra

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]

/-- **First-order Taylor expansion.** If `A` is generated over `k` by the `fⱼ`, one of which is
`1`, then modulo `𝔪²` for the maximal ideal `𝔪` of a `k`-point, every element of `A` is a
`k`-linear combination of the `fⱼ`. -/
theorem incidence_exists_sub_sum_mem_ker_sq {ι : Type*} [Fintype ι] (f : ι → A) (i₀ : ι)
    (hone : f i₀ = 1) (hgen : Algebra.adjoin k (Set.range f) = ⊤) (ev : A →ₐ[k] k) (a : A) :
    ∃ c : ι → k, a - ∑ j, algebraMap k A (c j) * f j ∈ RingHom.ker ev ^ 2 := by
  classical
  let W : Submodule k A :=
    Submodule.span k (Set.range f) ⊔ (RingHom.ker ev ^ 2).restrictScalars k
  have h1 : (1 : A) ∈ W := Submodule.mem_sup_left (Submodule.subset_span ⟨i₀, hone⟩)
  have hker : ∀ x : A, x - algebraMap k A (ev x) ∈ RingHom.ker ev := fun x => by
    simp [RingHom.mem_ker]
  have hW : ∀ b : A, b ∈ W := by
    intro b
    have hb : b ∈ Algebra.adjoin k (Set.range f) := by rw [hgen]; trivial
    induction hb using Algebra.adjoin_induction with
    | mem x hx => exact Submodule.mem_sup_left (Submodule.subset_span hx)
    | algebraMap c =>
      rw [Algebra.algebraMap_eq_smul_one]
      exact W.smul_mem c h1
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy =>
      have key : x * y = (x - algebraMap k A (ev x)) * (y - algebraMap k A (ev y)) +
          ev x • y + ev y • x - (ev x * ev y) • (1 : A) := by
        simp only [Algebra.smul_def, map_mul]
        ring
      rw [key]
      refine sub_mem (add_mem (add_mem ?_ (W.smul_mem _ hy)) (W.smul_mem _ hx))
        (W.smul_mem _ h1)
      refine Submodule.mem_sup_right ?_
      rw [Submodule.restrictScalars_mem, pow_two]
      exact Ideal.mul_mem_mul (hker x) (hker y)
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 (hW a)
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 hu
  refine ⟨c, ?_⟩
  simp only [Algebra.smul_def] at huv
  rw [← huv, add_sub_cancel_left]
  exact hv

/-- **Local equations from a jet frame.** Let `A` be a finitely generated `k`-algebra and
`f₀, …, fₙ ∈ A` elements spanning `A / 𝔪₀²` over `k`, where `𝔪₀` is the maximal ideal of a
`k`-point `ev₀` and `dim_k A / 𝔪₀² = r + 1`. Then there are an injection `J` of `{0, …, r}` into
`{0, …, n}`, elements `μ ℓ j ∈ A` and `h ∈ A` such that `h · det (μ ℓ (J ℓ'))` does not vanish at
`ev₀`, and for every `k`-point `ev` with `h(ev) ≠ 0` and every `a ∈ kⁿ⁺¹`, if
`∑ⱼ aⱼ μ ℓ j (ev) = 0` for all `ℓ`, then `∑ⱼ aⱼ fⱼ ∈ (ker ev)²`. -/
theorem exists_jetFrame_incidence_equations [Algebra.FiniteType k A] {n r : ℕ}
    (f : Fin (n + 1) → A) (ev₀ : A →ₐ[k] k)
    (hf : ∀ a : A, ∃ c : Fin (n + 1) → k,
      a - ∑ j, algebraMap k A (c j) * f j ∈ RingHom.ker ev₀ ^ 2)
    (hdim : Module.finrank k (A ⧸ RingHom.ker ev₀ ^ 2) = r + 1) :
    ∃ (J : Fin (r + 1) ↪ Fin (n + 1)) (μ : Fin (r + 1) → Fin (n + 1) → A) (h : A),
      ev₀ (h * (Matrix.of fun ℓ ℓ' => μ ℓ (J ℓ')).det) ≠ 0 ∧
      ∀ ev : A →ₐ[k] k, ev h ≠ 0 → ∀ a : Fin (n + 1) → k,
        (∀ ℓ, ∑ j, a j * ev (μ ℓ j) = 0) →
          ∑ j, algebraMap k A (a j) * f j ∈ RingHom.ker ev ^ 2 := by
  classical
  set I := RingHom.ker ev₀ ^ 2 with hI
  let π : A →ₗ[k] A ⧸ I := (Ideal.Quotient.mkₐ k I).toLinearMap
  have hπ : ∀ (c : k) (b : A), π (algebraMap k A c * b) = c • π b := fun c b => by
    rw [← Algebra.smul_def, map_smul]
  have hπeq : ∀ b b' : A, π b = π b' ↔ b - b' ∈ I := fun b b' => Ideal.Quotient.eq
  let v : Fin (n + 1) → A ⧸ I := fun j => π (f j)
  have hspan : Submodule.span k (Set.range v) = ⊤ := by
    refine Submodule.eq_top_iff'.2 fun y => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨c, hc⟩ := hf a
    have : Ideal.Quotient.mk I a = ∑ j, c j • v j := by
      change π a = _
      rw [(hπeq _ _).2 hc, map_sum]
      exact Finset.sum_congr rfl fun j _ => hπ _ _
    rw [this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have : FiniteDimensional k (A ⧸ I) := Module.finite_of_finrank_eq_succ hdim
  obtain ⟨κ, b, hb, hbspan, hbli⟩ := exists_linearIndependent' k v
  have : Fintype κ := Fintype.ofInjective b hb
  have hcard : Fintype.card κ = r + 1 := by
    rw [← finrank_span_eq_card hbli, hbspan, hspan, finrank_top, hdim]
  let eκ : Fin (r + 1) ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  let J : Fin (r + 1) ↪ Fin (n + 1) := eκ.toEmbedding.trans ⟨b, hb⟩
  let g : Fin (r + 1) → A := fun ℓ => f (J ℓ)
  have hli : LinearIndependent k (fun ℓ => π (g ℓ)) := hbli.comp eκ eκ.injective
  have hgspan : Submodule.span k (Set.range fun ℓ => π (g ℓ)) = ⊤ := by
    have : (Set.range fun ℓ => π (g ℓ)) = Set.range (v ∘ b) :=
      (EquivLike.range_comp (v ∘ b) eκ)
    rw [this, hbspan, hspan]
  have hg : ∀ a : A, ∃ c : Fin (r + 1) → k,
      a - ∑ ℓ, algebraMap k A (c ℓ) * g ℓ ∈ RingHom.ker ev₀ ^ 2 := by
    intro a
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).1
      (hgspan ▸ Submodule.mem_top : π a ∈ Submodule.span k (Set.range fun ℓ => π (g ℓ)))
    refine ⟨c, (hπeq _ _).1 ?_⟩
    rw [map_sum, ← hc]
    exact Finset.sum_congr rfl fun ℓ _ => (hπ _ _).symm
  obtain ⟨h, hh0, hμ⟩ := exists_jet_frame ev₀ g hg
  choose μ' hμ' using hμ
  refine ⟨J, fun ℓ j => μ' (f j) ℓ, h, ?_, ?_⟩
  · -- at `ev₀`, the matrix `(μ ℓ (J ℓ'))` evaluates to `ev₀(h)` times the identity
    have hdiag : ∀ ℓ ℓ', ev₀ (μ' (f (J ℓ')) ℓ) = if ℓ = ℓ' then ev₀ h else 0 := by
      intro ℓ ℓ'
      have h0 : π (ev₀ h • g ℓ' - ∑ m, algebraMap k A (ev₀ (μ' (f (J ℓ')) m)) * g m) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 (hμ' (f (J ℓ')) ev₀)
      rw [map_sub, map_smul, map_sum] at h0
      simp only [hπ] at h0
      have := Fintype.linearIndependent_iff.1 hli
        (fun m => (if m = ℓ' then ev₀ h else 0) - ev₀ (μ' (f (J ℓ')) m)) ?_ ℓ
      · rw [sub_eq_zero] at this
        exact this.symm
      · simp only [sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul, Finset.sum_ite_eq',
          Finset.mem_univ, if_true]
        exact h0
    have hM : ev₀.mapMatrix (Matrix.of fun ℓ ℓ' => μ' (f (J ℓ')) ℓ) =
        Matrix.diagonal fun _ => ev₀ h := by
      ext ℓ ℓ'
      simp [Matrix.diagonal_apply, hdiag]
    rw [map_mul, AlgHom.map_det, hM, Matrix.det_diagonal, Finset.prod_const]
    exact mul_ne_zero hh0 (pow_ne_zero _ hh0)
  · intro ev hev a ha
    have hsum : ∑ j, algebraMap k A (a j) *
        (ev h • f j - ∑ ℓ, algebraMap k A (ev (μ' (f j) ℓ)) * g ℓ) ∈ RingHom.ker ev ^ 2 :=
      Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hμ' (f j) ev)
    have hid : ∑ j, algebraMap k A (a j) *
        (ev h • f j - ∑ ℓ, algebraMap k A (ev (μ' (f j) ℓ)) * g ℓ) =
        algebraMap k A (ev h) * ∑ j, algebraMap k A (a j) * f j -
          ∑ ℓ, algebraMap k A (∑ j, a j * ev (μ' (f j) ℓ)) * g ℓ := by
      simp only [Algebra.smul_def, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum,
        Finset.sum_mul, map_sum, map_mul]
      congr 1
      · exact Finset.sum_congr rfl fun j _ => by ring
      · rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun ℓ _ => Finset.sum_congr rfl fun j _ => by ring
    simp only [ha, map_zero, zero_mul, Finset.sum_const_zero, sub_zero] at hid
    rw [hid] at hsum
    have hX : ∑ j, algebraMap k A (a j) * f j = algebraMap k A (ev h)⁻¹ *
        (algebraMap k A (ev h) * ∑ j, algebraMap k A (a j) * f j) := by
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hev, map_one, one_mul]
    rw [hX]
    exact Ideal.mul_mem_left _ _ hsum

/-- The maximal ideal of a `k`-point is prime. -/
private instance incidence_isPrime_ker (ev : A →ₐ[k] k) : (RingHom.ker ev).IsPrime :=
  RingHom.ker_isPrime ev

/-- **Contraction of `𝔪²` from the local ring at a `k`-point.** If `S` is the localization of
`A` at the maximal ideal `𝔪 = ker ev` of a `k`-point, then `g ∈ A` maps into `(𝔪 S)²` iff
`g ∈ 𝔪²`. -/
theorem incidence_algebraMap_mem_maximalIdeal_sq_iff {S : Type*} [CommRing S] [IsLocalRing S]
    [Algebra A S] (ev : A →ₐ[k] k) [IsLocalization.AtPrime S (RingHom.ker ev)] (g : A) :
    algebraMap A S g ∈ maximalIdeal S ^ 2 ↔ g ∈ RingHom.ker ev ^ 2 := by
  set p := RingHom.ker ev with hp
  have hmap : Ideal.map (algebraMap A S) (p ^ 2) = maximalIdeal S ^ 2 := by
    rw [Ideal.map_pow, IsLocalization.AtPrime.map_eq_maximalIdeal]
  constructor
  · intro hg
    have hgp : g ∈ p := (IsLocalization.AtPrime.to_map_mem_maximal_iff S p g).1
      (Ideal.pow_le_self two_ne_zero hg)
    rw [← hmap, IsLocalization.mem_map_algebraMap_iff p.primeCompl S] at hg
    obtain ⟨⟨⟨b, hb⟩, u⟩, hbu⟩ := hg
    rw [← map_mul] at hbu
    obtain ⟨v, hv⟩ := (IsLocalization.eq_iff_exists p.primeCompl S).1 hbu
    have hwp : ((v : A) * u) ∉ p := (v * u).2
    have hwg : ((v : A) * u) * g ∈ p * p := by
      have : ((v : A) * u) * g = v * b := by rw [← hv]; ring
      rw [this, ← pow_two]
      exact Ideal.mul_mem_left _ _ hb
    have hc : ev ((v : A) * u) ≠ 0 := fun h => hwp h
    have hcg : algebraMap k A (ev ((v : A) * u)) * g ∈ p ^ 2 := by
      have : algebraMap k A (ev ((v : A) * u)) * g =
          ((v : A) * u) * g - ((v : A) * u - algebraMap k A (ev ((v : A) * u))) * g := by ring
      rw [this, pow_two]
      refine sub_mem hwg (Ideal.mul_mem_mul ?_ hgp)
      simp [hp, RingHom.mem_ker]
    have : g = algebraMap k A (ev ((v : A) * u))⁻¹ * (algebraMap k A (ev ((v : A) * u)) * g) := by
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
    rw [this]
    exact Ideal.mul_mem_left _ _ hcg
  · intro hg
    rw [← hmap]
    exact Ideal.mem_map_of_mem _ hg

/-- In the situation of `incidence_algebraMap_mem_maximalIdeal_sq_iff`, the map
`A → S / (𝔪 S)²` is surjective: an inverse `1/u` with `u(ev) = c ≠ 0` agrees modulo second order
terms with `c⁻¹ (2 - c⁻¹ u)`. -/
theorem incidence_surjective_quotient_maximalIdeal_sq {S : Type*} [CommRing S] [IsLocalRing S]
    [Algebra A S] (ev : A →ₐ[k] k) [IsLocalization.AtPrime S (RingHom.ker ev)] :
    Function.Surjective ((Ideal.Quotient.mk (maximalIdeal S ^ 2)).comp (algebraMap A S)) := by
  set p := RingHom.ker ev with hp
  intro y
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨⟨a, u⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl z
  have hc : ev u ≠ 0 := fun h => u.2 h
  set e := algebraMap k A (ev u)⁻¹ with he
  refine ⟨a * e * (2 - e * u), ?_⟩
  rw [RingHom.comp_apply, Ideal.Quotient.eq]
  have hspec := IsLocalization.mk'_spec S a u
  have ht : 1 - e * u ∈ p := by
    simp [hp, RingHom.mem_ker, he, inv_mul_cancel₀ hc]
  have hmem : (algebraMap A S (a * e * (2 - e * u)) - IsLocalization.mk' S a u) *
      algebraMap A S u ∈ maximalIdeal S ^ 2 := by
    have : (algebraMap A S (a * e * (2 - e * u)) - IsLocalization.mk' S a u) *
        algebraMap A S u = algebraMap A S (-(a * (1 - e * u) ^ 2)) := by
      rw [sub_mul, hspec, ← map_mul, ← map_sub]
      congr 1
      ring
    rw [this, incidence_algebraMap_mem_maximalIdeal_sq_iff ev]
    exact neg_mem (Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow ht 2))
  obtain ⟨w, hw⟩ := (IsLocalization.map_units S u).exists_right_inv
  have := Ideal.mul_mem_right w _ hmem
  rwa [mul_assoc, hw, mul_one] at this

/-- In the situation of `incidence_algebraMap_mem_maximalIdeal_sq_iff`, with `S` a
`k`-algebra compatibly with `A`, the `k`-algebras `A / 𝔪²` and `S / (𝔪 S)²` have the same
dimension. -/
theorem incidence_finrank_quotient_ker_sq_eq {S : Type*} [CommRing S] [IsLocalRing S]
    [Algebra A S] [Algebra k S] [IsScalarTower k A S] (ev : A →ₐ[k] k)
    [IsLocalization.AtPrime S (RingHom.ker ev)] :
    Module.finrank k (A ⧸ RingHom.ker ev ^ 2) = Module.finrank k (S ⧸ maximalIdeal S ^ 2) := by
  let ψ : A →ₐ[k] S ⧸ maximalIdeal S ^ 2 :=
    (Ideal.Quotient.mkₐ k _).comp (IsScalarTower.toAlgHom k A S)
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨g, hg⟩ := incidence_surjective_quotient_maximalIdeal_sq (S := S) ev y
    exact ⟨g, hg⟩
  have hker : RingHom.ker ψ = RingHom.ker ev ^ 2 := by
    ext g
    rw [RingHom.mem_ker, ← incidence_algebraMap_mem_maximalIdeal_sq_iff (S := S) ev]
    exact Ideal.Quotient.eq_zero_iff_mem
  exact ((Ideal.quotientEquivAlgOfEq k hker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective hψ)).toLinearEquiv.finrank_eq

end JetAlgebra

/-! ### Kernels of matrices with an invertible minor -/

section Minor

variable {k : Type*} [Field k]

/-- Let `m` be an `(r + 1) × (n + 1)` matrix over `k` with an invertible `(r + 1)`-minor, and let
`K ⊆ kⁿ⁺¹` be a subspace of dimension `n - r` containing the kernel of `m`. Then `K` is the kernel
of `m`. -/
theorem incidence_mem_iff_of_minor {n r : ℕ} (m : Fin (r + 1) → Fin (n + 1) → k)
    (J : Fin (r + 1) ↪ Fin (n + 1)) (hdet : (Matrix.of fun ℓ ℓ' => m ℓ (J ℓ')).det ≠ 0)
    (K : Submodule k (Fin (n + 1) → k)) (hK : Module.finrank k K = n - r)
    (hle : ∀ a : Fin (n + 1) → k, (∀ ℓ, ∑ j, a j * m ℓ j = 0) → a ∈ K)
    (a : Fin (n + 1) → k) :
    a ∈ K ↔ ∀ ℓ, ∑ j, a j * m ℓ j = 0 := by
  classical
  let M : Matrix (Fin (r + 1)) (Fin (n + 1)) k := Matrix.of m
  have hli : LinearIndependent k M.row := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hv : Matrix.vecMul c (Matrix.of fun ℓ ℓ' => m ℓ (J ℓ')) = 0 := by
      ext ℓ'
      have := congrFun hc (J ℓ')
      simpa [Matrix.vecMul, dotProduct, Finset.sum_apply, M, Matrix.row] using this
    intro ℓ
    exact congrFun (Matrix.eq_zero_of_vecMul_eq_zero hdet hv) ℓ
  have hrank : M.rank = r + 1 := by
    rw [Matrix.rank_eq_finrank_span_row, finrank_span_eq_card hli, Fintype.card_fin]
  let N := LinearMap.ker M.mulVecLin
  have hN : Module.finrank k N = n - r := by
    change Module.finrank k (LinearMap.ker M.mulVecLin) = n - r
    have := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    rw [Module.finrank_fin_fun] at this
    have h2 : Module.finrank k (LinearMap.range M.mulVecLin) = r + 1 := hrank
    omega
  have hmemN : ∀ b, b ∈ N ↔ ∀ ℓ, ∑ j, b j * m ℓ j = 0 := by
    intro b
    simp only [N, LinearMap.mem_ker, Matrix.mulVecLin_apply, funext_iff, Matrix.mulVec,
      dotProduct, M, Matrix.of_apply, Pi.zero_apply]
    exact forall_congr' fun ℓ => by simp only [mul_comm]
  have hNK : N ≤ K := fun b hb => hle b ((hmemN b).1 hb)
  have hNeq : N = K := Submodule.eq_of_le_of_finrank_eq hNK (by rw [hN, hK])
  rw [← hNeq, hmemN]

end Minor

/-! ### Closed points of an affine chart -/

section Chart

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- **Closed points of an affine open as `k`-points.** Let `X` be locally of finite type over an
algebraically closed field `k`, let `U ⊆ X` be an affine open whose ring of functions is a
`k`-algebra through the constants, and let `x ∈ U` be a closed point. Evaluation at `x` is a
`k`-point `ev` of `Γ(U, 𝒪_X)` whose kernel consists of the functions vanishing at `x`, the germ
at `x` of a function `g` lies in `𝔪_x²` iff `g ∈ (ker ev)²`, and
`dim_k Γ(U, 𝒪_X) / (ker ev)² = dim 𝔪_x/𝔪_x² + 1`. -/
theorem incidence_exists_kPoint_chart [IsAlgClosed k] (q : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType q] {U : X.Opens} (hU : IsAffineOpen U) [Algebra k Γ(X, U)]
    (halg : ∀ c, algebraMap k Γ(X, U) c = X.presheaf.map (homOfLE le_top).op (kConst q c))
    (x : X) (hx : x ∈ U) (hxc : IsClosed {x}) [IsNoetherianRing (X.presheaf.stalk x)] :
    ∃ ev : Γ(X, U) →ₐ[k] k,
      (∀ g, ev g = 0 ↔ X.presheaf.germ U x hx g ∈ maximalIdeal (X.presheaf.stalk x)) ∧
      (∀ g, X.presheaf.germ U x hx g ∈ maximalIdeal (X.presheaf.stalk x) ^ 2 ↔
        g ∈ RingHom.ker ev ^ 2) ∧
      Module.finrank k (Γ(X, U) ⧸ RingHom.ker ev ^ 2) =
        Module.finrank (ResidueField (X.presheaf.stalk x))
          (CotangentSpace (X.presheaf.stalk x)) + 1 := by
  have hbij := bijective_residue_kConstStalk q x hxc
  let eK := RingEquiv.ofBijective _ hbij
  have hres : ∀ c, X.presheaf.germ U x hx (algebraMap k Γ(X, U) c) = kConstStalk q x c := by
    intro c
    rw [halg]
    exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
  let evr : Γ(X, U) →+* k :=
    eK.symm.toRingHom.comp ((residue (X.presheaf.stalk x)).comp (X.presheaf.germ U x hx).hom)
  let ev : Γ(X, U) →ₐ[k] k :=
    { evr with
      commutes' := fun c => by
        change eK.symm (residue _ (X.presheaf.germ U x hx (algebraMap k Γ(X, U) c))) = c
        rw [RingEquiv.symm_apply_eq, hres]
        rfl }
  have hev : ∀ g, ev g = 0 ↔ X.presheaf.germ U x hx g ∈ maximalIdeal (X.presheaf.stalk x) := by
    intro g
    change eK.symm (residue _ (X.presheaf.germ U x hx g)) = 0 ↔ _
    rw [map_eq_zero_iff _ eK.symm.injective, residue_eq_zero_iff]
  let := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have hloc := hU.isLocalization_stalk ⟨x, hx⟩
  have hp : (hU.primeIdealOf ⟨x, hx⟩).asIdeal = RingHom.ker ev := by
    ext g
    rw [RingHom.mem_ker, hev,
      ← IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk x) _ g]
    rfl
  have htransfer : ∀ (P : Ideal Γ(X, U)) [P.IsPrime], P = RingHom.ker ev →
      IsLocalization.AtPrime (X.presheaf.stalk x) P →
        IsLocalization.AtPrime (X.presheaf.stalk x) (RingHom.ker ev) := by
    rintro P _ rfl h
    exact h
  have : IsLocalization.AtPrime (X.presheaf.stalk x) (RingHom.ker ev) := htransfer _ hp hloc
  let : Algebra k (X.presheaf.stalk x) := (kConstStalk q x).toAlgebra
  have : IsScalarTower k Γ(X, U) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq fun c => (hres c).symm
  refine ⟨ev, hev, fun g => incidence_algebraMap_mem_maximalIdeal_sq_iff ev g, ?_⟩
  rw [incidence_finrank_quotient_ker_sq_eq (S := X.presheaf.stalk x) ev]
  exact finrank_quotient_maximalIdeal_sq hbij

/-- **Bad sections on a chart.** On the chart `X_{sᵢ}` where `sᵢ` trivializes `L`, the section
`∑ aⱼ sⱼ` lies in `𝔪_x² L_x` iff the function `∑ aⱼ (sⱼ / sᵢ)` has germ in `𝔪_x²`. -/
theorem incidence_mem_badSubspace_iff_chart (q : X ⟶ Spec (CommRingCat.of k)) {L : X.Modules}
    (hL : L.IsInvertible) {n : ℕ} (s : Fin (n + 1) → Γ(L, ⊤)) (i : Fin (n + 1))
    [Algebra k Γ(X, nonvanishingLocusOpens hL (s i))]
    (halg : ∀ c, algebraMap k Γ(X, nonvanishingLocusOpens hL (s i)) c =
      X.presheaf.map (homOfLE le_top).op (kConst q c))
    (x : X) (hx : x ∈ nonvanishingLocusOpens hL (s i)) (a : Fin (n + 1) → k) :
    a ∈ badSubspace q s x ↔ X.presheaf.germ _ x hx
      (∑ j, algebraMap k _ (a j) * sectionRatio hL s i j) ∈
        maximalIdeal (X.presheaf.stalk x) ^ 2 := by
  rw [mem_badSubspace_iff]
  have hε := isTrivializingSection_nonvanishingLocusOpens hL (s i)
  have key : L.presheaf.map (homOfLE (le_top : nonvanishingLocusOpens hL (s i) ≤ ⊤)).op
      (linearSystemSection q s a) = (∑ j, algebraMap k _ (a j) * sectionRatio hL s i j) •
        L.presheaf.map (homOfLE le_top).op (s i) := by
    rw [linearSystemSection, map_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Scheme.Modules.map_smul, mul_smul, ← sectionRatio_spec, halg]
  have hgerm : L.presheaf.germ ⊤ x trivial (linearSystemSection q s a) =
      X.presheaf.germ _ x hx (∑ j, algebraMap k _ (a j) * sectionRatio hL s i j) •
        L.presheaf.germ _ x hx (L.presheaf.map (homOfLE le_top).op (s i)) := by
    rw [← germ_smul_module, ← key, TopCat.Presheaf.germ_res_apply]
  rw [hgerm]
  exact smul_germ_mem_smul_top_iff hε hx _ _

end Chart

/-! ### Local equations for the bad hyperplanes -/

section LocalEquations

variable {k : Type u} [Field k] {n : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ projectiveSpaceOverScheme n (Spec (CommRingCat.of k)))

/-- **Local equations for the bad hyperplanes.** Let `k` be algebraically closed and let
`φ : X ⟶ ℙⁿ_k` be a closed immersion of a nonsingular integral scheme of dimension `r`. Every
closed point `x₀` has an affine neighbourhood `V` carrying functions `μ ℓ j` (`ℓ ≤ r`, `j ≤ n`)
with an `(r + 1)`-minor `det (μ ℓ (J ℓ'))` invertible on `V`, such that at every closed point
`x ∈ V`, the hyperplane `∑ aⱼ xⱼ = 0` is bad at `x` (i.e. `a ∈ K_x`) iff the `r + 1` functions
`∑ⱼ aⱼ μ ℓ j` all vanish at `x`. -/
theorem exists_local_incidence_equations [IsAlgClosed k] [IsClosedImmersion φ] [IsIntegral X]
    (hX : X.IsRegular) {r : ℕ} (hr : topologicalKrullDim X = r) (x₀ : X) (hx₀ : IsClosed {x₀}) :
    ∃ (V : X.Opens) (_ : IsAffineOpen V) (_ : x₀ ∈ V)
      (μ : Fin (r + 1) → Fin (n + 1) → Γ(X, V)) (J : Fin (r + 1) ↪ Fin (n + 1)),
      IsUnit (Matrix.det (Matrix.of fun ℓ ℓ' => μ ℓ (J ℓ'))) ∧
      ∀ (x : X) (hx : x ∈ V), IsClosed {x} → ∀ a : Fin (n + 1) → k,
        (a ∈ badHyperplaneSubspace φ x ↔
          ∀ ℓ, X.presheaf.germ V x hx (∑ j, X.presheaf.map (homOfLE le_top).op
            (kConst (φ ≫ projectiveSpaceOverSchemeProjection n _) (a j)) * μ ℓ j) ∈
            IsLocalRing.maximalIdeal (X.presheaf.stalk x)) := by
  classical
  have : IsProper (projectiveSpaceOverSchemeProjection n (Spec (CommRingCat.of k))) :=
    projectiveSpaceOverSchemeProjection_isProper n _
  set q := φ ≫ projectiveSpaceOverSchemeProjection n (Spec (CommRingCat.of k)) with hq
  have hL := isInvertible_pullback_projectiveSpaceTwistingSheaf φ
  set s := pulledBackCoordinates φ with hs
  obtain ⟨i, hi⟩ := exists_mem_chartPreimage φ x₀
  set U := nonvanishingLocusOpens hL (s i) with hU_def
  have hx₀U : x₀ ∈ U := by
    rw [hU_def, ← preimage_projectiveSpaceChart_eq_nonvanishingLocusOpens hL s φ (Iso.refl _)
      (fun _ => rfl) i]
    exact hi
  obtain ⟨hU, hsurj⟩ :=
    (isClosedImmersion_iff_isAffineOpen_and_surjective_chartSectionPolynomialMap hL s q φ
      (Iso.refl _) (fun _ => rfl) rfl).1 inferInstance i
  let : Algebra k Γ(X, U) :=
    ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.comp (kConst q)).toAlgebra
  have halg : ∀ c, algebraMap k Γ(X, U) c = X.presheaf.map (homOfLE le_top).op (kConst q c) :=
    fun _ => rfl
  let f : Fin (n + 1) → Γ(X, U) := sectionRatio hL s i
  have hgen : Algebra.adjoin k (Set.range f) = ⊤ := by
    rw [Algebra.adjoin_range_eq_range_aeval, eq_top_iff]
    rintro g -
    obtain ⟨P, rfl⟩ := hsurj g
    refine (AlgHom.mem_range _).2
      ⟨MvPolynomial.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom P, ?_⟩
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map, chartSectionPolynomialMap,
      MvPolynomial.coe_eval₂Hom]
    congr 1
    ext b
    change X.presheaf.map _ (q.appTop ((Scheme.ΓSpecIso _).inv ((Scheme.ΓSpecIso _).hom b))) = _
    rw [Iso.hom_inv_id_apply]
    rfl
  have : Algebra.FiniteType k Γ(X, U) :=
    ⟨⟨Finset.univ.image f, by rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, hgen]⟩⟩
  have hpt : ∀ (x : X) (hx : x ∈ U), IsClosed {x} → ∃ ev : Γ(X, U) →ₐ[k] k,
      (∀ g, ev g = 0 ↔ X.presheaf.germ U x hx g ∈ maximalIdeal (X.presheaf.stalk x)) ∧
      (∀ g, X.presheaf.germ U x hx g ∈ maximalIdeal (X.presheaf.stalk x) ^ 2 ↔
        g ∈ RingHom.ker ev ^ 2) ∧
      Module.finrank k (Γ(X, U) ⧸ RingHom.ker ev ^ 2) = r + 1 := by
    intro x hx hxc
    have : IsRegularLocalRing (X.presheaf.stalk x) := hX.2 x
    obtain ⟨ev, h1, h2, h3⟩ := incidence_exists_kPoint_chart q hU halg x hx hxc
    refine ⟨ev, h1, h2, ?_⟩
    have hdim := dimension_at_closed_point q ⟨inferInstance, inferInstance⟩ x hxc
    rw [hr] at hdim
    have h := (IsRegularLocalRing.iff_finrank_cotangentSpace (X.presheaf.stalk x)).mp
      inferInstance
    rw [← hdim] at h
    have h' : Module.finrank (ResidueField (X.presheaf.stalk x))
        (CotangentSpace (X.presheaf.stalk x)) = r := by exact_mod_cast h
    rw [h3, h']
  obtain ⟨ev₀, hev₀, -, hdim₀⟩ := hpt x₀ hx₀U hx₀
  obtain ⟨J, μ, h, hh, hμ⟩ := exists_jetFrame_incidence_equations f ev₀
    (incidence_exists_sub_sum_mem_ker_sq f i (sectionRatio_self hL s i) hgen ev₀) hdim₀
  set D := h * (Matrix.of fun ℓ ℓ' => μ ℓ (J ℓ')).det with hD
  have hDunit : ∀ (x : X) (hxU : x ∈ U) (ev : Γ(X, U) →ₐ[k] k),
      (∀ g, ev g = 0 ↔ X.presheaf.germ U x hxU g ∈ maximalIdeal (X.presheaf.stalk x)) →
      (x ∈ X.basicOpen D ↔ ev D ≠ 0) := by
    intro x hxU ev hev
    rw [X.mem_basicOpen D x hxU, Ne, hev, notMem_maximalIdeal]
  refine ⟨X.basicOpen D, hU.basicOpen D, (hDunit x₀ hx₀U ev₀ hev₀).2 hh,
    fun ℓ j => X.presheaf.map (homOfLE (X.basicOpen_le D)).op (μ ℓ j), J, ?_, ?_⟩
  · have hdet : Matrix.det (Matrix.of fun ℓ ℓ' =>
        X.presheaf.map (homOfLE (X.basicOpen_le D)).op (μ ℓ (J ℓ'))) =
        X.presheaf.map (homOfLE (X.basicOpen_le D)).op (Matrix.of fun ℓ ℓ' => μ ℓ (J ℓ')).det := by
      rw [RingHom.map_det]
      rfl
    rw [hdet]
    have hu := X.toRingedSpace.isUnit_res_basicOpen D
    change IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le D)).op D) at hu
    rw [hD, map_mul] at hu
    exact isUnit_of_mul_isUnit_right hu
  · intro x hx hxc a
    have hxU : x ∈ U := X.basicOpen_le D hx
    obtain ⟨ev, hev, hsq, -⟩ := hpt x hxU hxc
    have hevD := (hDunit x hxU ev hev).1 hx
    rw [hD, map_mul] at hevD
    have hgerm : ∀ ℓ, X.presheaf.germ (X.basicOpen D) x hx
        (∑ j, X.presheaf.map (homOfLE le_top).op (kConst q (a j)) *
          X.presheaf.map (homOfLE (X.basicOpen_le D)).op (μ ℓ j)) =
        X.presheaf.germ U x hxU (∑ j, algebraMap k _ (a j) * μ ℓ j) := by
      intro ℓ
      simp only [map_sum, map_mul, TopCat.Presheaf.germ_res_apply, halg]
    simp_rw [hgerm, ← hev]
    simp only [map_sum, map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
    refine incidence_mem_iff_of_minor (fun ℓ j => ev (μ ℓ j)) J ?_ _
      (finrank_badHyperplaneSubspace φ hX hr x hxc) ?_ a
    · convert right_ne_zero_of_mul hevD using 1
      rw [AlgHom.map_det]
      rfl
    · intro b hb
      rw [badHyperplaneSubspace, incidence_mem_badSubspace_iff_chart q hL s i halg x hxU, hsq]
      exact hμ ev (left_ne_zero_of_mul hevD) b hb

end LocalEquations

end BertiniIncidence

end Hartshorne

/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.VeroneseProj
import Hartshorne.Scheme.GeneratedProjProjective

/-!
# The `d`-uple embedding through `Proj S ≅ Proj S^{(d)}`

Hartshorne, *Algebraic Geometry*, II, Exercise 5.13 (p. 126), and the `d`-uple embedding of
I, Exercise 2.12.

Let `S` be an `ℕ`-graded ring generated as an `S₀`-algebra by `x₀, …, xₙ ∈ S₁` (a polynomial
presentation `S₀[x₀, …, xₙ] → S`), and `d > 0`. Then the Veronese subring `S^{(d)}` is generated
as an `S^{(d)}_0 = S₀`-algebra by the monomials of degree `d` in the `xᵢ`, which lie in
`S^{(d)}_1 = S_d`. Hence these monomials define a closed immersion
`Proj S^{(d)} ⟶ ℙ^N_{Spec S₀}`, `N + 1` being the number of monomials of degree `d` in `n + 1`
variables, by sending the homogeneous coordinate `y_I` to the monomial `x^I`. Composed with the
isomorphism `Proj S ≅ Proj S^{(d)}`, this is the `d`-uple embedding `Proj S ⟶ ℙ^N`, a closed
immersion.

## Main definitions and results

* `Hartshorne.Veronese.adjoin_dupleCoords`: the degree-`d` monomials generate `S^{(d)}`.
* `Hartshorne.Veronese.dupleEmbedding`: the morphism `Proj S ⟶ ℙ^N_{Spec S₀}` given by the
  degree-`d` monomials, through `Proj S ≅ Proj S^{(d)}`.
* `Hartshorne.Veronese.isClosedImmersion_dupleEmbedding`: it is a closed immersion.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry DirectSum

universe u

namespace Hartshorne

namespace Veronese

/-- The multi-indices of total degree `d` in `n + 1` variables. -/
abbrev DupleIndex (n d : ℕ) := {m : Fin (n + 1) →₀ ℕ // m.degree = d}

instance (n d : ℕ) : Fintype (DupleIndex n d) :=
  (Finsupp.finite_of_degree_eq d).fintype

/-- `N` with `N + 1` the number of monomials of degree `d` in `n + 1` variables. -/
def dupleN (n d : ℕ) : ℕ :=
  Fintype.card (DupleIndex n d) - 1

theorem card_dupleIndex (n d : ℕ) : Fintype.card (DupleIndex n d) = dupleN n d + 1 := by
  have : 0 < Fintype.card (DupleIndex n d) :=
    Fintype.card_pos_iff.mpr ⟨⟨Finsupp.single 0 d, Finsupp.degree_single _ _⟩⟩
  rw [dupleN]
  omega

/-- An enumeration of the monomials of degree `d` in `n + 1` variables. -/
def dupleEquiv (n d : ℕ) : Fin (dupleN n d + 1) ≃ DupleIndex n d :=
  (Fintype.equivFinOfCardEq (card_dupleIndex n d)).symm

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {d : ℕ} [NeZero d] {n : ℕ} (x : Fin (n + 1) → A)

/-! ### Monomials -/

/-- The monomial `x^m = ∏ᵢ xᵢ^{mᵢ}`. -/
def monomialOf (m : Fin (n + 1) →₀ ℕ) : A :=
  m.prod fun i k => x i ^ k

theorem monomialOf_zero : monomialOf x 0 = 1 :=
  Finsupp.prod_zero_index

theorem monomialOf_add (m m' : Fin (n + 1) →₀ ℕ) :
    monomialOf x (m + m') = monomialOf x m * monomialOf x m' :=
  Finsupp.prod_add_index' (fun _ => pow_zero _) fun _ _ _ => pow_add _ _ _

omit [NeZero d] in
theorem monomialOf_mem (hx : ∀ i, x i ∈ 𝒜 1) (m : Fin (n + 1) →₀ ℕ) :
    monomialOf x m ∈ 𝒜 m.degree := by
  have := SetLike.prod_pow_mem_graded 𝒜 (F := m.support) (g := x) (i := fun _ => 1) m
    (fun j _ => hx j)
  rw [monomialOf, Finsupp.prod, Finsupp.degree_apply]
  simpa using this

/-- Below a multi-index of total degree at least `t` there is one of total degree `t`. -/
theorem exists_le_degree_eq (m : Fin (n + 1) →₀ ℕ) :
    ∀ t ≤ m.degree, ∃ m' ≤ m, m'.degree = t := by
  intro t
  induction t with
  | zero => exact fun _ => ⟨0, by simp, map_zero _⟩
  | succ t ih =>
    intro ht
    obtain ⟨m'', hle, hdeg⟩ := ih (Nat.le_of_succ_le ht)
    obtain ⟨i, hi⟩ : ∃ i, m'' i < m i := by
      by_contra! H
      have : m = m'' := le_antisymm (fun i => H i) hle
      subst this
      omega
    refine ⟨m'' + Finsupp.single i 1, fun j => ?_, by
      rw [map_add, Finsupp.degree_single, hdeg]⟩
    rcases eq_or_ne j i with rfl | hji
    · simpa using hi
    · simpa [Finsupp.single_apply, hji.symm] using hle j

/-! ### Generators of the Veronese subring -/

omit [NeZero d] in
theorem monomialOf_mem_veronese_one (hx : ∀ i, x i ∈ 𝒜 1) (m : DupleIndex n d) :
    monomialOf x m.1 ∈ 𝒜 (1 * d) := by
  have := monomialOf_mem x hx m.1
  rw [m.2] at this
  simpa using this

variable (d) in
/-- The degree-`d` monomials in the `xᵢ`, as elements of `S^{(d)}_1 = S_d`. -/
def dupleCoords (hx : ∀ i, x i ∈ 𝒜 1) (j : Fin (dupleN n d + 1)) : veroneseSubring 𝒜 d :=
  ofMem (monomialOf_mem_veronese_one x hx (dupleEquiv n d j))

omit [NeZero d] in
variable (d) in
theorem dupleCoords_mem (hx : ∀ i, x i ∈ 𝒜 1) (j : Fin (dupleN n d + 1)) :
    dupleCoords d x hx j ∈ veronese 𝒜 d 1 :=
  ofMem_mem _

omit [NeZero d] in
theorem monomialOf_mem_mul (hx : ∀ i, x i ∈ 𝒜 1) {k : ℕ} {m : Fin (n + 1) →₀ ℕ}
    (hm : m.degree = k * d) : monomialOf x m ∈ 𝒜 (k * d) :=
  hm ▸ monomialOf_mem x hx m

omit [NeZero d] in
theorem ofMem_monomialOf_mem_adjoin (hx : ∀ i, x i ∈ 𝒜 1) :
    ∀ (k : ℕ) (m : Fin (n + 1) →₀ ℕ) (hm : m.degree = k * d),
      ofMem (monomialOf_mem_mul x hx hm) ∈
        Algebra.adjoin ((veronese 𝒜 d) 0) (Set.range (dupleCoords d x hx)) := by
  intro k
  induction k with
  | zero =>
    intro m hm
    have hm0 : m = 0 := (Finsupp.degree_eq_zero_iff m).mp (by rw [hm, zero_mul])
    subst hm0
    convert Subalgebra.one_mem _
    exact Subtype.ext (monomialOf_zero x)
  | succ k ih =>
    intro m hm
    obtain ⟨m', hle, hdeg⟩ := exists_le_degree_eq m d (by rw [hm]; nlinarith)
    have hsplit : m = m' + (m - m') := (add_tsub_cancel_of_le hle).symm
    have hdeg' : (m - m').degree = k * d := by
      have := congrArg Finsupp.degree hsplit
      rw [map_add, hdeg, hm] at this
      linarith
    have heq : ofMem (monomialOf_mem_mul x hx hm) =
        dupleCoords d x hx ((dupleEquiv n d).symm ⟨m', hdeg⟩) *
          ofMem (monomialOf_mem_mul x hx hdeg') := by
      apply Subtype.ext
      simp only [dupleCoords, Subring.coe_mul, coe_ofMem, Equiv.apply_symm_apply]
      conv_lhs => rw [hsplit]
      exact monomialOf_add x m' (m - m')
    rw [heq]
    exact Subalgebra.mul_mem _ (Algebra.subset_adjoin ⟨_, rfl⟩) (ih _ hdeg')

variable (𝒜 d) in
/-- The degree-`kd` component of an element of `S`, as an element of `S^{(d)}_k`. -/
def componentHom (k : ℕ) : A →+ veroneseSubring 𝒜 d where
  toFun a := ofMem (𝒜 := 𝒜) (d := d) (n := k) (decompose 𝒜 a (k * d)).2
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

omit [NeZero d] in
theorem componentHom_apply (k : ℕ) (a : A) :
    (componentHom 𝒜 d k a : A) = (decompose 𝒜 a (k * d) : A) :=
  rfl

/-- **The degree-`d` monomials generate the Veronese subring**: if `S` is generated as an
`S₀`-algebra by `x₀, …, xₙ ∈ S₁`, then `S^{(d)}` is generated as an `S^{(d)}_0`-algebra by the
monomials of degree `d` in the `xᵢ`. -/
theorem adjoin_dupleCoords (hx : ∀ i, x i ∈ 𝒜 1)
    (hgen : Algebra.adjoin (𝒜 0) (Set.range x) = ⊤) :
    Algebra.adjoin ((veronese 𝒜 d) 0) (Set.range (dupleCoords d x hx)) = ⊤ := by
  classical
  set T := Algebra.adjoin ((veronese 𝒜 d) 0) (Set.range (dupleCoords d x hx))
  -- Every degree-`kd` component of every element of `S` lies in `T`.
  let T' : AddSubgroup A :=
    { carrier := {a | ∀ k, componentHom 𝒜 d k a ∈ T}
      zero_mem' := fun k => by rw [map_zero]; exact zero_mem T
      add_mem' := fun ha hb k => by rw [map_add]; exact add_mem (ha k) (hb k)
      neg_mem' := fun ha k => by rw [map_neg]; exact neg_mem (ha k) }
  have hmono : ∀ (c : 𝒜 0) (m : Fin (n + 1) →₀ ℕ),
      ((c : A) * monomialOf x m) ∈ T' := by
    intro c m k
    have hcm : (c : A) * monomialOf x m ∈ 𝒜 m.degree := by
      simpa using SetLike.mul_mem_graded c.2 (monomialOf_mem x hx m)
    by_cases hk : m.degree = k * d
    · have hc0 : (c : A) ∈ 𝒜 (0 * d) := by rw [zero_mul]; exact c.2
      have heq : componentHom 𝒜 d k ((c : A) * monomialOf x m) =
          algebraMap ((veronese 𝒜 d) 0) (veroneseSubring 𝒜 d) ⟨ofMem hc0, ofMem_mem hc0⟩ *
            ofMem (monomialOf_mem_mul x hx hk) := by
        apply Subtype.ext
        have hdec := decompose_of_mem_same 𝒜 hcm
        rw [hk] at hdec
        rw [componentHom_apply, hdec]
        rfl
      rw [heq]
      exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
        (ofMem_monomialOf_mem_adjoin x hx k m hk)
    · have heq : componentHom 𝒜 d k ((c : A) * monomialOf x m) = 0 := by
        apply Subtype.ext
        rw [componentHom_apply, decompose_of_mem_ne 𝒜 hcm hk]
        rfl
      rw [heq]
      exact zero_mem T
  have hall : ∀ a : A, a ∈ T' := by
    intro a
    have ha : a ∈ Algebra.adjoin (𝒜 0) (Set.range x) := hgen ▸ Algebra.mem_top
    rw [Algebra.adjoin_range_eq_range_aeval] at ha
    obtain ⟨p, rfl⟩ := ha
    rw [p.as_sum, map_sum]
    refine AddSubgroup.sum_mem _ fun m _ => ?_
    change MvPolynomial.aeval x (MvPolynomial.monomial m (p.coeff m)) ∈ T'
    rw [MvPolynomial.aeval_monomial]
    exact hmono _ m
  refine eq_top_iff.mpr fun r _ => ?_
  rw [← sum_support_decompose (veronese 𝒜 d) r]
  refine Subalgebra.sum_mem _ fun k _ => ?_
  have : (decompose (veronese 𝒜 d) r k : veroneseSubring 𝒜 d) = componentHom 𝒜 d k (r : A) :=
    Subtype.ext (coe_decompose r k)
  rw [this]
  exact hall _ k

/-! ### The `d`-uple embedding -/

variable (𝒜 d) in
/-- **The `d`-uple embedding** `Proj S ⟶ ℙ^N_{Spec S₀}` for `S` generated by `x₀, …, xₙ ∈ S₁`
over `S₀`: the isomorphism `Proj S ≅ Proj S^{(d)}` followed by the morphism
`Proj S^{(d)} ⟶ ℙ^N_{Spec S^{(d)}_0}` sending the homogeneous coordinate `y_I` to the
monomial `x^I` of degree `d` (here `S^{(d)}_0 = S₀`). -/
def dupleEmbedding (hx : ∀ i, x i ∈ 𝒜 1) (hgen : Algebra.adjoin (𝒜 0) (Set.range x) = ⊤) :
    Proj 𝒜 ⟶ projectiveSpaceOverScheme (dupleN n d) (Spec (.of ((veronese 𝒜 d) 0))) :=
  (projIso 𝒜 d).hom ≫
    GeneratedProj.toProjectiveSpace (veronese 𝒜 d) (dupleCoords_mem d x hx)
      (adjoin_dupleCoords x hx hgen)

/-- **The `d`-uple embedding is a closed immersion.** -/
theorem isClosedImmersion_dupleEmbedding (hx : ∀ i, x i ∈ 𝒜 1)
    (hgen : Algebra.adjoin (𝒜 0) (Set.range x) = ⊤) :
    IsClosedImmersion (dupleEmbedding 𝒜 d x hx hgen) := by
  have := GeneratedProj.isClosedImmersion_toProjectiveSpace (veronese 𝒜 d)
    (dupleCoords_mem d x hx) (adjoin_dupleCoords x hx hgen)
  rw [dupleEmbedding]
  infer_instance

end Veronese

end Hartshorne

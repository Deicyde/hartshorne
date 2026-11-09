/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.VeroneseProj
import Hartshorne.Scheme.GeneratedProjProjective
import Hartshorne.Scheme.RelativeSegre

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
* `Hartshorne.Veronese.map_comp_toProj`: `Proj S ≅ Proj S^{(d)}` is natural in `S`.
* `Hartshorne.Veronese.dupleMap`: the `d`-uple map `ρ_d : ℙⁿ_Y ⟶ ℙᴺ_Y` given by the
  degree-`d` monomials in `x₀, …, xₙ`, the base extension of `Hartshorne.Veronese.dupleMapInt`.
* `Hartshorne.Veronese.dupleEmbedding_eq_comp_dupleMap`: the `d`-uple embedding of `Proj S` is
  the closed immersion `Proj S ⟶ ℙⁿ_{Spec S₀}` given by `x₀, …, xₙ` followed by `ρ_d`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry DirectSum

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

/-! ### Functoriality of `Proj S ≅ Proj S^{(d)}` in `S` -/

section Functoriality

variable {B τ : Type u} [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {ℬ : ℕ → τ} [GradedRing ℬ]

omit [NeZero d] in
/-- A graded homomorphism `S → T` maps `S^{(d)}` into `T^{(d)}`. -/
theorem map_mem_veroneseSubring (φ : 𝒜 →+*ᵍ ℬ) {a : A} (ha : a ∈ veroneseSubring 𝒜 d) :
    φ a ∈ veroneseSubring ℬ d := by
  classical
  rw [← sum_support_decompose 𝒜 a, map_sum]
  refine sum_mem fun i _ => ?_
  by_cases hi : d ∣ i
  · exact mem_veroneseAddSubgroup_of_mem_of_dvd hi (φ.map_mem (decompose 𝒜 a i).2)
  · rw [ha i hi, map_zero]
    exact zero_mem _

variable (d) in
/-- The graded homomorphism `S^{(d)} → T^{(d)}` induced by a graded homomorphism `S → T`. -/
def veroneseMap (φ : 𝒜 →+*ᵍ ℬ) : veronese 𝒜 d →+*ᵍ veronese ℬ d where
  __ := φ.toRingHom.restrict (veroneseSubring 𝒜 d) (veroneseSubring ℬ d)
    fun _ ha => map_mem_veroneseSubring φ ha
  map_mem {i y} hy := by
    change φ (y : A) ∈ ℬ (i * d)
    exact φ.map_mem hy

omit [NeZero d] in
@[simp] theorem coe_veroneseMap_apply (φ : 𝒜 →+*ᵍ ℬ) (y : veroneseSubring 𝒜 d) :
    (veroneseMap d φ y : B) = φ (y : A) :=
  rfl

variable (d) in
/-- On the chart `D₊(g) ≅ Spec S^{(d)}_{(g)}` of `Proj S^{(d)}`, the inverse of
`Proj S ⟶ Proj S^{(d)}` is `Spec S^{(d)}_{(g)} ≅ Spec S_{(g)}` followed by the chart of `Proj S`. -/
theorem awayι_comp_inv_toProj {i : ℕ} (hi : 0 < i) {g : veroneseSubring 𝒜 d}
    (hg : g ∈ veronese 𝒜 d i) :
    Proj.awayι (veronese 𝒜 d) g hg hi ≫ inv (toProj (𝒜 := 𝒜) d) =
      Spec.map (CommRingCat.ofHom (awayEquiv hg).symm.toRingHom) ≫
        Proj.awayι 𝒜 (g : A) (mem_veronese_iff.mp hg) (Nat.mul_pos hi (NeZero.pos d)) := by
  rw [IsIso.comp_inv_eq, Category.assoc, awayι_comp_toProj d hi hg, ← Spec.map_comp_assoc]
  have : CommRingCat.ofHom (awayMap g) ≫ CommRingCat.ofHom (awayEquiv hg).symm.toRingHom =
      𝟙 _ :=
    CommRingCat.hom_ext (RingHom.ext fun z => (awayEquiv hg).symm_apply_apply z)
  rw [this, Spec.map_id, Category.id_comp]

variable (d) in
/-- **Naturality of `Proj S ≅ Proj S^{(d)}`**: for a graded homomorphism `φ : S → T` inducing
`Proj T ⟶ Proj S` and `Proj T^{(d)} ⟶ Proj S^{(d)}`, the square with the isomorphisms
`Proj T ≅ Proj T^{(d)}` and `Proj S ≅ Proj S^{(d)}` commutes. -/
theorem map_comp_toProj (φ : 𝒜 →+*ᵍ ℬ)
    (hφ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map φ)
    (hφd : HomogeneousIdeal.irrelevant (veronese ℬ d) ≤
      (HomogeneousIdeal.irrelevant (veronese 𝒜 d)).map (veroneseMap d φ)) :
    Proj.map φ hφ ≫ toProj d = toProj d ≫ Proj.map (veroneseMap d φ) hφd := by
  rw [← IsIso.inv_comp_eq]
  suffices key : ∀ (i : ℕ) (hi : 0 < i) (s : veroneseSubring 𝒜 d) (hs : s ∈ veronese 𝒜 d i),
      Proj.awayι (veronese ℬ d) (veroneseMap d φ s) ((veroneseMap d φ).map_mem hs) hi ≫
          inv (toProj d) ≫ Proj.map φ hφ ≫ toProj d =
        Proj.awayι (veronese ℬ d) (veroneseMap d φ s) ((veroneseMap d φ).map_mem hs) hi ≫
          Proj.map (veroneseMap d φ) hφd from
    (Proj.mapAffineOpenCover _ hφd).openCover.hom_ext _ _ fun s => key _ s.1.2 _ s.2.2
  intro i hi s hs
  have hg : veroneseMap d φ s ∈ veronese ℬ d i := (veroneseMap d φ).map_mem hs
  have hs' : (s : A) ∈ 𝒜 (i * d) := hs
  have hid : 0 < i * d := Nat.mul_pos hi (NeZero.pos d)
  rw [reassoc_of% awayι_comp_inv_toProj d hi hg, Proj.awayι_comp_map _ _ hi s hs]
  change _ ≫ (Proj.awayι ℬ (φ (s : A)) (φ.map_mem hs') hid ≫ Proj.map φ hφ) ≫ toProj d = _
  rw [Proj.awayι_comp_map _ _ hid _ hs', Category.assoc, awayι_comp_toProj d hi hs,
    ← Spec.map_comp_assoc]
  refine (Category.assoc _ _ _).symm.trans (congrArg (· ≫ Proj.awayι (veronese 𝒜 d) s hs hi)
    ((Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)))
  refine CommRingCat.hom_ext (RingHom.ext fun z => (awayEquiv hg).injective ?_)
  obtain ⟨k, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (veronese 𝒜 d) hs z
  change awayEquiv hg ((awayEquiv hg).symm (HomogeneousLocalization.Away.map φ (s : A)
      (awayMap s (HomogeneousLocalization.Away.mk (veronese 𝒜 d) hs k a ha)))) =
    awayEquiv hg (HomogeneousLocalization.Away.map (veroneseMap d φ) s
      (HomogeneousLocalization.Away.mk (veronese 𝒜 d) hs k a ha))
  refine ((awayEquiv hg).apply_symm_apply _).trans ?_
  rw [awayEquiv_apply, HomogeneousLocalization.Away.map_mk,
    awayMap_mk, awayMap_mk, HomogeneousLocalization.Away.map_mk]
  rfl

end Functoriality

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

/-! ### The `d`-uple map of projective space and the factorization of `dupleEmbedding` -/

section DupleMap

attribute [local instance] MvPolynomial.gradedAlgebra

variable (𝒜 d) in
/-- `S^{(d)}_0 = S_0`. -/
def zeroEquiv : (veronese 𝒜 d) 0 ≃+* 𝒜 0 where
  toFun r := ⟨(r : veroneseSubring 𝒜 d), by
    have h : ((r : veroneseSubring 𝒜 d) : A) ∈ 𝒜 (0 * d) := r.2
    rwa [zero_mul] at h⟩
  invFun a := ⟨ofMem (n := 0) (by rw [zero_mul]; exact a.2), ofMem_mem _⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- `Proj S ≅ Proj S^{(d)}` lies over `Spec S₀ = Spec S^{(d)}_0`. -/
theorem toProj_comp_toSpecZero :
    toProj d ≫ Proj.toSpecZero (veronese 𝒜 d) =
      Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (zeroEquiv 𝒜 d).toRingHom) := by
  rw [eq_comm, ← IsIso.inv_comp_eq]
  suffices key : ∀ (i : ℕ) (hi : 0 < i) (g : veroneseSubring 𝒜 d) (hg : g ∈ veronese 𝒜 d i),
      Proj.awayι (veronese 𝒜 d) g hg hi ≫ inv (toProj d) ≫ Proj.toSpecZero 𝒜 ≫
          Spec.map (CommRingCat.ofHom (zeroEquiv 𝒜 d).toRingHom) =
        Proj.awayι (veronese 𝒜 d) g hg hi ≫ Proj.toSpecZero (veronese 𝒜 d) from
    (Proj.affineOpenCover _).openCover.hom_ext _ _ fun s => key _ s.1.2 _ s.2.2
  intro i hi g hg
  rw [reassoc_of% awayι_comp_inv_toProj d hi hg, Proj.awayι_toSpecZero_assoc,
    Proj.awayι_toSpecZero, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun z => (awayEquiv hg).injective ?_)
  refine ((awayEquiv hg).apply_symm_apply _).trans ?_
  apply HomogeneousLocalization.val_injective
  rw [awayEquiv_apply, awayMap, val_hlMap]
  change (HomogeneousLocalization.mk _).val =
    IsLocalization.map _ _ _ (HomogeneousLocalization.mk _).val
  rw [HomogeneousLocalization.val_mk, HomogeneousLocalization.val_mk, Localization.mk_eq_mk',
    Localization.mk_eq_mk', IsLocalization.map_mk']
  rfl

omit [NeZero d] in
/-- A ring homomorphism maps the monomial `x^m` to the monomial `f(x)^m`. -/
theorem map_monomialOf {B : Type u} [CommRing B] (f : A →+* B) (m : Fin (n + 1) →₀ ℕ) :
    f (monomialOf x m) = monomialOf (f ∘ x) m := by
  rw [monomialOf, monomialOf, map_finsuppProd]
  simp [map_pow]

/-- The variables generate `ℤ[x₀, …, xₙ]` over its degree-zero part. -/
theorem adjoin_range_X_intGrading (n : ℕ) :
    Algebra.adjoin (GeneratedProj.intGrading.{u} n 0)
      (Set.range (MvPolynomial.X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ))) =
      ⊤ := by
  rw [eq_top_iff]
  rintro p -
  induction p using MvPolynomial.induction_on with
  | C a =>
    exact Subalgebra.algebraMap_mem _ (⟨MvPolynomial.C a,
      (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_C _ a)⟩ :
        GeneratedProj.intGrading.{u} n 0)
  | add p q hp hq => exact add_mem hp hq
  | mul_X p i hp => exact mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩)

variable (d n) in
/-- **The `d`-uple map of projective space over `ℤ`**, `ℙⁿ_ℤ ⟶ ℙᴺ_ℤ`: the isomorphism
`Proj ℤ[x₀, …, xₙ] ≅ Proj ℤ[x₀, …, xₙ]^{(d)}` followed by the morphism sending the homogeneous
coordinate `y_I` to the monomial `x^I` of degree `d`. -/
def dupleMapInt :
    projectiveSpaceScheme (ULift.{u} ℤ) n ⟶ projectiveSpaceScheme (ULift.{u} ℤ) (dupleN n d) :=
  toProj (𝒜 := GeneratedProj.intGrading.{u} n) d ≫
    GeneratedProj.toProjectiveSpaceInt (veronese (GeneratedProj.intGrading.{u} n) d)
      (dupleCoords_mem d MvPolynomial.X (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ)))
      (adjoin_dupleCoords MvPolynomial.X _ (adjoin_range_X_intGrading n))

variable (d n) in
/-- **The `d`-uple map of projective space** `ρ_d : ℙⁿ_Y ⟶ ℙᴺ_Y` over a scheme `Y`, given by
the monomials of degree `d` in `x₀, …, xₙ`: the base extension of `ℙⁿ_ℤ ⟶ ℙᴺ_ℤ` to `Y`. -/
def dupleMap (Y : Scheme.{u}) :
    projectiveSpaceOverScheme n Y ⟶ projectiveSpaceOverScheme (dupleN n d) Y :=
  pullback.map _ _ _ _ (dupleMapInt.{u} d n) (𝟙 Y) (𝟙 _)
    (specULiftZIsTerminal.{u}.hom_ext _ _) (by simp)

/-- Followed by the projection to `ℙᴺ_ℤ`, the `d`-uple map of `ℙⁿ_Y` is the projection to
`ℙⁿ_ℤ` followed by the `d`-uple map over `ℤ`. -/
@[reassoc (attr := simp)]
theorem dupleMap_fst (Y : Scheme.{u}) :
    dupleMap d n Y ≫ pullback.fst _ _ = pullback.fst _ _ ≫ dupleMapInt d n :=
  pullback.lift_fst _ _ _

/-- The `d`-uple map of `ℙⁿ_Y` is a morphism over `Y`. -/
@[reassoc (attr := simp)]
theorem dupleMap_projection (Y : Scheme.{u}) :
    dupleMap d n Y ≫ projectiveSpaceOverSchemeProjection (dupleN n d) Y =
      projectiveSpaceOverSchemeProjection n Y :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

omit [NeZero d] in
/-- The graded homomorphism `ℤ[x₀, …, xₙ] → S`, `xᵢ ↦ xᵢ`, maps the degree-`d` monomials in the
variables to the degree-`d` monomials in the `xᵢ`. -/
theorem veroneseMap_dupleCoords (hx : ∀ i, x i ∈ 𝒜 1) (j : Fin (dupleN n d + 1)) :
    veroneseMap d (GeneratedProj.evalGradedHom 𝒜 hx)
        (dupleCoords d MvPolynomial.X (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ)) j) =
      dupleCoords d x hx j := by
  apply Subtype.ext
  rw [coe_veroneseMap_apply]
  change GeneratedProj.evalRingHom x (monomialOf MvPolynomial.X _) = monomialOf x _
  rw [map_monomialOf]
  congr 1
  funext i
  exact GeneratedProj.evalRingHom_X x i

/-- The homomorphism `ℤ[y_I] → S^{(d)}`, `y_I ↦ x^I`, factors through `ℤ[x₀, …, xₙ]^{(d)}`. -/
theorem veroneseMap_comp_evalGradedHom (hx : ∀ i, x i ∈ 𝒜 1) :
    (veroneseMap d (GeneratedProj.evalGradedHom 𝒜 hx)).comp
        (GeneratedProj.evalGradedHom (veronese (GeneratedProj.intGrading.{u} n) d)
          (dupleCoords_mem d MvPolynomial.X (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ)))) =
      GeneratedProj.evalGradedHom (veronese 𝒜 d) (dupleCoords_mem d x hx) := by
  refine GradedRingHom.ext fun p => RingHom.congr_fun (MvPolynomial.ringHom_ext ?_ ?_) p
  · rintro ⟨k⟩
    have : (MvPolynomial.C (⟨k⟩ : ULift.{u} ℤ) :
        MvPolynomial (Fin (dupleN n d + 1)) (ULift.{u} ℤ)) = (k : MvPolynomial _ _) := by
      rw [← map_intCast (MvPolynomial.C (σ := Fin (dupleN n d + 1)) (R := ULift.{u} ℤ))]
      rfl
    rw [this, map_intCast, map_intCast]
  · intro j
    change veroneseMap d _ (GeneratedProj.evalRingHom _ (MvPolynomial.X j)) =
      GeneratedProj.evalRingHom _ (MvPolynomial.X j)
    rw [GeneratedProj.evalRingHom_X, GeneratedProj.evalRingHom_X, veroneseMap_dupleCoords]

/-- **The `d`-uple embedding factors through the `d`-uple map of projective space.** For `S`
generated over `S₀` by `x₀, …, xₙ ∈ S₁`, the morphism `Proj S ⟶ ℙᴺ` given by the degree-`d`
monomials through `Proj S ≅ Proj S^{(d)}` is the closed immersion `Proj S ⟶ ℙⁿ_{Spec S₀}` given by
`x₀, …, xₙ`, followed by the `d`-uple map `ρ_d : ℙⁿ_{Spec S₀} ⟶ ℙᴺ_{Spec S₀}` (and the
identification `S₀ = S^{(d)}_0` of base rings). -/
theorem dupleEmbedding_eq_comp_dupleMap (hx : ∀ i, x i ∈ 𝒜 1)
    (hgen : Algebra.adjoin (𝒜 0) (Set.range x) = ⊤) :
    dupleEmbedding 𝒜 d x hx hgen =
      GeneratedProj.toProjectiveSpace 𝒜 hx hgen ≫ dupleMap d n (Spec (.of (𝒜 0))) ≫
        projectiveSpaceOverSchemeMap (dupleN n d)
          (Spec.map (CommRingCat.ofHom (zeroEquiv 𝒜 d).toRingHom)) := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, projectiveSpaceOverSchemeMap_fst, dupleMap_fst,
      ← Category.assoc, GeneratedProj.toProjectiveSpace_fst, dupleEmbedding, Category.assoc,
      GeneratedProj.toProjectiveSpace_fst, projIso_hom, dupleMapInt]
    let ψ := GeneratedProj.evalGradedHom 𝒜 hx
    have hψd : HomogeneousIdeal.irrelevant (veronese 𝒜 d) ≤
        (HomogeneousIdeal.irrelevant (veronese (GeneratedProj.intGrading.{u} n) d)).map
          (veroneseMap d ψ) := by
      rw [← toIdeal_le_toIdeal_iff, HomogeneousIdeal.toIdeal_map]
      refine (GeneratedProj.irrelevant_le_span_of_adjoin_eq_top (veronese 𝒜 d)
        (dupleCoords d x hx) (fun j => ⟨1, dupleCoords_mem d x hx j⟩)
        (adjoin_dupleCoords x hx hgen)).trans ?_
      rw [Ideal.span_le, Set.range_subset_iff]
      intro j
      rw [← veroneseMap_dupleCoords x hx j]
      exact Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem _ Nat.one_pos
        (dupleCoords_mem d _ (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ)) j))
    let evZ := GeneratedProj.evalGradedHom (veronese (GeneratedProj.intGrading.{u} n) d)
      (dupleCoords_mem d _ (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ)))
    let evS := GeneratedProj.evalGradedHom (veronese 𝒜 d) (dupleCoords_mem d x hx)
    have hZ : HomogeneousIdeal.irrelevant (veronese (GeneratedProj.intGrading.{u} n) d) ≤
        (HomogeneousIdeal.irrelevant (GeneratedProj.intGrading.{u} (dupleN n d))).map evZ :=
      GeneratedProj.irrelevant_le_map_evalGradedHom
      (veronese (GeneratedProj.intGrading.{u} n) d)
      (dupleCoords_mem d _ (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ)))
      (adjoin_dupleCoords _ (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ))
        (adjoin_range_X_intGrading n))
    have hS : HomogeneousIdeal.irrelevant (veronese 𝒜 d) ≤
        (HomogeneousIdeal.irrelevant (GeneratedProj.intGrading.{u} (dupleN n d))).map evS :=
      GeneratedProj.irrelevant_le_map_evalGradedHom (veronese 𝒜 d)
      (dupleCoords_mem d x hx) (adjoin_dupleCoords x hx hgen)
    have hψ : HomogeneousIdeal.irrelevant 𝒜 ≤
        (HomogeneousIdeal.irrelevant (GeneratedProj.intGrading.{u} n)).map ψ :=
      GeneratedProj.irrelevant_le_map_evalGradedHom 𝒜 hx hgen
    have e1 : Proj.map evS hS = Proj.map (veroneseMap d ψ) hψd ≫ Proj.map evZ hZ := by
      rw [← Proj.map_comp]
      congr 1
      exact (veroneseMap_comp_evalGradedHom x hx).symm
    exact (congrArg (toProj d ≫ ·) e1).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ Proj.map evZ hZ) (map_comp_toProj d ψ hψ hψd).symm).trans
        (Category.assoc _ _ _)))
  · change _ ≫ projectiveSpaceOverSchemeProjection _ _ = _ ≫ projectiveSpaceOverSchemeProjection _ _
    rw [Category.assoc, Category.assoc, projectiveSpaceOverSchemeMap_projection,
      dupleMap_projection_assoc, ← Category.assoc,
      GeneratedProj.toProjectiveSpace_projection, dupleEmbedding, projIso_hom, Category.assoc,
      GeneratedProj.toProjectiveSpace_projection, toProj_comp_toSpecZero]

end DupleMap

end Veronese

end Hartshorne

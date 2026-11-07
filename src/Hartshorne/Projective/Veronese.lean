/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# The Veronese subring `S^{(d)}`

Hartshorne, *Algebraic Geometry*, II, Exercise 5.13 (p. 126).

Let `S` be an `ℕ`-graded ring and `d > 0`. The Veronese subring `S^{(d)} = ⊕_n S_{nd}` is the
subring of `S` of elements whose homogeneous components vanish in degrees not divisible by `d`,
graded by `S^{(d)}_n = S_{nd}`.

For a homogeneous `g ∈ S^{(d)}_n` the degree-zero localizations agree: the inclusion
`S^{(d)} → S` induces an isomorphism `S^{(d)}_{(g)} ≅ S_{(g)}`, since a fraction `a / g^k` of
degree zero in `S_g` has numerator `a ∈ S_{knd} = S^{(d)}_{kn}`.

## Main definitions and results

* `Hartshorne.veroneseSubring 𝒜 d`: the Veronese subring `S^{(d)}`.
* `Hartshorne.veronese 𝒜 d`: its grading `n ↦ S_{nd}`; a `GradedRing` for `d ≠ 0`.
* `Hartshorne.Veronese.coe_decompose`: the degree-`n` component of `x ∈ S^{(d)}` is the
  degree-`nd` component of `x` in `S`.
* `Hartshorne.Veronese.hlMap`: the map of homogeneous localizations induced by the inclusion.
* `Hartshorne.Veronese.awayEquiv`: `S^{(d)}_{(g)} ≅ S_{(g)}` for homogeneous `g ∈ S^{(d)}`.
-/

universe u

noncomputable section

namespace Hartshorne

open DirectSum HomogeneousLocalization

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ)

/-- The additive subgroup of `S` of elements whose homogeneous components vanish in degrees not
divisible by `d`. -/
def veroneseAddSubgroup : AddSubgroup A where
  carrier := {a | ∀ i, ¬ d ∣ i → (decompose 𝒜 a i : A) = 0}
  zero_mem' i _ := by simp
  add_mem' {a b} ha hb i hi := by simp [ha i hi, hb i hi]
  neg_mem' {a} ha i hi := by
    rw [decompose_neg, DFinsupp.neg_apply, NegMemClass.coe_neg, ha i hi, neg_zero]

namespace Veronese

variable {𝒜 d}

theorem mem_veroneseAddSubgroup_of_mem {n : ℕ} {a : A} (ha : a ∈ 𝒜 (n * d)) :
    a ∈ veroneseAddSubgroup 𝒜 d := by
  intro i hi
  exact decompose_of_mem_ne 𝒜 ha fun h => hi (h ▸ Dvd.intro_left n rfl)

theorem mem_veroneseAddSubgroup_of_mem_of_dvd {i : ℕ} (hi : d ∣ i) {a : A} (ha : a ∈ 𝒜 i) :
    a ∈ veroneseAddSubgroup 𝒜 d := by
  obtain ⟨k, rfl⟩ := hi
  exact mem_veroneseAddSubgroup_of_mem (n := k) (by rwa [mul_comm])

theorem mul_mem_veroneseAddSubgroup {a b : A} (ha : a ∈ veroneseAddSubgroup 𝒜 d)
    (hb : b ∈ veroneseAddSubgroup 𝒜 d) : a * b ∈ veroneseAddSubgroup 𝒜 d := by
  classical
  rw [← sum_support_decompose 𝒜 a, ← sum_support_decompose 𝒜 b, Finset.sum_mul_sum]
  refine AddSubgroup.sum_mem _ fun i _ => AddSubgroup.sum_mem _ fun j _ => ?_
  by_cases hi : d ∣ i
  · by_cases hj : d ∣ j
    · exact mem_veroneseAddSubgroup_of_mem_of_dvd (dvd_add hi hj)
        (SetLike.mul_mem_graded (decompose 𝒜 a i).2 (decompose 𝒜 b j).2)
    · rw [hb j hj, mul_zero]
      exact zero_mem _
  · rw [ha i hi, zero_mul]
    exact zero_mem _

end Veronese

/-- **The Veronese subring** `S^{(d)} = ⊕_n S_{nd}` of a graded ring `S`: the elements whose
homogeneous components vanish in degrees not divisible by `d`. -/
def veroneseSubring : Subring A where
  __ := veroneseAddSubgroup 𝒜 d
  one_mem' := Veronese.mem_veroneseAddSubgroup_of_mem (n := 0) (by
    simpa using SetLike.one_mem_graded 𝒜)
  mul_mem' := Veronese.mul_mem_veroneseAddSubgroup

/-- The grading `S^{(d)}_n = S_{nd}` of the Veronese subring. -/
def veronese (n : ℕ) : AddSubgroup (veroneseSubring 𝒜 d) where
  carrier := {x | (x : A) ∈ 𝒜 (n * d)}
  zero_mem' := zero_mem (𝒜 (n * d))
  add_mem' ha hb := add_mem (S := σ) ha hb
  neg_mem' ha := neg_mem (G := A) (S := σ) ha

namespace Veronese

variable {𝒜 d}

theorem mem_veronese_iff {n : ℕ} {x : veroneseSubring 𝒜 d} :
    x ∈ veronese 𝒜 d n ↔ (x : A) ∈ 𝒜 (n * d) :=
  Iff.rfl

theorem mem_veroneseSubring_of_mem {n : ℕ} {a : A} (ha : a ∈ 𝒜 (n * d)) :
    a ∈ veroneseSubring 𝒜 d :=
  mem_veroneseAddSubgroup_of_mem ha

theorem mem_veroneseSubring_iff {a : A} :
    a ∈ veroneseSubring 𝒜 d ↔ ∀ i, ¬ d ∣ i → (decompose 𝒜 a i : A) = 0 :=
  Iff.rfl

/-- The element `a ∈ S_{nd}` as an element of `S^{(d)}_n`. -/
def ofMem {n : ℕ} {a : A} (ha : a ∈ 𝒜 (n * d)) : veroneseSubring 𝒜 d :=
  ⟨a, mem_veroneseSubring_of_mem ha⟩

@[simp] theorem coe_ofMem {n : ℕ} {a : A} (ha : a ∈ 𝒜 (n * d)) : (ofMem ha : A) = a :=
  rfl

theorem ofMem_mem {n : ℕ} {a : A} (ha : a ∈ 𝒜 (n * d)) : ofMem ha ∈ veronese 𝒜 d n :=
  ha

instance gradedMonoid : SetLike.GradedMonoid (veronese 𝒜 d) where
  one_mem := by
    change (1 : A) ∈ 𝒜 (0 * d)
    simpa using SetLike.one_mem_graded 𝒜
  mul_mem i j x y hx hy := by
    change (x : A) * y ∈ 𝒜 ((i + j) * d)
    rw [add_mul]
    exact SetLike.mul_mem_graded hx hy

theorem decompose_coeAddMonoidHom [NeZero d] (y : ⨁ n, veronese 𝒜 d n) (n : ℕ) :
    (decompose 𝒜 ((DirectSum.coeAddMonoidHom (veronese 𝒜 d) y : veroneseSubring 𝒜 d) : A) (n * d) : A) =
      ((y n : veroneseSubring 𝒜 d) : A) := by
  classical
  induction y using DirectSum.induction_on with
  | zero => simp
  | of m v =>
    rw [coeAddMonoidHom_of]
    by_cases hmn : m = n
    · subst hmn
      rw [of_eq_same]
      exact decompose_of_mem_same 𝒜 v.2
    · rw [of_eq_of_ne _ _ _ (Ne.symm hmn)]
      refine (decompose_of_mem_ne 𝒜 v.2 ?_).trans rfl
      exact fun h => hmn (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (NeZero.ne d)) h)
  | add y z hy hz =>
    simp only [map_add, decompose_add, add_apply, AddMemClass.coe_add, hy, hz]

theorem isInternal [NeZero d] : DirectSum.IsInternal (veronese 𝒜 d) := by
  classical
  constructor
  · rw [injective_iff_map_eq_zero]
    intro y hy
    ext n
    have := decompose_coeAddMonoidHom y n
    rw [hy] at this
    simpa using this.symm
  · intro x
    refine ⟨∑ i ∈ (decompose 𝒜 (x : A)).support, DirectSum.of (fun n => veronese 𝒜 d n) (i / d)
      ⟨ofMem (decompose 𝒜 (x : A) (i / d * d)).2, ofMem_mem _⟩, ?_⟩
    apply Subtype.ext
    rw [map_sum]
    simp only [coeAddMonoidHom_of]
    push_cast
    conv_rhs => rw [← sum_support_decompose 𝒜 (x : A)]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hdi : d ∣ i := by
      by_contra h
      exact (DFinsupp.mem_support_iff.mp hi) (Subtype.ext (x.2 i h))
    rw [coe_ofMem, Nat.div_mul_cancel hdi]

instance decomposition [NeZero d] : DirectSum.Decomposition (veronese 𝒜 d) :=
  isInternal.chooseDecomposition _

instance gradedRing [NeZero d] : GradedRing (veronese 𝒜 d) where

/-- **The homogeneous components of `S^{(d)}`**: the degree-`n` component of `x ∈ S^{(d)}` is the
degree-`nd` component of `x` in `S`. -/
theorem coe_decompose [NeZero d] (x : veroneseSubring 𝒜 d) (n : ℕ) :
    ((decompose (veronese 𝒜 d) x n : veroneseSubring 𝒜 d) : A) =
      (decompose 𝒜 (x : A) (n * d) : A) := by
  conv_rhs => rw [← (decompose (veronese 𝒜 d)).symm_apply_apply x]
  exact (decompose_coeAddMonoidHom _ n).symm

/-! ### Homogeneous localizations -/

variable [NeZero d] {P : Submonoid (veroneseSubring 𝒜 d)} {Q : Submonoid A}

/-- A fraction `a / b` with `a, b ∈ S^{(d)}_i = S_{id}` as a fraction of degree `id` in `S`. -/
@[simps] def numDenMap (h : P ≤ Q.comap (veroneseSubring 𝒜 d).subtype)
    (c : NumDenSameDeg (veronese 𝒜 d) P) : NumDenSameDeg 𝒜 Q where
  deg := c.deg * d
  num := ⟨(c.num : veroneseSubring 𝒜 d), c.num.2⟩
  den := ⟨(c.den : veroneseSubring 𝒜 d), c.den.2⟩
  den_mem := h c.den_mem

set_option backward.isDefEq.respectTransparency.types false in
/-- The underlying function of `hlMap`. -/
def hlMapFun (h : P ≤ Q.comap (veroneseSubring 𝒜 d).subtype) :
    HomogeneousLocalization (veronese 𝒜 d) P → HomogeneousLocalization 𝒜 Q :=
  Quotient.map' (numDenMap h) fun x y (e : x.embedding = y.embedding) ↦ by
    apply_fun IsLocalization.map (Localization Q) (veroneseSubring 𝒜 d).subtype h at e
    simp_rw [HomogeneousLocalization.NumDenSameDeg.embedding, Localization.mk_eq_mk',
      IsLocalization.map_mk', ← Localization.mk_eq_mk'] at e
    exact e

omit [NeZero d] in
theorem hlMapFun_mk (h : P ≤ Q.comap (veroneseSubring 𝒜 d).subtype)
    (c : NumDenSameDeg (veronese 𝒜 d) P) :
    hlMapFun h (HomogeneousLocalization.mk c) = HomogeneousLocalization.mk (numDenMap h c) :=
  rfl

omit [NeZero d] in
set_option backward.isDefEq.respectTransparency.types false in
theorem val_hlMapFun (h : P ≤ Q.comap (veroneseSubring 𝒜 d).subtype)
    (x : HomogeneousLocalization (veronese 𝒜 d) P) :
    (hlMapFun h x).val =
      IsLocalization.map (Localization Q) (veroneseSubring 𝒜 d).subtype h x.val := by
  obtain ⟨c, rfl⟩ := x.mk_surjective
  rw [hlMapFun_mk, val_mk, val_mk, Localization.mk_eq_mk', Localization.mk_eq_mk',
    IsLocalization.map_mk']
  rfl

/-- The map of homogeneous localizations `S^{(d)}_{(P)} → S_{(Q)}` induced by the inclusion
`S^{(d)} → S`, for submonoids with `P ⊆ Q`: a fraction `a / b` with `a, b ∈ S^{(d)}_i = S_{id}`
goes to the same fraction of degree `id`. -/
def hlMap (h : P ≤ Q.comap (veroneseSubring 𝒜 d).subtype) :
    HomogeneousLocalization (veronese 𝒜 d) P →+* HomogeneousLocalization 𝒜 Q where
  toFun := hlMapFun h
  map_one' := val_injective _ (by rw [val_hlMapFun, val_one, map_one, val_one])
  map_mul' x y := val_injective _ (by simp only [val_hlMapFun, val_mul, map_mul])
  map_zero' := val_injective _ (by rw [val_hlMapFun, val_zero, map_zero, val_zero])
  map_add' x y := val_injective _ (by simp only [val_hlMapFun, val_add, map_add])

theorem hlMap_mk (h : P ≤ Q.comap (veroneseSubring 𝒜 d).subtype)
    (c : NumDenSameDeg (veronese 𝒜 d) P) :
    hlMap h (HomogeneousLocalization.mk c) = HomogeneousLocalization.mk (numDenMap h c) :=
  rfl

theorem val_hlMap (h : P ≤ Q.comap (veroneseSubring 𝒜 d).subtype)
    (x : HomogeneousLocalization (veronese 𝒜 d) P) :
    (hlMap h x).val =
      IsLocalization.map (Localization Q) (veroneseSubring 𝒜 d).subtype h x.val :=
  val_hlMapFun h x

omit [NeZero d] in
theorem powers_le_comap (g : veroneseSubring 𝒜 d) :
    Submonoid.powers g ≤ (Submonoid.powers (g : A)).comap (veroneseSubring 𝒜 d).subtype := by
  rintro _ ⟨k, rfl⟩
  exact ⟨k, by simp⟩

/-- The map `S^{(d)}_{(g)} → S_{(g)}` induced by the inclusion `S^{(d)} → S`. -/
def awayMap (g : veroneseSubring 𝒜 d) :
    Away (veronese 𝒜 d) g →+* Away 𝒜 (g : A) :=
  hlMap (powers_le_comap g)

omit [NeZero d] in
theorem mem_of_mem_veronese_smul {n k : ℕ} {a : veroneseSubring 𝒜 d}
    (ha : a ∈ veronese 𝒜 d (k • n)) : (a : A) ∈ 𝒜 (k • (n * d)) := by
  have : k • (n * d) = (k • n) * d := by simp [smul_eq_mul, mul_assoc]
  rw [this]
  exact ha

theorem awayMap_mk {g : veroneseSubring 𝒜 d} {n : ℕ} (hg : g ∈ veronese 𝒜 d n) (k : ℕ)
    (a : veroneseSubring 𝒜 d) (ha : a ∈ veronese 𝒜 d (k • n)) :
    awayMap g (Away.mk (veronese 𝒜 d) hg k a ha) =
      Away.mk 𝒜 (mem_veronese_iff.mp hg) k (a : A) (mem_of_mem_veronese_smul ha) := by
  apply val_injective
  rw [awayMap, val_hlMap, Away.val_mk, Away.val_mk, Localization.mk_eq_mk',
    Localization.mk_eq_mk', IsLocalization.map_mk']
  rfl

theorem awayMap_injective (g : veroneseSubring 𝒜 d) : Function.Injective (awayMap g) := by
  have : IsLocalization ((Submonoid.powers g).map (veroneseSubring 𝒜 d).subtype)
      (Localization (Submonoid.powers (g : A))) := by
    rw [Submonoid.map_powers]
    exact Localization.isLocalization
  intro x y hxy
  apply val_injective
  apply IsLocalization.map_injective_of_injective (Submonoid.powers g)
    (Localization (Submonoid.powers g)) (Localization (Submonoid.powers (g : A)))
    (g := (veroneseSubring 𝒜 d).subtype) Subtype.val_injective
  have := congrArg HomogeneousLocalization.val hxy
  rwa [awayMap, val_hlMap, val_hlMap] at this

theorem awayMap_surjective {g : veroneseSubring 𝒜 d} {n : ℕ} (hg : g ∈ veronese 𝒜 d n) :
    Function.Surjective (awayMap g) := by
  intro z
  obtain ⟨k, a, ha, rfl⟩ := Away.mk_surjective 𝒜 (mem_veronese_iff.mp hg) z
  have ha' : a ∈ 𝒜 ((k • n) * d) := by
    have : (k • n) * d = k • (n * d) := by simp [smul_eq_mul, mul_assoc]
    rwa [this]
  exact ⟨Away.mk (veronese 𝒜 d) hg k (ofMem ha') ha', awayMap_mk hg k _ _⟩

/-- **Degree-zero localizations of the Veronese subring**: for homogeneous `g ∈ S^{(d)}_n`, the
inclusion `S^{(d)} → S` induces an isomorphism `S^{(d)}_{(g)} ≅ S_{(g)}`. -/
def awayEquiv {g : veroneseSubring 𝒜 d} {n : ℕ} (hg : g ∈ veronese 𝒜 d n) :
    Away (veronese 𝒜 d) g ≃+* Away 𝒜 (g : A) :=
  RingEquiv.ofBijective (awayMap g) ⟨awayMap_injective g, awayMap_surjective hg⟩

@[simp] theorem awayEquiv_apply {g : veroneseSubring 𝒜 d} {n : ℕ} (hg : g ∈ veronese 𝒜 d n)
    (x : Away (veronese 𝒜 d) g) : awayEquiv hg x = awayMap g x :=
  rfl

end Veronese

end Hartshorne

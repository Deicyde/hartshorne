/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.SmoothMorphisms.LocalFlatnessNonZeroDivisor
import Hartshorne.Cohomology.SmoothMorphisms.ZariskiTangentMap
import Hartshorne.Scheme.Differentials.RegularQuotientCotangentIndependent
import Hartshorne.Scheme.RegularLocalCohenMacaulay
import Hartshorne.Scheme.Regular
import Mathlib.RingTheory.RingHom.Flat

/-!
# Flatness from an injective cotangent map

Hartshorne, *Algebraic Geometry*, III, proof of Proposition 10.4, (3) ⇒ (1) (p. 271).

Let `A → B` be a local homomorphism of regular local rings such that the cotangent map
`𝔪_A/𝔪_A² → 𝔪_B/𝔪_B²` preserves linear independence (over the residue fields), i.e. after
extending scalars to `κ_B` it is injective. Then `B` is flat over `A`
(`Hartshorne.RegularCotangentFlat.flat_of_cotangentLinIndep`).

## Proof

Induction on `dim A`. If `dim A = 0`, then `A` is a field. Otherwise pick `x ∈ 𝔪_A ∖ 𝔪_A²`. Its
image `x'` in `B` lies in `𝔪_B ∖ 𝔪_B²`, so `A/(x)` and `B/(x')` are regular local rings, of
dimension `dim A - 1` for the first; `x` is a non-zero-divisor on the domains `A` and `B`. The
cotangent condition passes to `A/(x) → B/(x')`, because the kernel of
`𝔪_B/𝔪_B² → 𝔪_{B'}/𝔪_{B'}²` is spanned by the class of `x'`. By induction `B/(x')` is flat over
`A/(x)`, and the local criterion of flatness by a non-zero-divisor
(`Hartshorne.flat_iff_isSMulRegular_and_flat_quotSMulTop`) gives flatness of `B` over `A`.
-/

namespace Hartshorne

noncomputable section

open IsLocalRing Module
open scoped TensorProduct

universe u

namespace RegularCotangentFlat

variable (A B : Type*) [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] [Algebra A B]
  [IsLocalHom (algebraMap A B)]

/-- The cotangent map of a local homomorphism `A → B` carries families of cotangent vectors that
are linearly independent over `κ_A` to families that are linearly independent over `κ_B`. -/
def CotangentLinIndep : Prop :=
  ∀ (m : ℕ) (a : Fin m → maximalIdeal A),
    LinearIndependent (ResidueField A) (fun i ↦ (maximalIdeal A).toCotangent (a i)) →
      LinearIndependent (ResidueField B)
        (fun i ↦ localCotangentMap A B ((maximalIdeal A).toCotangent (a i)))

section Quotient

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- Modulo a proper ideal of a local ring, only units become units. -/
theorem isUnit_of_isUnit_mk {I : Ideal R} (hI : I ≠ ⊤) {r : R}
    (h : IsUnit (Ideal.Quotient.mk I r)) : IsUnit r := by
  by_contra hr
  obtain ⟨s', hs⟩ := h.exists_right_inv
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s'
  have h1 : r * s - 1 ∈ I := Ideal.Quotient.eq.mp (by rw [map_mul, hs, map_one])
  have hrs : r * s ∈ maximalIdeal R := Ideal.mul_mem_right s _ ((mem_maximalIdeal r).mpr hr)
  have h1m : (1 : R) ∈ maximalIdeal R := by
    simpa using sub_mem hrs (le_maximalIdeal hI h1)
  exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h1m)

theorem span_singleton_ne_top {x : R} (hx : x ∈ maximalIdeal R) : Ideal.span {x} ≠ ⊤ := by
  rw [Ne, Ideal.span_singleton_eq_top]
  exact (mem_maximalIdeal x).mp hx

/-- A quotient of a local ring by a proper ideal is local. -/
theorem isLocalRing_quotient {I : Ideal R} (hI : I ≠ ⊤) : IsLocalRing (R ⧸ I) :=
  haveI := Ideal.Quotient.nontrivial_iff.mpr hI
  IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

/-- The maximal ideal of `R ⧸ I` is the image of that of `R`. -/
theorem maximalIdeal_quotient {I : Ideal R} (hI : I ≠ ⊤) [IsLocalRing (R ⧸ I)] :
    maximalIdeal (R ⧸ I) = (maximalIdeal R).map (Ideal.Quotient.mk I) := by
  have hmap : (maximalIdeal R).map (Ideal.Quotient.mk I) ≠ ⊤ := by
    intro h
    have h' := congrArg (Ideal.comap (Ideal.Quotient.mk I)) h
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, Ideal.comap_top, sup_eq_left.mpr (le_maximalIdeal hI)] at h'
    exact (maximalIdeal.isMaximal R).ne_top h'
  have hmax := (Ideal.map_eq_top_or_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    (maximalIdeal.isMaximal R)).resolve_left hmap
  exact (IsLocalRing.eq_maximalIdeal hmax).symm

/-- The kernel of the cotangent map `𝔪/𝔪² → 𝔪'/𝔪'²` of `R → R ⧸ (y)` is spanned by the class
of `y`. -/
theorem exists_eq_smul_of_localCotangentMap_eq_zero {y : R} (hy : y ∈ maximalIdeal R)
    {I : Ideal R} (hI : I = Ideal.span {y}) [IsLocalRing (R ⧸ I)]
    [IsLocalHom (algebraMap R (R ⧸ I))]
    (ω : CotangentSpace R) (hω : localCotangentMap R (R ⧸ I) ω = 0) :
    ∃ c : ResidueField R, ω = c • (maximalIdeal R).toCotangent ⟨y, hy⟩ := by
  subst hI
  obtain ⟨⟨b, hb⟩, rfl⟩ := Ideal.toCotangent_surjective _ ω
  rw [localCotangentMap_toCotangent, Ideal.toCotangent_eq_zero] at hω
  have hω' : Ideal.Quotient.mk (Ideal.span {y}) b ∈
      ((maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {y}))) ^ 2 := by
    rw [← maximalIdeal_quotient (span_singleton_ne_top hy)]; exact hω
  rw [← Ideal.map_pow] at hω'
  have hb' : b ∈ maximalIdeal R ^ 2 ⊔ Ideal.span {y} := by
    have h := Ideal.mem_comap.mpr hω'
    rwa [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker] at h
  obtain ⟨q, hq, z, hz, hqz⟩ := Submodule.mem_sup.mp hb'
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hz
  have hqm : q ∈ maximalIdeal R := Ideal.pow_le_self two_ne_zero hq
  refine ⟨residue R c, ?_⟩
  have hsplit : (⟨b, hb⟩ : maximalIdeal R) = ⟨q, hqm⟩ + c • ⟨y, hy⟩ := by
    ext; simp [← hqz, smul_eq_mul]
  rw [hsplit, map_add, map_smul, (Ideal.toCotangent_eq_zero _ _).mpr hq, zero_add,
    ← algebraMap_smul (ResidueField R) c]
  rfl

/-- The quotient map of a local ring by a proper ideal is a local homomorphism. -/
theorem isLocalHom_algebraMap_quotient {I : Ideal R} (hI : I ≠ ⊤) :
    IsLocalHom (algebraMap R (R ⧸ I)) :=
  ⟨fun _ h ↦ isUnit_of_isUnit_mk hI h⟩

end Quotient

section RegularQuotient

variable {R : Type*} [CommRing R] [IsRegularLocalRing R]

/-- `R ⧸ (y)` is a regular local ring when `R` is and `y ∈ 𝔪 ∖ 𝔪²`. -/
theorem isRegularLocalRing_quotient {y : R} (hy : y ∈ maximalIdeal R)
    (hy0 : (maximalIdeal R).toCotangent ⟨y, hy⟩ ≠ 0) {I : Ideal R} (hI : I = Ideal.span {y}) :
    IsRegularLocalRing (R ⧸ I) := by
  subst hI
  have h := isRegularLocalRing_quotient_span_range_of_linearIndependent
    (fun _ : Fin 1 ↦ (⟨y, hy⟩ : maximalIdeal R)) (linearIndependent_unique_iff.mpr hy0)
  rwa [Set.range_const] at h

/-- If `R` is a regular local ring of dimension `n + 1` and `y ∈ 𝔪 ∖ 𝔪²`, then `R ⧸ (y)` has
dimension `n`. -/
theorem ringKrullDim_quotient {y : R} (hy : y ∈ maximalIdeal R)
    (hy0 : (maximalIdeal R).toCotangent ⟨y, hy⟩ ≠ 0) {I : Ideal R} (hI : I = Ideal.span {y})
    {n : ℕ} (hn : ringKrullDim R = (n + 1 : ℕ)) : ringKrullDim (R ⧸ I) = n := by
  subst hI
  have h := ringKrullDim_quotient_span_range_add_card_of_linearIndependent
    (fun _ : Fin 1 ↦ (⟨y, hy⟩ : maximalIdeal R)) (linearIndependent_unique_iff.mpr hy0)
  rw [Set.range_const, Fintype.card_fin, hn] at h
  generalize ringKrullDim (R ⧸ Ideal.span {y}) = e at h ⊢
  induction e using WithBot.recBotCoe with
  | bot =>
    simp at h
    exact absurd h.symm (by simp)
  | coe e =>
    induction e using ENat.recTopCoe with
    | top => norm_cast at h
    | coe e =>
      norm_cast at h ⊢
      omega

end RegularQuotient

section Step

variable {A B : Type*} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] [Algebra A B]
  [IsLocalHom (algebraMap A B)]

omit [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] in
theorem map_span_singleton (x : A) :
    (Ideal.span {x}).map (algebraMap A B) = Ideal.span {algebraMap A B x} := by
  rw [Ideal.map_span, Set.image_singleton]

omit [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] in
open scoped Pointwise in
theorem smul_top_eq_restrictScalars (x : A) :
    (x • ⊤ : Submodule A B) = ((Ideal.span {x}).map (algebraMap A B)).restrictScalars A := by
  ext b
  rw [Submodule.restrictScalars_mem, map_span_singleton, Ideal.mem_span_singleton',
    Submodule.mem_smul_pointwise_iff_exists]
  simp only [Submodule.mem_top, true_and, Algebra.smul_def, mul_comm]

/-- `B ⧸ x B ≅ B ⧸ (x) B` as modules over `A ⧸ (x)`. -/
def quotSMulTopEquiv (x : A) :
    QuotSMulTop x B ≃ₗ[A ⧸ Ideal.span {x}] B ⧸ (Ideal.span {x}).map (algebraMap A B) :=
  ((Submodule.quotEquivOfEq _ _ (smul_top_eq_restrictScalars x)).trans
    (Submodule.Quotient.restrictScalarsEquiv A _)).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective

/-- The cotangent condition passes to `A ⧸ (x) → B ⧸ (x)B` for `x ∈ 𝔪_A ∖ 𝔪_A²`. -/
theorem cotangentLinIndep_quotient {x : A} (hx : x ∈ maximalIdeal A)
    (hx0 : (maximalIdeal A).toCotangent ⟨x, hx⟩ ≠ 0)
    [IsLocalRing (A ⧸ Ideal.span {x})]
    [IsLocalRing (B ⧸ (Ideal.span {x}).map (algebraMap A B))]
    [IsLocalHom (algebraMap A (A ⧸ Ideal.span {x}))]
    [IsLocalHom (algebraMap B (B ⧸ (Ideal.span {x}).map (algebraMap A B)))]
    [IsLocalHom (algebraMap (A ⧸ Ideal.span {x}) (B ⧸ (Ideal.span {x}).map (algebraMap A B)))]
    (H : CotangentLinIndep A B) :
    CotangentLinIndep (A ⧸ Ideal.span {x}) (B ⧸ (Ideal.span {x}).map (algebraMap A B)) := by
  intro m a' ha'
  have hmA := maximalIdeal_quotient (span_singleton_ne_top hx)
  choose a ha using fun i ↦ (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp
    (by rw [← hmA]; exact (a' i).2)
  let v : Fin (m + 1) → maximalIdeal A := Fin.cons ⟨x, hx⟩ fun i ↦ ⟨a i, (ha i).1⟩
  have e1 :
      localCotangentMap A (A ⧸ Ideal.span {x}) ((maximalIdeal A).toCotangent ⟨x, hx⟩) = 0 := by
    rw [localCotangentMap_toCotangent, Ideal.toCotangent_eq_zero]
    change Ideal.Quotient.mk _ x ∈ _
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self x)]
    exact zero_mem _
  have e2 : ∀ i, localCotangentMap A (A ⧸ Ideal.span {x})
      ((maximalIdeal A).toCotangent ⟨a i, (ha i).1⟩) = (maximalIdeal _).toCotangent (a' i) := by
    intro i
    rw [localCotangentMap_toCotangent]
    congr 1
    exact Subtype.ext (ha i).2
  have hv : LinearIndependent (ResidueField A) fun j ↦ (maximalIdeal A).toCotangent (v j) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_succ] at hg
    have hg' := congrArg (localCotangentMap A (A ⧸ Ideal.span {x})) hg
    simp only [map_add, map_sum, localCotangentMap_residue_smul, map_zero, v, Fin.cons_zero,
      Fin.cons_succ, e1, e2, smul_zero, zero_add] at hg'
    have htail := (Fintype.linearIndependent_iff.mp ha') _ hg'
    have htail' : ∀ i : Fin m, g i.succ = 0 := fun i ↦
      (algebraMap (ResidueField A) (ResidueField (A ⧸ Ideal.span {x}))).injective
        (by rw [htail i, map_zero])
    simp only [v, htail', zero_smul, Finset.sum_const_zero, add_zero, Fin.cons_zero] at hg
    have h0 : g 0 = 0 := (smul_eq_zero.mp hg).resolve_right hx0
    intro j
    exact Fin.cases h0 htail' j
  have hw := H (m + 1) v hv
  have hy : algebraMap A B x ∈ maximalIdeal B := maximalIdeal_le_comap_ofId A B hx
  have hsurj : Function.Surjective (algebraMap (ResidueField B)
      (ResidueField (B ⧸ (Ideal.span {x}).map (algebraMap A B)))) := by
    intro z
    obtain ⟨z, rfl⟩ := residue_surjective z
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨residue B b, ResidueField.algebraMap_residue _⟩
  have e3 : ∀ i, localCotangentMap (A ⧸ Ideal.span {x})
      (B ⧸ (Ideal.span {x}).map (algebraMap A B)) ((maximalIdeal _).toCotangent (a' i)) =
      localCotangentMap B (B ⧸ (Ideal.span {x}).map (algebraMap A B))
        (localCotangentMap A B ((maximalIdeal A).toCotangent (v i.succ))) := by
    intro i
    simp only [v, Fin.cons_succ, localCotangentMap_toCotangent]
    congr 1
    refine Subtype.ext ?_
    change algebraMap _ _ (a' i : A ⧸ Ideal.span {x}) = Ideal.Quotient.mk _ (algebraMap A B (a i))
    rw [← (ha i).2]
    rfl
  rw [Fintype.linearIndependent_iff]
  intro h hh i
  choose k hk using fun i ↦ hsurj (h i)
  simp only [e3, ← hk, ← localCotangentMap_residue_smul, ← map_sum] at hh
  obtain ⟨c, hc⟩ := exists_eq_smul_of_localCotangentMap_eq_zero hy (map_span_singleton x) _ hh
  have hcons := (Fintype.linearIndependent_iff.mp hw) (Fin.cons (-c) k) (by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [hc, neg_smul]
    simp only [v, Fin.cons_zero, localCotangentMap_toCotangent]
    exact neg_add_cancel _)
  rw [← hk i, show k i = 0 from hcons i.succ, map_zero]

end Step

universe v

/-- Induction on `dim A` for `Hartshorne.RegularCotangentFlat.flat_of_cotangentLinIndep`. -/
theorem flat_of_cotangentLinIndep_of_ringKrullDim_eq (n : ℕ) :
    ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [IsRegularLocalRing A]
      [IsRegularLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)],
      ringKrullDim A = n → CotangentLinIndep A B → Module.Flat A B := by
  induction n with
  | zero =>
    intro A B _ _ _ _ _ _ hdim _
    have hf : finrank (ResidueField A) (CotangentSpace A) = 0 := by
      have := (IsRegularLocalRing.iff_finrank_cotangentSpace A).mp inferInstance
      rw [hdim] at this
      exact_mod_cast this
    let _ := (finrank_cotangentSpace_eq_zero_iff.mp hf).toField
    infer_instance
  | succ n ih =>
    intro A B _ _ _ _ _ _ hdim H
    have hfr : finrank (ResidueField A) (CotangentSpace A) = n + 1 := by
      have := (IsRegularLocalRing.iff_finrank_cotangentSpace A).mp inferInstance
      rw [hdim] at this
      exact_mod_cast this
    obtain ⟨⟨x, hx⟩, hx0⟩ : ∃ v : maximalIdeal A, (maximalIdeal A).toCotangent v ≠ 0 := by
      by_contra! h
      have : Subsingleton (CotangentSpace A) := by
        refine ⟨fun a b ↦ ?_⟩
        obtain ⟨a, rfl⟩ := Ideal.toCotangent_surjective _ a
        obtain ⟨b, rfl⟩ := Ideal.toCotangent_surjective _ b
        rw [h a, h b]
      rw [finrank_zero_of_subsingleton] at hfr
      omega
    have hy : algebraMap A B x ∈ maximalIdeal B := maximalIdeal_le_comap_ofId A B hx
    have hy0 : (maximalIdeal B).toCotangent ⟨algebraMap A B x, hy⟩ ≠ 0 :=
      linearIndependent_unique_iff.mp
        (H 1 (fun _ ↦ ⟨x, hx⟩) (linearIndependent_unique_iff.mpr hx0))
    have hJ := map_span_singleton (B := B) x
    have hJtop : (Ideal.span {x}).map (algebraMap A B) ≠ ⊤ := hJ ▸ span_singleton_ne_top hy
    have : IsRegularLocalRing (A ⧸ Ideal.span {x}) := isRegularLocalRing_quotient hx hx0 rfl
    have : IsRegularLocalRing (B ⧸ (Ideal.span {x}).map (algebraMap A B)) :=
      isRegularLocalRing_quotient hy hy0 hJ
    have : IsLocalHom (algebraMap A (A ⧸ Ideal.span {x})) :=
      isLocalHom_algebraMap_quotient (span_singleton_ne_top hx)
    have : IsLocalHom (algebraMap B (B ⧸ (Ideal.span {x}).map (algebraMap A B))) :=
      isLocalHom_algebraMap_quotient hJtop
    have : IsLocalHom
        (algebraMap (A ⧸ Ideal.span {x}) (B ⧸ (Ideal.span {x}).map (algebraMap A B))) := by
      refine ⟨fun a h ↦ ?_⟩
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      exact (isUnit_of_map_unit (algebraMap A B) a (isUnit_of_isUnit_mk hJtop h)).map _
    have hflat : Module.Flat (A ⧸ Ideal.span {x}) (B ⧸ (Ideal.span {x}).map (algebraMap A B)) :=
      ih _ _ (ringKrullDim_quotient hx hx0 rfl hdim) (cotangentLinIndep_quotient hx hx0 H)
    have : IsDomain A := RegularLocal.isDomain A
    have : IsDomain B := RegularLocal.isDomain B
    have hx0' : x ≠ 0 := fun h ↦ hx0 (by rw [Ideal.toCotangent_eq_zero]; simp [h])
    have hy0' : algebraMap A B x ≠ 0 := fun h ↦ hy0 (by rw [Ideal.toCotangent_eq_zero]; simp [h])
    refine (flat_iff_isSMulRegular_and_flat_quotSMulTop (B := B) (M := B)
      ((mem_maximalIdeal x).mp hx) (mem_nonZeroDivisors_of_ne_zero hx0')).mpr ⟨?_, ?_⟩
    · intro b c hbc
      simp only [Algebra.smul_def] at hbc
      exact mul_left_cancel₀ hy0' hbc
    · exact Module.Flat.of_linearEquiv (quotSMulTopEquiv x)

/-- **Hartshorne III, proof of Proposition 10.4, (3) ⇒ (1)** (algebraic core). Let `A → B` be a
local homomorphism of regular local rings whose cotangent map `𝔪_A/𝔪_A² → 𝔪_B/𝔪_B²` carries
`κ_A`-linearly independent families to `κ_B`-linearly independent families. Then `B` is flat
over `A`. -/
theorem flat_of_cotangentLinIndep (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [IsRegularLocalRing A] [IsRegularLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    (H : CotangentLinIndep A B) : Module.Flat A B := by
  have hfin := (IsRegularLocalRing.iff_finrank_cotangentSpace A).mp inferInstance
  exact flat_of_cotangentLinIndep_of_ringKrullDim_eq _ A B hfin.symm H

/-- Base change along a field extension `K/k` preserves linear independence:
if `v` is `k`-linearly independent, then `1 ⊗ v` is `K`-linearly independent in `K ⊗_k V`. -/
theorem linearIndependent_one_tmul {k K V ι : Type*} [Field k] [Field K] [Algebra k K]
    [AddCommGroup V] [Module k V] {v : ι → V} (hv : LinearIndependent k v) :
    LinearIndependent K fun i ↦ (1 : K) ⊗ₜ[k] v i := by
  let b := Basis.extend hv.linearIndepOn_id
  let j : ι → hv.linearIndepOn_id.extend (Set.subset_univ _) :=
    fun i ↦ ⟨v i, Basis.subset_extend hv.linearIndepOn_id (Set.mem_range_self i)⟩
  have hj : Function.Injective j := fun i i' h ↦ hv.injective (congrArg Subtype.val h)
  convert (b.baseChange K).linearIndependent.comp j hj with i
  simp [b, j]

section Corollaries

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [IsRegularLocalRing A]
  [IsRegularLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]

omit [IsRegularLocalRing A] [IsRegularLocalRing B] in
/-- If the scalar-extended cotangent map `κ_B ⊗_{κ_A} 𝔪_A/𝔪_A² → 𝔪_B/𝔪_B²` is injective, the
cotangent map preserves linear independence. -/
theorem cotangentLinIndep_of_injective [IsLocalRing A] [IsLocalRing B]
    (h : Function.Injective (localCotangentBaseChange A B)) : CotangentLinIndep A B := by
  intro m a ha
  have := (linearIndependent_one_tmul (K := ResidueField B) ha).map'
    (localCotangentBaseChange A B) (LinearMap.ker_eq_bot.mpr h)
  simpa [Function.comp_def, localCotangentBaseChange_tmul] using this

/-- **Hartshorne III, proof of Proposition 10.4, (3) ⇒ (1)** (local form). For a local
homomorphism of regular local rings `A → B`, if `κ_B ⊗_{κ_A} 𝔪_A/𝔪_A² → 𝔪_B/𝔪_B²` is injective,
then `B` is flat over `A`. -/
theorem flat_of_injective_localCotangentBaseChange
    (h : Function.Injective (localCotangentBaseChange A B)) : Module.Flat A B :=
  flat_of_cotangentLinIndep A B (cotangentLinIndep_of_injective A B h)

/-- **Hartshorne III, proof of Proposition 10.4, (3) ⇒ (1)** (local form, tangent version). For
a local homomorphism of regular local rings `A → B`, if the tangent map
`T_B → κ_B ⊗_{κ_A} T_A` is surjective, then `B` is flat over `A`. -/
theorem flat_of_surjective_localTangentMap
    (h : Function.Surjective (localTangentMap A B)) : Module.Flat A B := by
  refine flat_of_injective_localCotangentBaseChange A B ?_
  refine LinearMap.dualMap_surjective_iff.mp ?_
  rw [← dualBaseChangeEquiv_comp_localTangentMap, LinearMap.coe_comp]
  exact (LinearEquiv.surjective _).comp h

end Corollaries

section Scheme

open AlgebraicGeometry CategoryTheory

/-- **Hartshorne III, proof of Proposition 10.4, (3) ⇒ (1)** (at a point). Let `f : X ⟶ Y` be a
morphism of schemes and `x ∈ X` such that `X` is regular at `x` and `Y` is regular at `f x`. If
the Zariski tangent map `T_x X → k(x) ⊗_{k(f x)} T_{f x} Y` is surjective, then the stalk map
`𝒪_{Y, f x} → 𝒪_{X, x}` is flat. -/
theorem flat_stalkMap_of_surjective_zariskiTangentMap {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (hX : X.IsRegularAt x) (hY : Y.IsRegularAt (f x))
    [Module.Finite (ResidueField (Y.presheaf.stalk (f x)))
      (CotangentSpace (Y.presheaf.stalk (f x)))]
    (h : Function.Surjective (zariskiTangentMap f x)) : (f.stalkMap x).hom.Flat := by
  let _ := (f.stalkMap x).hom.toAlgebra
  have := isLocalHom_stalkMap_algebraMap f x
  have : IsRegularLocalRing (X.presheaf.stalk x) := hX
  have : IsRegularLocalRing (Y.presheaf.stalk (f x)) := hY
  exact flat_of_surjective_localTangentMap _ _ h

end Scheme

end RegularCotangentFlat

end

end Hartshorne

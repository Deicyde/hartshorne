/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.WeilClassGroup
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.RingTheory.RegularLocalRing.Polynomial

/-!
# The class group of the relative affine line

Hartshorne, *Algebraic Geometry*, II.6, Proposition 6.6 (pp. 134--135).

The relative affine line over a scheme `X` is `𝔸¹_X = X ×_ℤ Spec ℤ[t]`, written
`𝔸(PUnit; X)`. If `X` satisfies Hartshorne's condition `(*)` then so does `𝔸¹_X`:
it is Noetherian and separated because the projection is affine of finite type, integral
because the projection is geometrically integral, and regular in codimension one because,
for a Noetherian domain `A` whose height-one localizations are regular, every height-one
localization of `A[t]` is regular. The last fact reduces, after localizing at the
contraction `q` of a height-one prime of `A[t]` (which has height at most one by going
down along the flat extension `A → A[t]`), to Mathlib's theorem that a polynomial ring over
a regular local ring has regular localizations at primes lying over the maximal ideal.
-/

noncomputable section

open CategoryTheory Limits Polynomial IsLocalRing Ideal

namespace Hartshorne

/-- A commutative ring is regular in codimension one when its localization at every prime of
height one is a regular local ring. -/
def RingIsRegularInCodimensionOne (R : Type*) [CommRing R] : Prop :=
  ∀ (p : Ideal R) [p.IsPrime], p.height = 1 → IsRegularLocalRing (Localization.AtPrime p)

/-- In a Noetherian domain that is regular in codimension one, the localization at any prime of
height at most one is regular. -/
theorem isRegularLocalRing_localization_of_height_le_one {A : Type*} [CommRing A]
    [IsNoetherianRing A] [IsDomain A] (hA : RingIsRegularInCodimensionOne A)
    (q : Ideal A) [q.IsPrime] (hq : q.height ≤ 1) :
    IsRegularLocalRing (Localization.AtPrime q) := by
  rcases (show q.height = 0 ∨ q.height = 1 by
    rcases eq_or_lt_of_le hq with h | h
    · exact Or.inr h
    · exact Or.inl ((Order.lt_one_iff).mp h)) with h0 | h1
  · have hdim : ringKrullDim (Localization.AtPrime q) = 0 := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q), h0]
      rfl
    have : Ring.KrullDimLE 0 (Localization.AtPrime q) := Ring.krullDimLE_iff.mpr hdim.le
    have hfield : IsField (Localization.AtPrime q) := Ring.KrullDimLE.isField_of_isDomain
    apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
    rw [(isField_iff_maximalIdeal_eq.mp hfield), Submodule.spanFinrank_bot, hdim]
    rfl
  · exact hA q h1

/-- **Polynomial rings preserve regularity in codimension one.** If `A` is a Noetherian domain
whose localizations at height-one primes are regular, then so is `A[X]`. -/
theorem Polynomial.ringIsRegularInCodimensionOne {A : Type*} [CommRing A]
    [IsNoetherianRing A] [IsDomain A] (hA : RingIsRegularInCodimensionOne A) :
    RingIsRegularInCodimensionOne A[X] := by
  intro p hp hp1
  let q := p.comap C
  have hqle : q.height ≤ 1 := by
    have : p.LiesOver q := ⟨rfl⟩
    rw [← hp1, Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown q p]
    exact le_self_add
  let S := (Localization.AtPrime q)[X]
  let pc := Submonoid.map Polynomial.C.toMonoidHom q.primeCompl
  let : Algebra A[X] S := Polynomial.algebra A (Localization.AtPrime q)
  have : IsLocalization pc S := Polynomial.isLocalization _ _
  let pS := p.map (algebraMap A[X] S)
  have disj : Disjoint (pc : Set A[X]) (p : Set A[X]) := by
    simpa [pc, q] using! Set.disjoint_image_left.mpr
      (Set.disjoint_compl_left_iff_subset.mpr (fun _ a ↦ a))
  have : pS.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint pc _ _ ‹_› disj
  have : IsLocalization.AtPrime (Localization.AtPrime pS) p := by
    convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization pc
      (Localization.AtPrime pS) pS
    exact (IsLocalization.under_map_of_isPrime_disjoint pc _ ‹_› disj).symm
  have := isRegularLocalRing_localization_of_height_le_one hA q hqle
  have eq : comap C pS = maximalIdeal (Localization.AtPrime q) := by
    rw [← IsLocalization.map_under q.primeCompl _ (comap C pS),
      ← IsLocalization.map_under q.primeCompl _ (maximalIdeal (Localization.AtPrime q))]
    simp only [comap_comap, S, pS]
    rw [← Polynomial.algebraMap_eq (R := Localization.AtPrime q),
      ← IsScalarTower.algebraMap_eq A (Localization.AtPrime q) (Localization.AtPrime q)[X],
      IsScalarTower.algebraMap_eq A A[X] (Localization.AtPrime q)[X], ← comap_comap,
      ← Ideal.under_def A[X], IsLocalization.under_map_of_isPrime_disjoint pc _ ‹_› disj]
    simp [q, IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime q) q]
  have := Polynomial.isRegularLocalRing_localization_atPrime_of_comap_eq_maximalIdeal _ pS eq
  exact IsRegularLocalRing.of_ringEquiv (R := Localization.AtPrime pS)
    (IsLocalization.algEquiv p.primeCompl
    (Localization.AtPrime pS) (Localization.AtPrime p)).toRingEquiv

/-- Regularity in codimension one is invariant under ring isomorphisms. -/
theorem RingIsRegularInCodimensionOne.of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (hR : RingIsRegularInCodimensionOne R) : RingIsRegularInCodimensionOne S := by
  intro P hP hP1
  let Q : Ideal R := P.comap e
  have hQ1 : Q.height = 1 := by
    rw [← hP1]
    exact e.height_comap P
  have := hR Q hQ1
  have hmap : Q.primeCompl.map (e : R →* S) = P.primeCompl := by
    ext s
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact hr
    · intro hs
      refine ⟨e.symm s, ?_, by simp⟩
      change e.symm s ∉ P.comap e
      rw [Ideal.mem_comap]
      simpa using hs
  exact IsRegularLocalRing.of_ringEquiv (IsLocalization.ringEquivOfRingEquiv
    (Localization.AtPrime Q) (Localization.AtPrime P) e hmap)


/-- Contracting the extension of an ideal of `R` to `R[X]` gives back the ideal. -/
theorem comap_C_map_C {R : Type*} [CommRing R] (p : Ideal R) :
    (p.map (C : R →+* R[X])).comap C = p := by
  ext r
  simp only [Ideal.mem_comap, Ideal.mem_map_C_iff]
  constructor
  · intro h
    simpa only [coeff_C_zero] using h 0
  · rintro h (- | n)
    · rwa [coeff_C_zero]
    · simp only [coeff_C_of_ne_zero (Nat.succ_ne_zero _), Submodule.zero_mem]

/-- Going down along `R → R[X]`: the contraction of a prime of `R[X]` has height at most the
height of the prime. -/
theorem height_comap_C_le {R : Type*} [CommRing R] [IsNoetherianRing R]
    (P : Ideal R[X]) [P.IsPrime] : (P.comap C).height ≤ P.height := by
  have : P.LiesOver (P.comap C) := ⟨rfl⟩
  rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (P.comap C) P]
  exact le_self_add

/-- A prime of `R[X]` has the same height as its contraction to `R` exactly when it is the
extension of that contraction. -/
theorem height_eq_height_comap_C_iff {R : Type*} [CommRing R] [IsNoetherianRing R]
    (P : Ideal R[X]) [P.IsPrime] : P.height = (P.comap C).height ↔ P = (P.comap C).map C := by
  set q := P.comap C with hq
  have : P.LiesOver q := ⟨rfl⟩
  let Q : Ideal R[X] := q.map (algebraMap R R[X])
  have hQ : Q = q.map C := rfl
  have : Q.IsPrime := Ideal.isPrime_map_C_of_isPrime
  have hQP : Q ≤ P := Ideal.map_comap_le
  have : (P.map (Ideal.Quotient.mk Q)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown q P, ← hQ]
  have hfin : q.height ≠ ⊤ := Ideal.height_ne_top_of_isPrime
  constructor
  · intro h
    have h0 : (P.map (Ideal.Quotient.mk Q)).height = 0 := by
      have h' : q.height + (P.map (Ideal.Quotient.mk Q)).height = q.height + 0 := by
        rw [add_zero]; exact h
      rw [add_comm q.height, add_comm q.height] at h'
      exact (WithTop.add_right_inj hfin).mp h'
    rw [Ideal.height_eq_zero_iff_eq_bot, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker] at h0
    exact le_antisymm h0 hQP
  · intro h
    have : P.map (Ideal.Quotient.mk Q) = ⊥ := by
      rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
      exact h.le
    rw [this, Ideal.height_bot, add_zero]


/-- A local homomorphism of discrete valuation rings carrying the maximal ideal onto the maximal
ideal preserves the normalized valuation, via any compatible map of fraction fields. -/
theorem ordFrac_map_of_map_maximalIdeal_eq {A B K L : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Field K]
    [Algebra A K] [IsFractionRing A K] [Field L] [Algebra B L] [IsFractionRing B L]
    (φ : A →+* B) [IsLocalHom φ] (ψ : K →+* L)
    (hψ : ∀ a, ψ (algebraMap A K a) = algebraMap B L (φ a))
    (hm : (maximalIdeal A).map φ = maximalIdeal B) (k : K) :
    Ring.ordFrac B (ψ k) = Ring.ordFrac A k := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hϖB : Irreducible (φ ϖ) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer] at hϖ ⊢
    rw [← hm, hϖ, Ideal.map_span, Set.image_singleton]
  have key : ∀ a : A, Ring.ordFrac B (algebraMap B L (φ a)) = Ring.ordFrac A (algebraMap A K a) := by
    intro a
    by_cases ha : a = 0
    · simp [ha]
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
    simp only [map_mul, map_pow]
    rw [Ring.ordFrac_of_isUnit (u.isUnit.map φ), Ring.ordFrac_of_isUnit u.isUnit,
      Ring.ordFrac_irreducible hϖB, Ring.ordFrac_irreducible hϖ]
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := A) k
  rw [map_div₀, hψ, hψ, map_div₀, map_div₀, key, key]



/-- Precomposing with a ring isomorphism of local rings does not change the image of the maximal
ideal. -/
theorem map_maximalIdeal_comp_ringEquiv {A A' B : Type*} [CommRing A] [CommRing A'] [CommRing B]
    [IsLocalRing A] [IsLocalRing A'] (e : A' ≃+* A) (φ : A →+* B) :
    (maximalIdeal A').map (φ.comp (e : A' →+* A)) = (maximalIdeal A).map φ := by
  rw [← Ideal.map_map]
  exact congrArg (Ideal.map φ) (map_ringEquiv_maximalIdeal e)

/-- Postcomposing with a ring isomorphism of local rings preserves the property that the maximal
ideal generates the maximal ideal. -/
theorem map_maximalIdeal_ringEquiv_comp_iff {A B B' : Type*} [CommRing A] [CommRing B]
    [CommRing B'] [IsLocalRing A] [IsLocalRing B] [IsLocalRing B'] (φ : A →+* B) (e : B ≃+* B') :
    (maximalIdeal A).map ((e : B →+* B').comp φ) = maximalIdeal B' ↔
      (maximalIdeal A).map φ = maximalIdeal B := by
  constructor
  · intro h
    have h' := congrArg (Ideal.map (e.symm : B' →+* B)) h
    rw [Ideal.map_map, show ((e.symm : B' →+* B).comp ((e : B →+* B').comp φ)) = φ by
      ext; simp] at h'
    rw [h']
    exact map_ringEquiv_maximalIdeal e.symm
  · intro h
    rw [← Ideal.map_map, h]
    exact map_ringEquiv_maximalIdeal e

/-- For a prime `p` of `R`, the maximal ideal of `R_p` generates the maximal ideal of
`R[X]_{p[X]}`. -/
theorem map_maximalIdeal_localRingHom_C {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime]
    (P : Ideal R[X]) [P.IsPrime] (hP : P = p.map C) (hp : p = P.comap C) :
    (maximalIdeal (Localization.AtPrime p)).map (Localization.localRingHom p P C hp) =
      maximalIdeal (Localization.AtPrime P) := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
    ← Localization.AtPrime.map_eq_maximalIdeal]
  rw [show Ideal.map (algebraMap R[X] (Localization.AtPrime P)) P =
    Ideal.map (algebraMap R[X] (Localization.AtPrime P)) (p.map C) from congrArg _ hP,
    Ideal.map_map]
  congr 1
  ext r
  simp

/-- Composing with isomorphisms on both sides preserves the property that the maximal ideal
generates the maximal ideal. -/
theorem map_maximalIdeal_iso_comp_iff {A' A B B' : CommRingCat} [IsLocalRing A'] [IsLocalRing A]
    [IsLocalRing B] [IsLocalRing B'] (e₁ : A' ≅ A) (φ : A ⟶ B) (e₂ : B' ≅ B) :
    (maximalIdeal A').map (e₁.hom ≫ φ ≫ e₂.inv).hom = maximalIdeal B' ↔
      (maximalIdeal A).map φ.hom = maximalIdeal B := by
  have : (e₁.hom ≫ φ ≫ e₂.inv).hom = (e₂.symm.commRingCatIsoToRingEquiv : B →+* B').comp
      (φ.hom.comp (e₁.commRingCatIsoToRingEquiv : A' →+* A)) := rfl
  rw [this, map_maximalIdeal_ringEquiv_comp_iff, map_maximalIdeal_comp_ringEquiv]


section Horizontal

attribute [local instance] Polynomial.algebra

variable {R : Type*} [CommRing R] [IsDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

variable (R) in
/-- The multiplicative set of nonzero constants of `R[X]`. -/
abbrev nonzeroConstants : Submonoid R[X] := (nonZeroDivisors R).map (C : R →+* R[X])

omit [IsDomain R] in
theorem isLocalization_nonzeroConstants :
    IsLocalization (nonzeroConstants R) K[X] :=
  Polynomial.isLocalization (nonZeroDivisors R) K

attribute [local instance] isLocalization_nonzeroConstants

/-- A prime of `R[X]` lying over the zero ideal of `R` misses the nonzero constants. -/
theorem disjoint_nonzeroConstants {P : Ideal R[X]} (hP : P.comap C = ⊥) :
    Disjoint (nonzeroConstants R : Set R[X]) P := by
  rw [Set.disjoint_left]
  rintro x ⟨r, hr, rfl⟩ hx
  have : r ∈ P.comap C := hx
  rw [hP, Ideal.mem_bot] at this
  exact nonZeroDivisors.ne_zero hr this

variable (K) in
/-- The contraction to `R[X]` of a proper ideal of `K[X]` lies over the zero ideal of `R`. -/
theorem comap_C_comap_algebraMap_eq_bot {Q : Ideal K[X]} (hQ : Q ≠ ⊤) :
    (Q.comap (algebraMap R[X] K[X])).comap C = ⊥ := by
  rw [eq_bot_iff]
  intro r hr
  rw [Ideal.mem_bot]
  by_contra h0
  apply hQ
  apply Ideal.eq_top_of_isUnit_mem _ (show algebraMap R[X] K[X] (C r) ∈ Q from hr)
  rw [Polynomial.algebraMap_def, coe_mapRingHom, map_C]
  have : algebraMap R K r ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero h0)
  exact isUnit_C.mpr this.isUnit

variable (K) in
/-- A nonzero prime of `K[X]` contracts to a height-one prime of `R[X]`. -/
theorem height_comap_algebraMap_eq_one {Q : Ideal K[X]} [Q.IsPrime] (hQ : Q ≠ ⊥) :
    (Q.comap (algebraMap R[X] K[X])).height = 1 := by
  have hQ' : Q.IsMaximal := IsPrime.to_maximal_ideal hQ
  have hdisj := disjoint_nonzeroConstants (comap_C_comap_algebraMap_eq_bot (R := R) K hQ'.ne_top)
  have : (Q.comap (algebraMap R[X] K[X])).IsPrime := Ideal.comap_isPrime _ _
  rw [← IsLocalization.height_map_of_disjoint (S := K[X]) (nonzeroConstants R) _ hdisj]
  rw [show Ideal.map (algebraMap R[X] K[X]) (Q.comap (algebraMap R[X] K[X])) = Q from
    IsLocalization.map_under (nonzeroConstants R) K[X] Q]
  exact IsPrincipalIdealRing.height_eq_one_of_isMaximal Q (Polynomial.not_isField K)

section Local

variable (K) (P : Ideal R[X]) [P.IsPrime] (hP : P.comap C = ⊥) (A : Type*) [CommRing A]
  [Algebra R[X] A] [IsLocalization.AtPrime A P]

include hP in
theorem isUnit_algebraMap_nonzeroConstants (y : nonzeroConstants R) :
    IsUnit (algebraMap R[X] A y) := by
  rw [IsLocalization.AtPrime.isUnit_to_map_iff A P]
  exact Set.disjoint_left.mp (disjoint_nonzeroConstants hP) y.2

/-- The localization of `R[X]` at a prime over the zero ideal of `R` receives `K[X]`. -/
noncomputable def horizontalLift : K[X] →+* A :=
  IsLocalization.lift (M := nonzeroConstants R) (S := K[X])
    (isUnit_algebraMap_nonzeroConstants P hP A)

theorem horizontalLift_algebraMap (s : R[X]) :
    horizontalLift K P hP A (algebraMap R[X] K[X] s) = algebraMap R[X] A s :=
  IsLocalization.lift_eq _ s

theorem comap_maximalIdeal_horizontalLift :
    have : IsLocalRing A := IsLocalization.AtPrime.isLocalRing A P
    (maximalIdeal A).comap (horizontalLift K P hP A) = P.map (algebraMap R[X] K[X]) := by
  intro _
  set J := (maximalIdeal A).comap (horizontalLift K P hP A)
  have hJ : J.comap (algebraMap R[X] K[X]) = P := by
    rw [Ideal.comap_comap]
    have : (horizontalLift K P hP A).comp (algebraMap R[X] K[X]) = algebraMap R[X] A :=
      IsLocalization.lift_comp _
    rw [this]
    exact IsLocalization.AtPrime.under_maximalIdeal A P
  rw [← hJ]
  exact (IsLocalization.map_under (nonzeroConstants R) K[X] J).symm

variable (L : Type*) [Field L] [Algebra R[X] L] [Algebra K[X] L] [IsScalarTower R[X] K[X] L]
  [Algebra A L] [IsScalarTower R[X] A L]

theorem algebraMap_horizontalLift (b : K[X]) :
    algebraMap A L (horizontalLift K P hP A b) = algebraMap K[X] L b := by
  have : (algebraMap A L).comp (horizontalLift K P hP A) = algebraMap K[X] L := by
    apply IsLocalization.ringHom_ext (nonzeroConstants R)
    refine RingHom.ext fun s => ?_
    simp only [RingHom.comp_apply, horizontalLift_algebraMap]
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  exact RingHom.congr_fun this b

variable [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A L]

include hP in
/-- A polynomial over `K` outside the extension of `P` has order zero along `P`. -/
theorem ordFrac_algebraMap_eq_one_of_notMem {b : K[X]} (hb : b ∉ P.map (algebraMap R[X] K[X])) :
    Ring.ordFrac A (algebraMap K[X] L b) = 1 := by
  rw [← algebraMap_horizontalLift K P hP A L]
  apply Ring.ordFrac_of_isUnit
  by_contra h
  apply hb
  rw [← comap_maximalIdeal_horizontalLift K P hP A]
  exact (mem_maximalIdeal _).mpr h

include hP in
/-- A generator of the extension of `P` has order one along `P`. -/
theorem ordFrac_algebraMap_eq_exp_one_of_span_eq {q : K[X]}
    (hq : Ideal.span {q} = P.map (algebraMap R[X] K[X])) :
    Ring.ordFrac A (algebraMap K[X] L q) = WithZero.exp 1 := by
  rw [← algebraMap_horizontalLift K P hP A L]
  apply Ring.ordFrac_irreducible
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
  apply le_antisymm
  · rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P A, Ideal.map_le_iff_le_comap]
    intro p hp
    have hmem : algebraMap R[X] K[X] p ∈ Ideal.span {q} := hq ▸ Ideal.mem_map_of_mem _ hp
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hmem
    rw [Ideal.mem_comap, ← horizontalLift_algebraMap K P hP A, ← ht, map_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, ← Ideal.mem_comap,
      comap_maximalIdeal_horizontalLift K P hP A, ← hq]
    exact Ideal.mem_span_singleton_self q

end Local

end Horizontal

/-- An element of the fraction field of `K[X]` with order zero along every irreducible polynomial
is a constant. -/
theorem exists_eq_algebraMap_C_of_forall_irreducible {K L : Type*} [Field K] [Field L]
    [Algebra K[X] L] [IsFractionRing K[X] L] (w : ∀ q : K[X], Irreducible q → L →*₀ WithZero (Multiplicative ℤ))
    (hw₁ : ∀ q (hq : Irreducible q) b, ¬ q ∣ b → w q hq (algebraMap K[X] L b) = 1)
    (hw₂ : ∀ q (hq : Irreducible q), w q hq (algebraMap K[X] L q) = WithZero.exp 1)
    {F : L} (hF : ∀ q (hq : Irreducible q), w q hq F = 1) :
    ∃ c : K, F = algebraMap K[X] L (C c) := by
  have hmult : ∀ q (hq : Irreducible q) (x : K[X]), x ≠ 0 →
      w q hq (algebraMap K[X] L x) = WithZero.exp (multiplicity q x : ℤ) := by
    intro q hq x hx
    obtain ⟨c, hc, hnd⟩ :=
      (FiniteMultiplicity.of_not_isUnit hq.not_isUnit hx).exists_eq_pow_mul_and_not_dvd
    conv_lhs => rw [hc]
    rw [map_mul, map_mul, map_pow, map_pow, hw₂ q hq, hw₁ q hq c hnd, mul_one, ← WithZero.exp_nsmul]
    simp
  suffices key : ∀ n : ℕ, ∀ a b : K[X], a ≠ 0 → b ≠ 0 → a.natDegree + b.natDegree ≤ n →
      F = algebraMap K[X] L a / algebraMap K[X] L b → ∃ c : K, F = algebraMap K[X] L (C c) by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := K[X]) F
    by_cases ha : a = 0
    · exact ⟨0, by simp [ha]⟩
    exact key _ a b ha (nonZeroDivisors.ne_zero hb) le_rfl rfl
  intro n
  induction n with
  | zero =>
    intro a b ha hb hdeg hF'
    have ha0 : a.natDegree = 0 := by omega
    have hb0 : b.natDegree = 0 := by omega
    rw [eq_C_of_natDegree_eq_zero ha0, eq_C_of_natDegree_eq_zero hb0] at hF'
    refine ⟨a.coeff 0 / b.coeff 0, ?_⟩
    rw [hF']
    exact (map_div₀ ((algebraMap K[X] L).comp C) _ _).symm
  | succ n ih =>
    intro a b ha hb hdeg hF'
    by_cases hdeg0 : a.natDegree + b.natDegree = 0
    · exact ih a b ha hb (by omega) hF'
    -- an irreducible factor of `a` or `b`
    obtain ⟨q, hq, hqab⟩ : ∃ q, Irreducible q ∧ (q ∣ a ∨ q ∣ b) := by
      by_cases hapos : 0 < a.natDegree
      · obtain ⟨q, hq, hqa⟩ := WfDvdMonoid.exists_irreducible_factor
          (Polynomial.not_isUnit_of_natDegree_pos a hapos) ha
        exact ⟨q, hq, Or.inl hqa⟩
      · obtain ⟨q, hq, hqb⟩ := WfDvdMonoid.exists_irreducible_factor
          (Polynomial.not_isUnit_of_natDegree_pos b (by omega)) hb
        exact ⟨q, hq, Or.inr hqb⟩
    have hab : multiplicity q a = multiplicity q b := by
      have h1 := hF q hq
      rw [hF', map_div₀, hmult q hq a ha, hmult q hq b hb, div_eq_one_iff_eq] at h1
      · exact_mod_cast WithZero.exp_injective h1
      · exact WithZero.exp_ne_zero
    have hqa : q ∣ a := by
      rcases hqab with h | h
      · exact h
      · rw [← multiplicity_ne_zero, hab, multiplicity_ne_zero]; exact h
    have hqb : q ∣ b := by
      rcases hqab with h | h
      · rw [← multiplicity_ne_zero, ← hab, multiplicity_ne_zero]; exact h
      · exact h
    obtain ⟨a', rfl⟩ := hqa
    obtain ⟨b', rfl⟩ := hqb
    have hq0 : q ≠ 0 := hq.ne_zero
    have ha' : a' ≠ 0 := right_ne_zero_of_mul ha
    have hb' : b' ≠ 0 := right_ne_zero_of_mul hb
    have hqL : algebraMap K[X] L q ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hq0)
    have hqdeg := Irreducible.natDegree_pos hq
    rw [natDegree_mul hq0 ha', natDegree_mul hq0 hb'] at hdeg
    refine ih a' b' ha' hb' (by omega) ?_
    rw [hF', map_mul, map_mul, mul_div_mul_left _ _ hqL]

end Hartshorne

namespace AlgebraicGeometry

open CategoryTheory Limits

universe u

/-- Regularity in codimension one of an affine scheme is the corresponding property of its
ring. -/
theorem isRegularInCodimensionOne_Spec_iff (R : CommRingCat.{u}) :
    (Spec R).IsRegularInCodimensionOne ↔ Hartshorne.RingIsRegularInCodimensionOne R := by
  constructor
  · intro h p hp hp1
    let x : Spec R := ⟨p, hp⟩
    have hx : Order.coheight x = 1 := by
      rw [← idealHeight_eq_coheight]
      exact hp1
    have := h x hx
    let _ : Algebra R ((Spec R).presheaf.stalk x) := StructureSheaf.stalkAlgebra R x
    have : IsLocalization.AtPrime ((Spec R).presheaf.stalk x) p :=
      StructureSheaf.IsLocalization.to_stalk R x
    exact IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv p.primeCompl
      ((Spec R).presheaf.stalk x) (Localization.AtPrime p)).toRingEquiv
  · intro h x hx
    have : x.asIdeal.IsPrime := x.isPrime
    have hx' : x.asIdeal.height = 1 := by
      rw [idealHeight_eq_coheight]
      exact hx
    have := h x.asIdeal hx'
    let _ : Algebra R ((Spec R).presheaf.stalk x) := StructureSheaf.stalkAlgebra R x
    have : IsLocalization.AtPrime ((Spec R).presheaf.stalk x) x.asIdeal :=
      StructureSheaf.IsLocalization.to_stalk R x
    exact IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv x.asIdeal.primeCompl
      (Localization.AtPrime x.asIdeal) ((Spec R).presheaf.stalk x)).toRingEquiv

/-- Regularity in codimension one restricts along open immersions. -/
theorem Scheme.IsRegularInCodimensionOne.of_isOpenImmersion {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    [IsOpenImmersion f] (hZ : Z.IsRegularInCodimensionOne) : Y.IsRegularInCodimensionOne := by
  intro y hy
  have hy' : Order.coheight (f.base y) = 1 := by
    rw [coheight_eq_of_isOpenImmersion]
    exact hy
  have := hZ _ hy'
  exact IsRegularLocalRing.of_ringEquiv (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv

/-- Regularity in codimension one can be checked on a family of open immersions covering the
scheme. -/
theorem Scheme.IsRegularInCodimensionOne.of_forall_exists_isOpenImmersion {Z : Scheme.{u}}
    (h : ∀ z : Z, ∃ (Y : Scheme.{u}) (f : Y ⟶ Z), IsOpenImmersion f ∧
      Y.IsRegularInCodimensionOne ∧ z ∈ Set.range f.base) :
    Z.IsRegularInCodimensionOne := by
  intro z hz
  obtain ⟨Y, f, hf, hY, y, rfl⟩ := h z
  have hy : Order.coheight y = 1 := by
    rw [← coheight_eq_of_isOpenImmersion f]
    exact hz
  have := hY y hy
  exact IsRegularLocalRing.of_ringEquiv (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv.symm

/-- The relative affine line over a locally Noetherian integral scheme that is regular in
codimension one is again regular in codimension one. -/
theorem Scheme.IsRegularInCodimensionOne.affineLine {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsIntegral X] (hX : X.IsRegularInCodimensionOne) :
    𝔸(PUnit.{u + 1}; X).IsRegularInCodimensionOne := by
  apply of_forall_exists_isOpenImmersion
  intro z
  obtain ⟨R, f, hf, ⟨u, hu⟩, -⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (show (𝔸(PUnit.{u + 1}; X) ↘ X).base z ∈ (⊤ : X.Opens) from trivial)
  have hRspec : (Spec R).IsRegularInCodimensionOne := hX.of_isOpenImmersion f
  have hR : Hartshorne.RingIsRegularInCodimensionOne R :=
    (isRegularInCodimensionOne_Spec_iff R).mp hRspec
  have : IsLocallyNoetherian (Spec R) := isLocallyNoetherian_of_isOpenImmersion f
  have : IsNoetherianRing R := isLocallyNoetherian_Spec.mp this
  have : Nonempty (Spec R) := ⟨u⟩
  have : IsIntegral (Spec R) := isIntegral_of_isOpenImmersion f
  have : IsDomain R := (affine_isIntegral_iff R).mp this
  have hpoly : Hartshorne.RingIsRegularInCodimensionOne (MvPolynomial PUnit.{u + 1} R) :=
    (Hartshorne.Polynomial.ringIsRegularInCodimensionOne hR).of_ringEquiv
      (MvPolynomial.uniqueAlgEquiv R PUnit.{u + 1}).toRingEquiv.symm
  have hA : (𝔸(PUnit.{u + 1}; Spec R)).IsRegularInCodimensionOne :=
    ((isRegularInCodimensionOne_Spec_iff (.of (MvPolynomial PUnit.{u + 1} R))).mpr hpoly).of_isOpenImmersion
      (AffineSpace.SpecIso PUnit.{u + 1} R).hom
  have hpb := AffineSpace.isPullback_map (n := PUnit.{u + 1}) f
  have : IsOpenImmersion (AffineSpace.map PUnit.{u + 1} f) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hpb.flip hf
  obtain ⟨w, hw, -⟩ := Scheme.exists_preimage_of_isPullback hpb z u hu.symm
  exact ⟨_, AffineSpace.map PUnit.{u + 1} f, inferInstance, hA, w, hw⟩

/-- **Hartshorne II.6, Proposition 6.6, first part.** If `X` satisfies `(*)`, so does the
relative affine line `X × Spec ℤ[t]`. -/
theorem Scheme.SatisfiesConditionStar.affineLine {X : Scheme.{u}}
    (hX : X.SatisfiesConditionStar) : 𝔸(PUnit.{u + 1}; X).SatisfiesConditionStar := by
  have := hX.isNoetherian
  have := hX.isIntegral
  have := hX.isSeparated
  refine ⟨?_, inferInstance, ?_, hX.isRegularInCodimensionOne.affineLine⟩
  · have : IsLocallyNoetherian 𝔸(PUnit.{u + 1}; X) :=
      LocallyOfFiniteType.isLocallyNoetherian (𝔸(PUnit.{u + 1}; X) ↘ X)
    have : CompactSpace 𝔸(PUnit.{u + 1}; X) :=
      QuasiCompact.compactSpace_of_compactSpace (𝔸(PUnit.{u + 1}; X) ↘ X)
    exact {}
  · exact ⟨by rw [← terminal.comp_from (𝔸(PUnit.{u + 1}; X) ↘ X)]; infer_instance⟩

/-- Affine charts of the relative affine line: every point of `X` lies in an affine open
`Spec R`, over which the relative affine line is `Spec R[t]`, with the projection given by
the inclusion of constants. -/
theorem exists_affineLine_chart (X : Scheme.{u}) (x : X) :
    ∃ (R : CommRingCat.{u}) (f : Spec R ⟶ X) (g : Spec (CommRingCat.of R[X]) ⟶ 𝔸(PUnit.{u + 1}; X)),
      IsOpenImmersion f ∧ x ∈ Set.range f.base ∧
      IsPullback g (Spec.map (CommRingCat.ofHom (C : R →+* R[X]))) (𝔸(PUnit.{u + 1}; X) ↘ X) f := by
  obtain ⟨R, f, hf, hx, -⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (show x ∈ (⊤ : X.Opens) from trivial)
  let e : MvPolynomial PUnit.{u + 1} R ≃+* R[X] :=
    (MvPolynomial.uniqueAlgEquiv R PUnit.{u + 1}).toRingEquiv
  let i : Spec (CommRingCat.of R[X]) ≅ 𝔸(PUnit.{u + 1}; Spec R) :=
    Scheme.Spec.mapIso e.toCommRingCatIso.op ≪≫ (AffineSpace.SpecIso PUnit.{u + 1} R).symm
  refine ⟨R, f, i.hom ≫ AffineSpace.map PUnit.{u + 1} f, hf, hx, ?_⟩
  refine IsPullback.paste_horiz (IsPullback.of_horiz_isIso (fst := i.hom) (g := 𝟙 (Spec R)) ⟨?_⟩)
    (AffineSpace.isPullback_map f)
  simp only [i, Iso.trans_hom, Iso.symm_hom, Category.assoc, AffineSpace.SpecIso_inv_over,
    Category.comp_id, Functor.mapIso_hom, Iso.op_hom, Scheme.Spec_map]
  rw [← Spec.map_comp]
  congr 1
  ext r
  simp [e]

section VerticalPoints

variable {X : Scheme.{u}}

/-- In an affine chart of the relative affine line, the chart map is an open immersion. -/
theorem isOpenImmersion_of_affineLine_chart {R : CommRingCat.{u}} {f : Spec R ⟶ X}
    {g : Spec (CommRingCat.of R[X]) ⟶ 𝔸(PUnit.{u + 1}; X)} (hf : IsOpenImmersion f)
    (pb : IsPullback g (Spec.map (CommRingCat.ofHom (C : R →+* R[X]))) (𝔸(PUnit.{u + 1}; X) ↘ X) f) :
    IsOpenImmersion g :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) pb.flip hf

/-- Coheights and images of points in an affine chart of the relative affine line. -/
theorem affineLine_chart_point {R : CommRingCat.{u}} {f : Spec R ⟶ X}
    {g : Spec (CommRingCat.of R[X]) ⟶ 𝔸(PUnit.{u + 1}; X)} (hf : IsOpenImmersion f)
    (pb : IsPullback g (Spec.map (CommRingCat.ofHom (C : R →+* R[X]))) (𝔸(PUnit.{u + 1}; X) ↘ X) f)
    (P : Spec (CommRingCat.of R[X])) :
    Order.coheight (g.base P) = P.asIdeal.height ∧
      (𝔸(PUnit.{u + 1}; X) ↘ X).base (g.base P) =
        f.base ((Spec.map (CommRingCat.ofHom (C : R →+* R[X]))).base P) ∧
      Order.coheight ((𝔸(PUnit.{u + 1}; X) ↘ X).base (g.base P)) = (P.asIdeal.comap C).height := by
  have := isOpenImmersion_of_affineLine_chart hf pb
  have hsq : (𝔸(PUnit.{u + 1}; X) ↘ X).base (g.base P) =
      f.base ((Spec.map (CommRingCat.ofHom (C : R →+* R[X]))).base P) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pb.w]
  refine ⟨?_, hsq, ?_⟩
  · rw [coheight_eq_of_isOpenImmersion, ← idealHeight_eq_coheight]
  · rw [hsq, coheight_eq_of_isOpenImmersion, ← idealHeight_eq_coheight]
    rfl

variable [IsLocallyNoetherian X]

/-- The projection of the relative affine line does not increase coheight. -/
theorem coheight_affineLine_proj_le (z : 𝔸(PUnit.{u + 1}; X)) :
    Order.coheight ((𝔸(PUnit.{u + 1}; X) ↘ X).base z) ≤ Order.coheight z := by
  obtain ⟨R, f, g, hf, ⟨u, hu⟩, pb⟩ := exists_affineLine_chart X ((𝔸(PUnit.{u + 1}; X) ↘ X).base z)
  obtain ⟨P, hP, -⟩ := Scheme.exists_preimage_of_isPullback pb z u hu.symm
  have : IsLocallyNoetherian (Spec R) := isLocallyNoetherian_of_isOpenImmersion f
  have : IsNoetherianRing R := isLocallyNoetherian_Spec.mp this
  obtain ⟨h1, -, h3⟩ := affineLine_chart_point hf pb P
  rw [← hP, h1, h3]
  have : P.asIdeal.IsPrime := P.isPrime
  exact Hartshorne.height_comap_C_le P.asIdeal

/-- Two points of the relative affine line over the same point `x`, both with the coheight
of `x`, coincide. -/
theorem affineLine_eq_of_coheight_eq {z₁ z₂ : 𝔸(PUnit.{u + 1}; X)}
    (h : (𝔸(PUnit.{u + 1}; X) ↘ X).base z₁ = (𝔸(PUnit.{u + 1}; X) ↘ X).base z₂)
    (h₁ : Order.coheight z₁ = Order.coheight ((𝔸(PUnit.{u + 1}; X) ↘ X).base z₁))
    (h₂ : Order.coheight z₂ = Order.coheight ((𝔸(PUnit.{u + 1}; X) ↘ X).base z₂)) :
    z₁ = z₂ := by
  obtain ⟨R, f, g, hf, ⟨u, hu⟩, pb⟩ :=
    exists_affineLine_chart X ((𝔸(PUnit.{u + 1}; X) ↘ X).base z₁)
  have : IsOpenImmersion g := isOpenImmersion_of_affineLine_chart hf pb
  obtain ⟨P₁, hP₁, hu₁⟩ := Scheme.exists_preimage_of_isPullback pb z₁ u hu.symm
  obtain ⟨P₂, hP₂, hu₂⟩ := Scheme.exists_preimage_of_isPullback pb z₂ u (hu.trans h).symm
  have : IsLocallyNoetherian (Spec R) := isLocallyNoetherian_of_isOpenImmersion f
  have : IsNoetherianRing R := isLocallyNoetherian_Spec.mp this
  have : P₁.asIdeal.IsPrime := P₁.isPrime
  have : P₂.asIdeal.IsPrime := P₂.isPrime
  obtain ⟨a₁, -, c₁⟩ := affineLine_chart_point hf pb P₁
  obtain ⟨a₂, -, c₂⟩ := affineLine_chart_point hf pb P₂
  subst hP₁ hP₂
  rw [a₁, c₁] at h₁
  rw [a₂, c₂] at h₂
  have e₁ := (Hartshorne.height_eq_height_comap_C_iff P₁.asIdeal).mp h₁
  have e₂ := (Hartshorne.height_eq_height_comap_C_iff P₂.asIdeal).mp h₂
  have hc : P₁.asIdeal.comap C = P₂.asIdeal.comap C := by
    have := hu₁.trans hu₂.symm
    exact congrArg PrimeSpectrum.asIdeal this
  congr 1
  apply PrimeSpectrum.ext
  rw [e₁, e₂, hc]

/-- Every point `x` of `X` has a point of the relative affine line over it with the same
coheight: the generic point of the fibre over `x`. -/
theorem exists_affineLine_coheight_eq (x : X) :
    ∃ z : 𝔸(PUnit.{u + 1}; X), (𝔸(PUnit.{u + 1}; X) ↘ X).base z = x ∧
      Order.coheight z = Order.coheight x := by
  obtain ⟨R, f, g, hf, ⟨u, rfl⟩, pb⟩ := exists_affineLine_chart X x
  have : IsLocallyNoetherian (Spec R) := isLocallyNoetherian_of_isOpenImmersion f
  have : IsNoetherianRing R := isLocallyNoetherian_Spec.mp this
  have : u.asIdeal.IsPrime := u.isPrime
  let P : Spec (CommRingCat.of R[X]) :=
    ⟨u.asIdeal.map C, Ideal.isPrime_map_C_of_isPrime⟩
  have hPu : (Spec.map (CommRingCat.ofHom (C : R →+* R[X]))).base P = u := by
    apply PrimeSpectrum.ext
    exact Hartshorne.comap_C_map_C u.asIdeal
  obtain ⟨a, b, c⟩ := affineLine_chart_point hf pb P
  refine ⟨g.base P, by rw [b, hPu], ?_⟩
  rw [a, coheight_eq_of_isOpenImmersion, ← idealHeight_eq_coheight]
  have hP : P.asIdeal = (P.asIdeal.comap C).map C := by
    change u.asIdeal.map C = ((u.asIdeal.map C).comap C).map C
    rw [Hartshorne.comap_C_map_C]
  have : P.asIdeal.IsPrime := P.isPrime
  rw [(Hartshorne.height_eq_height_comap_C_iff P.asIdeal).mpr hP]
  exact congrArg (fun I => I.height) (Hartshorne.comap_C_map_C u.asIdeal)

end VerticalPoints

section Pullback

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- The generic point of the fibre of the relative affine line over `x`; it is the unique point
over `x` with the same coheight as `x`. -/
noncomputable def Scheme.affineLineFibreGenericPoint (x : X) : 𝔸(PUnit.{u + 1}; X) :=
  (exists_affineLine_coheight_eq x).choose

theorem Scheme.affineLineFibreGenericPoint_spec (x : X) :
    (𝔸(PUnit.{u + 1}; X) ↘ X).base (X.affineLineFibreGenericPoint x) = x ∧
      Order.coheight (X.affineLineFibreGenericPoint x) = Order.coheight x :=
  (exists_affineLine_coheight_eq x).choose_spec

/-- A point of the relative affine line with the same coheight as its image is the generic
point of its fibre. -/
theorem Scheme.eq_affineLineFibreGenericPoint {z : 𝔸(PUnit.{u + 1}; X)}
    (hz : Order.coheight z = Order.coheight ((𝔸(PUnit.{u + 1}; X) ↘ X).base z)) :
    z = X.affineLineFibreGenericPoint ((𝔸(PUnit.{u + 1}; X) ↘ X).base z) := by
  have hs := X.affineLineFibreGenericPoint_spec ((𝔸(PUnit.{u + 1}; X) ↘ X).base z)
  refine affineLine_eq_of_coheight_eq hs.1.symm hz ?_
  rw [hs.1, hs.2]

end Pullback

section PullbackDivisor

variable (X : Scheme.{u}) [IsNoetherian X]

private noncomputable def affineLinePullbackFun (D : X.WeilDivisor) :
    𝔸(PUnit.{u + 1}; X).WeilDivisor := by
  classical
  let coeff : 𝔸(PUnit.{u + 1}; X) → ℤ := fun z ↦
    if Order.coheight z = 1 then D.1 ((𝔸(PUnit.{u + 1}; X) ↘ X).base z) else 0
  have hfin : coeff.support.Finite := by
    refine ((Scheme.WeilDivisor.support_finite D).image
      X.affineLineFibreGenericPoint).subset ?_
    intro z hz
    simp only [Function.mem_support, coeff, ne_eq, ite_eq_right_iff, not_forall] at hz
    obtain ⟨hz1, hD⟩ := hz
    have hx1 : Order.coheight ((𝔸(PUnit.{u + 1}; X) ↘ X).base z) = 1 := by
      by_contra h
      exact hD (D.2 _ h)
    refine ⟨(𝔸(PUnit.{u + 1}; X) ↘ X).base z, hD, ?_⟩
    exact (X.eq_affineLineFibreGenericPoint (hz1.trans hx1.symm)).symm
  let E : AlgebraicCycle 𝔸(PUnit.{u + 1}; X) ℤ :=
    { toFun := coeff
      supportWithinDomain' := Set.subset_univ _
      supportLocallyFiniteWithinDomain' := fun _ _ ↦
        ⟨Set.univ, Filter.univ_mem, by simpa using hfin⟩ }
  refine ⟨E, ?_⟩
  intro z hz
  change coeff z = 0
  simp [coeff, hz]

/-- **Pullback of Weil divisors along the projection `𝔸¹_X → X`.** A prime divisor `Y` with
generic point `x` pulls back to the prime divisor `Y × 𝔸¹`, whose generic point is the generic
point of the fibre over `x`. -/
noncomputable def Scheme.affineLinePullback : X.WeilDivisor →+ 𝔸(PUnit.{u + 1}; X).WeilDivisor where
  toFun := affineLinePullbackFun X
  map_zero' := by
    apply Subtype.ext
    apply Function.locallyFinsuppWithin.ext
    intro z
    change (if Order.coheight z = 1 then (0 : X.WeilDivisor).1 _ else 0) = 0
    split_ifs <;> rfl
  map_add' D E := by
    apply Subtype.ext
    apply Function.locallyFinsuppWithin.ext
    intro z
    change (if Order.coheight z = 1 then (D + E).1 _ else 0) =
      (if Order.coheight z = 1 then D.1 _ else 0) + (if Order.coheight z = 1 then E.1 _ else 0)
    split_ifs <;> simp

variable {X}

theorem Scheme.affineLinePullback_apply (D : X.WeilDivisor) (z : 𝔸(PUnit.{u + 1}; X)) :
    (X.affineLinePullback D).1 z =
      if Order.coheight z = 1 then D.1 ((𝔸(PUnit.{u + 1}; X) ↘ X).base z) else 0 := by
  classical
  rfl

theorem Scheme.affineLinePullback_apply_fibreGenericPoint (D : X.WeilDivisor) {x : X}
    (hx : Order.coheight x = 1) :
    (X.affineLinePullback D).1 (X.affineLineFibreGenericPoint x) = D.1 x := by
  have hs := X.affineLineFibreGenericPoint_spec x
  rw [Scheme.affineLinePullback_apply, if_pos (hs.2.trans hx), hs.1]

/-- Pullback of Weil divisors along `𝔸¹_X → X` is injective. -/
theorem Scheme.affineLinePullback_injective : Function.Injective X.affineLinePullback := by
  rw [injective_iff_map_eq_zero]
  intro D hD
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro x
  by_cases hx : Order.coheight x = 1
  · rw [← Scheme.affineLinePullback_apply_fibreGenericPoint D hx, hD]
    rfl
  · exact D.2 x hx

end PullbackDivisor

section GenericFunctionFieldMap

variable {U V Y : Scheme.{u}} [IsIntegral U] [IsIntegral V] [IsIntegral Y]

/-- Pullback of rational functions along a morphism of integral schemes that sends the generic
point to the generic point. -/
noncomputable def Scheme.Hom.genericFunctionFieldMap (φ : V ⟶ Y)
    (h : φ.base (genericPoint V) = genericPoint Y) : Y.functionField ⟶ V.functionField :=
  Y.presheaf.stalkSpecializes (Inseparable.of_eq h).specializes ≫ φ.stalkMap (genericPoint V)

/-- Pullback of rational functions is compatible with the stalk maps. -/
theorem Scheme.Hom.genericFunctionFieldMap_algebraMap (φ : V ⟶ Y)
    (h : φ.base (genericPoint V) = genericPoint Y) (v : V) (r : Y.presheaf.stalk (φ.base v)) :
    φ.genericFunctionFieldMap h (algebraMap _ Y.functionField r) =
      algebraMap _ V.functionField (φ.stalkMap v r) := by
  have key : Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes (Set.mem_univ _) :
        genericPoint Y ⤳ φ.base v) ≫ φ.genericFunctionFieldMap h =
      φ.stalkMap v ≫ V.presheaf.stalkSpecializes
        ((genericPoint_spec V).specializes (Set.mem_univ _)) := by
    rw [Scheme.Hom.genericFunctionFieldMap, TopCat.Presheaf.stalkSpecializes_comp_assoc,
      Scheme.Hom.stalkSpecializes_stalkMap]
  exact ConcreteCategory.congr_hom key r

/-- Pullback of rational functions is functorial. -/
theorem Scheme.Hom.genericFunctionFieldMap_comp (a : U ⟶ V) (b : V ⟶ Y)
    (ha : a.base (genericPoint U) = genericPoint V) (hb : b.base (genericPoint V) = genericPoint Y)
    (hab : (a ≫ b).base (genericPoint U) = genericPoint Y) :
    (a ≫ b).genericFunctionFieldMap hab = b.genericFunctionFieldMap hb ≫ a.genericFunctionFieldMap ha := by
  rw [Scheme.Hom.genericFunctionFieldMap, Scheme.Hom.genericFunctionFieldMap,
    Scheme.Hom.genericFunctionFieldMap, Scheme.Hom.stalkMap_comp]
  have hsp : a.base (genericPoint U) ⤳ genericPoint V := (Inseparable.of_eq ha).specializes
  rw [Category.assoc, ← Scheme.Hom.stalkSpecializes_stalkMap_assoc b _ _ hsp,
    TopCat.Presheaf.stalkSpecializes_comp_assoc]
  rfl

/-- Pullback of rational functions only depends on the morphism. -/
theorem Scheme.Hom.genericFunctionFieldMap_congr {a b : V ⟶ Y} (hab : a = b)
    (ha : a.base (genericPoint V) = genericPoint Y) (hb : b.base (genericPoint V) = genericPoint Y) :
    a.genericFunctionFieldMap ha = b.genericFunctionFieldMap hb := by
  subst hab
  rfl

/-- If the maximal ideal of the stalk at the image generates the maximal ideal of the stalk at a
codimension-one point, pullback of rational functions preserves order of vanishing. -/
theorem Scheme.ord_genericFunctionFieldMap {V Y : Scheme.{u}} [IsNoetherian V] [IsIntegral V]
    [IsNoetherian Y] [IsIntegral Y] (hV : V.SatisfiesConditionStar)
    (hY : Y.SatisfiesConditionStar) (φ : V ⟶ Y) (h : φ.base (genericPoint V) = genericPoint Y)
    {v : V} (hv : Order.coheight v = 1) (hy : Order.coheight (φ.base v) = 1)
    (hm : (maximalIdeal (Y.presheaf.stalk (φ.base v))).map (φ.stalkMap v).hom =
      maximalIdeal (V.presheaf.stalk v)) (F : Y.functionField) :
    Scheme.ord (φ.genericFunctionFieldMap h F) v = Scheme.ord F (φ.base v) := by
  let _ : IsDiscreteValuationRing (Y.presheaf.stalk (φ.base v)) :=
    Y.codimensionOneStalk_isDiscreteValuationRing hY hy
  let _ : IsDiscreteValuationRing (V.presheaf.stalk v) :=
    V.codimensionOneStalk_isDiscreteValuationRing hV hv
  rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hv, Scheme.ord_eq_ordHom_of_coheight_eq_one hy]
  congr 2
  exact Hartshorne.ordFrac_map_of_map_maximalIdeal_eq (φ.stalkMap v).hom
    (φ.genericFunctionFieldMap h).hom (φ.genericFunctionFieldMap_algebraMap h v) hm F

/-- Open immersions satisfy the maximal-ideal condition. -/
theorem Scheme.Hom.map_maximalIdeal_stalkMap_of_isOpenImmersion {V Y : Scheme.{u}} (φ : V ⟶ Y)
    [IsOpenImmersion φ] (v : V) :
    (maximalIdeal (Y.presheaf.stalk (φ.base v))).map (φ.stalkMap v).hom =
      maximalIdeal (V.presheaf.stalk v) :=
  map_ringEquiv_maximalIdeal (asIso (φ.stalkMap v)).commRingCatIsoToRingEquiv

end GenericFunctionFieldMap

section FunctionField

variable (X : Scheme.{u}) [IsIntegral X]

/-- The projection of the relative affine line sends the generic point to the generic point. -/
theorem affineLine_proj_genericPoint :
    (𝔸(PUnit.{u + 1}; X) ↘ X).base (genericPoint 𝔸(PUnit.{u + 1}; X)) = genericPoint X := by
  have h := (genericPoint_spec 𝔸(PUnit.{u + 1}; X)).image (𝔸(PUnit.{u + 1}; X) ↘ X).continuous
  rw [Set.image_univ, (𝔸(PUnit.{u + 1}; X) ↘ X).surjective.range_eq, closure_univ] at h
  exact h.eq (genericPoint_spec X)

/-- Pullback of rational functions along the projection `𝔸¹_X → X`. -/
noncomputable def Scheme.affineLineFunctionFieldMap :
    X.functionField ⟶ 𝔸(PUnit.{u + 1}; X).functionField :=
  (𝔸(PUnit.{u + 1}; X) ↘ X).genericFunctionFieldMap (affineLine_proj_genericPoint X)

variable {X}

/-- Pullback of rational functions is compatible with the stalk maps of the projection. -/
theorem Scheme.affineLineFunctionFieldMap_algebraMap (z : 𝔸(PUnit.{u + 1}; X))
    (r : X.presheaf.stalk ((𝔸(PUnit.{u + 1}; X) ↘ X).base z)) :
    X.affineLineFunctionFieldMap (algebraMap _ X.functionField r) =
      algebraMap _ 𝔸(PUnit.{u + 1}; X).functionField
        ((𝔸(PUnit.{u + 1}; X) ↘ X).stalkMap z r) :=
  (𝔸(PUnit.{u + 1}; X) ↘ X).genericFunctionFieldMap_algebraMap _ z r

end FunctionField

section MaximalIdeal

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- At the generic point of a fibre of `𝔸¹_X → X`, the maximal ideal of the base stalk generates
the maximal ideal of the stalk. -/
theorem affineLine_map_maximalIdeal_stalk {z : 𝔸(PUnit.{u + 1}; X)}
    (hz : Order.coheight z = Order.coheight ((𝔸(PUnit.{u + 1}; X) ↘ X).base z)) :
    (maximalIdeal (X.presheaf.stalk ((𝔸(PUnit.{u + 1}; X) ↘ X).base z))).map
        ((𝔸(PUnit.{u + 1}; X) ↘ X).stalkMap z).hom =
      maximalIdeal (𝔸(PUnit.{u + 1}; X).presheaf.stalk z) := by
  obtain ⟨R, f, g, hf, ⟨u, hu⟩, pb⟩ :=
    exists_affineLine_chart X ((𝔸(PUnit.{u + 1}; X) ↘ X).base z)
  have : IsOpenImmersion g := isOpenImmersion_of_affineLine_chart hf pb
  obtain ⟨P, rfl, rfl⟩ := Scheme.exists_preimage_of_isPullback pb z u hu.symm
  have : IsLocallyNoetherian (Spec R) := isLocallyNoetherian_of_isOpenImmersion f
  have : IsNoetherianRing R := isLocallyNoetherian_Spec.mp this
  have : P.asIdeal.IsPrime := P.isPrime
  obtain ⟨a, -, c⟩ := affineLine_chart_point hf pb P
  rw [a, c] at hz
  have hP := (Hartshorne.height_eq_height_comap_C_iff P.asIdeal).mp hz
  set h := Spec.map (CommRingCat.ofHom (C : R →+* R[X]))
  set π := 𝔸(PUnit.{u + 1}; X) ↘ X
  have hpt : π.base (g.base P) = f.base (h.base P) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pb.w]
  -- the stalk maps around the chart square
  have hsq : π.stalkMap (g.base P) ≫ g.stalkMap P =
      (X.presheaf.stalkCongr (.of_eq hpt)).hom ≫ f.stalkMap (h.base P) ≫ h.stalkMap P := by
    rw [← Scheme.Hom.stalkMap_comp, ← Scheme.Hom.stalkMap_comp,
      Scheme.Hom.stalkMap_congr_hom _ _ pb.w]
    rfl
  have hspec := Scheme.localRingHom_comp_stalkIso (CommRingCat.ofHom (C : R →+* R[X])) P
  rw [← Hartshorne.map_maximalIdeal_ringEquiv_comp_iff _
    (asIso (g.stalkMap P)).commRingCatIsoToRingEquiv]
  have e1 : ((asIso (g.stalkMap P)).commRingCatIsoToRingEquiv : _ →+* _).comp
      (π.stalkMap (g.base P)).hom = (π.stalkMap (g.base P) ≫ g.stalkMap P).hom := rfl
  rw [e1, hsq]
  have e2 : ((X.presheaf.stalkCongr (.of_eq hpt)).hom ≫ f.stalkMap (h.base P) ≫ h.stalkMap P).hom =
      (h.stalkMap P).hom.comp ((X.presheaf.stalkCongr (.of_eq hpt) ≪≫ asIso (f.stalkMap (h.base P))).commRingCatIsoToRingEquiv :
        _ →+* _) := rfl
  rw [e2, Hartshorne.map_maximalIdeal_comp_ringEquiv, ← hspec]
  refine (Hartshorne.map_maximalIdeal_iso_comp_iff _ _ _).mpr ?_
  exact Hartshorne.map_maximalIdeal_localRingHom_C _ _ hP rfl

end MaximalIdeal

section Ord

/-- The relative affine line over a locally Noetherian scheme is locally Noetherian. -/
instance AffineSpace.isLocallyNoetherian_pUnit {X : Scheme.{u}} [IsLocallyNoetherian X] :
    IsLocallyNoetherian 𝔸(PUnit.{u + 1}; X) :=
  LocallyOfFiniteType.isLocallyNoetherian (𝔸(PUnit.{u + 1}; X) ↘ X)

/-- On an integral scheme, a point of coheight zero is the generic point. -/
theorem eq_genericPoint_of_coheight_eq_zero {X : Scheme.{u}} [IsIntegral X] {x : X}
    (hx : Order.coheight x = 0) : x = genericPoint X := by
  have h1 : (⊤ : X) ≤ x := Order.coheight_eq_zero.mp hx le_top
  exact ((show x ⤳ genericPoint X from h1).antisymm (genericPoint_specializes x)).eq

private theorem surjective_algebraMap_stalk_of_eq_genericPoint {X : Scheme.{u}} [IsIntegral X]
    {x : X} (hx : x = genericPoint X) :
    Function.Surjective (algebraMap (X.presheaf.stalk x) X.functionField) := by
  subst hx
  intro f
  refine ⟨f, ?_⟩
  change (X.presheaf.stalkSpecializes _).hom f = f
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  rfl

variable {X : Scheme.{u}} [IsNoetherian X] [IsIntegral X] (hX : X.SatisfiesConditionStar)
include hX

/-- Along a vertical prime divisor, pulling back a rational function preserves its order. -/
theorem Scheme.ord_affineLineFunctionFieldMap_of_coheight_eq_one {z : 𝔸(PUnit.{u + 1}; X)}
    (hz : Order.coheight z = 1)
    (hx : Order.coheight ((𝔸(PUnit.{u + 1}; X) ↘ X).base z) = 1) (f : X.functionField) :
    Scheme.ord (X.affineLineFunctionFieldMap f) z =
      Scheme.ord f ((𝔸(PUnit.{u + 1}; X) ↘ X).base z) := by
  have hY := hX.affineLine
  have : IsNoetherian 𝔸(PUnit.{u + 1}; X) := hY.isNoetherian
  let _ : IsDiscreteValuationRing (X.presheaf.stalk ((𝔸(PUnit.{u + 1}; X) ↘ X).base z)) :=
    X.codimensionOneStalk_isDiscreteValuationRing hX hx
  let _ : IsDiscreteValuationRing (𝔸(PUnit.{u + 1}; X).presheaf.stalk z) :=
    𝔸(PUnit.{u + 1}; X).codimensionOneStalk_isDiscreteValuationRing hY hz
  rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hz, Scheme.ord_eq_ordHom_of_coheight_eq_one hx]
  congr 2
  exact Hartshorne.ordFrac_map_of_map_maximalIdeal_eq ((𝔸(PUnit.{u + 1}; X) ↘ X).stalkMap z).hom
    X.affineLineFunctionFieldMap.hom (Scheme.affineLineFunctionFieldMap_algebraMap z)
    (affineLine_map_maximalIdeal_stalk (hz.trans hx.symm)) f

/-- Along a horizontal prime divisor, the pullback of a nonzero rational function has order
zero. -/
theorem Scheme.ord_affineLineFunctionFieldMap_of_eq_genericPoint {z : 𝔸(PUnit.{u + 1}; X)}
    (hz : Order.coheight z = 1)
    (hx : (𝔸(PUnit.{u + 1}; X) ↘ X).base z = (letI := hX.isIntegral; genericPoint X))
    {f : X.functionField} (hf : f ≠ 0) :
    Scheme.ord (X.affineLineFunctionFieldMap f) z = 0 := by
  have hY := hX.affineLine
  have : IsNoetherian 𝔸(PUnit.{u + 1}; X) := hY.isNoetherian
  have hinj : Function.Injective
      (algebraMap (X.presheaf.stalk ((𝔸(PUnit.{u + 1}; X) ↘ X).base z)) X.functionField) :=
    IsFractionRing.injective _ _
  have hbij := And.intro hinj (surjective_algebraMap_stalk_of_eq_genericPoint hx)
  let e := RingEquiv.ofBijective _ hbij
  obtain ⟨r, rfl⟩ := hbij.2 f
  have hr : IsUnit r := by
    have : IsUnit (e r) := (Ne.isUnit hf)
    simpa using this.map e.symm
  rw [Scheme.affineLineFunctionFieldMap_algebraMap, Scheme.ord_eq_ordHom_of_coheight_eq_one hz]
  have : Ring.KrullDimLE 1 (𝔸(PUnit.{u + 1}; X).presheaf.stalk z) :=
    krullDimLE_of_coheight_le hz.le
  unfold Scheme.ordHom
  rw [Ring.ordFrac_of_isUnit (hr.map _)]
  rfl

end Ord

section ClassGroupMap

variable {X : Scheme.{u}}

/-- The pullback of the principal divisor of `f` is the principal divisor of the pullback of
`f`. -/
theorem Scheme.affineLinePullback_principalDivisor [IsNoetherian X] [IsIntegral X]
    (hX : X.SatisfiesConditionStar) (f : X.functionFieldˣ) :
    X.affineLinePullback (X.principalDivisor hX f) =
      𝔸(PUnit.{u + 1}; X).principalDivisor hX.affineLine
        (Units.map X.affineLineFunctionFieldMap.hom.toMonoidHom f) := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro z
  rw [Scheme.affineLinePullback_apply]
  change (if Order.coheight z = 1 then
      Scheme.ord (f : X.functionField) ((𝔸(PUnit.{u + 1}; X) ↘ X).base z) else 0) =
    Scheme.ord (X.affineLineFunctionFieldMap (f : X.functionField)) z
  split_ifs with hz
  · by_cases hx : Order.coheight ((𝔸(PUnit.{u + 1}; X) ↘ X).base z) = 1
    · rw [Scheme.ord_affineLineFunctionFieldMap_of_coheight_eq_one hX hz hx]
    · have hlt : Order.coheight ((𝔸(PUnit.{u + 1}; X) ↘ X).base z) < 1 :=
        lt_of_le_of_ne ((coheight_affineLine_proj_le z).trans hz.le) hx
      rw [Scheme.ord_eq_zero_of_coheight_neq_one hx,
        Scheme.ord_affineLineFunctionFieldMap_of_eq_genericPoint hX hz
          (eq_genericPoint_of_coheight_eq_zero (Order.lt_one_iff.mp hlt)) f.ne_zero]
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one hz]

/-- **Hartshorne II.6, Proposition 6.6, the map.** Pullback along the projection `𝔸¹_X → X`
induces a homomorphism of Weil divisor class groups `Cl X → Cl (𝔸¹_X)`. -/
noncomputable def Scheme.affineLineClassGroupHom (hX : X.SatisfiesConditionStar) :
    X.WeilClassGroup hX →+ 𝔸(PUnit.{u + 1}; X).WeilClassGroup hX.affineLine := by
  let _ : IsNoetherian X := hX.isNoetherian
  let _ : IsIntegral X := hX.isIntegral
  refine QuotientAddGroup.map _ _ X.affineLinePullback ?_
  rintro D ⟨f, rfl⟩
  exact ⟨Additive.ofMul (Units.map X.affineLineFunctionFieldMap.hom.toMonoidHom f.toMul),
    (X.affineLinePullback_principalDivisor hX f.toMul).symm⟩

/-- The class-group map sends the class of `D` to the class of its pullback. -/
theorem Scheme.affineLineClassGroupHom_weilDivisorClassHom (hX : X.SatisfiesConditionStar)
    (D : X.WeilDivisor) :
    let _ : IsNoetherian X := hX.isNoetherian
    X.affineLineClassGroupHom hX (X.weilDivisorClassHom hX D) =
      𝔸(PUnit.{u + 1}; X).weilDivisorClassHom hX.affineLine (X.affineLinePullback D) :=
  rfl

end ClassGroupMap

end AlgebraicGeometry

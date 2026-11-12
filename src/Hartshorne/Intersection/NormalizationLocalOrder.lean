/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.NormalizationOrderLength
import Hartshorne.Scheme.PrincipalDivisor
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.RamificationInertia.Inertia

/-!
# Lengths at a prime via the primes of the normalization lying over it

Let `D` be a Noetherian domain with fraction field `K` whose integral closure `O` in `K` is a
finite `D`-module, and let `Q` be a prime of `D` with `dim D_Q = 1`. For `a ≠ 0` in `D`,
`ℓ_{D_Q}(D_Q / a) = ∑_𝔔 ord_{O_𝔔}(a) [κ(𝔔) : κ(Q)]`, the sum running over the primes `𝔔` of
`O` lying over `Q` (`length_quotient_eq_finsum_primesOver`).

This is the length formula for orders through the normalization
(`Hartshorne.NormalizationOrderLength.length_quotient_eq_finsum_ord_mul_inertiaDeg`) applied to
the one-dimensional local ring `D_Q`, whose integral closure `B` in `K` is the localization of
`O` at `D ∖ Q` (`IsLocalization.integralClosure`). The maximal ideals of `B` correspond to the
primes of `O` over `Q`, with `B_𝔪 ≅ O_𝔔`, and inertia degrees agree because localizations have
inertia degree one (`inertiaDeg_eq_one_of_isLocalization`).
-/

universe u

open IsLocalRing

namespace Hartshorne.NormalizationLocalOrder

section Localization

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- A prime of a localization `S` of `R` has inertia degree one over `R`. -/
theorem inertiaDeg_eq_one_of_isLocalization (M : Submonoid R) [IsLocalization M S]
    (q : Ideal S) [q.IsPrime] : q.inertiaDeg R = 1 := by
  let p := q.under R
  let _ := Localization.AtPrime.algebraOfLiesOver p q
  rw [Ideal.inertiaDeg_eq p q]
  have : IsLocalization.AtPrime (Localization.AtPrime q) p :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M (Localization.AtPrime q) q
  let e := IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p) (Localization.AtPrime q)
  have he : (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) = e.toRingHom := by
    apply IsLocalization.ringHom_ext p.primeCompl
    ext r
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [← IsScalarTower.algebraMap_apply R (Localization.AtPrime p) (Localization.AtPrime q)]
    exact (e.commutes r).symm
  have hres : Function.Bijective (algebraMap p.ResidueField q.ResidueField) := by
    let e' := ResidueField.mapEquiv e.toRingEquiv
    have : ⇑(algebraMap p.ResidueField q.ResidueField) = ⇑e' := by
      funext x
      obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective (R := Localization.AtPrime p) x
      change residue _ (algebraMap _ _ x) = residue _ (e x)
      rw [he]
      rfl
    rw [this]
    exact e'.bijective
  exact Module.finrank_of_bijective_algebraMap hres

/-- Orders at a prime of a localization `S` of `R` agree with orders at its contraction. -/
theorem ring_ord_localization_atPrime_eq (M : Submonoid R) [IsLocalization M S] (m : Ideal S)
    [m.IsPrime] (x : R) :
    Ring.ord (Localization.AtPrime m) (algebraMap R _ x) =
      Ring.ord (Localization.AtPrime (m.comap (algebraMap R S))) (algebraMap R _ x) := by
  have : IsLocalization.AtPrime (Localization.AtPrime m) (m.comap (algebraMap R S)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M (Localization.AtPrime m) m
  let e := IsLocalization.algEquiv (m.comap (algebraMap R S)).primeCompl (Localization.AtPrime m)
    (Localization.AtPrime (m.comap (algebraMap R S)))
  rw [← ring_ord_ringEquiv e.toRingEquiv]
  exact congrArg _ (e.commutes x)

/-- Inertia degrees in a localized extension: if `A` is the localization of `D` at `M` and `B`
the localization of a `D`-algebra `O` at the image of `M`, then a prime `𝔪` of `B` has the same
inertia degree over `A` as its contraction to `O` over `D`. -/
theorem inertiaDeg_eq_of_isLocalization {D O A B : Type*} [CommRing D] [CommRing O] [CommRing A]
    [CommRing B] [Algebra D O] [Algebra D A] [Algebra D B] [Algebra O B] [Algebra A B]
    [IsScalarTower D O B] [IsScalarTower D A B] (M : Submonoid D) [IsLocalization M A]
    [IsLocalization (Algebra.algebraMapSubmonoid O M) B] (m : Ideal B) [m.IsPrime] :
    m.inertiaDeg A = (m.comap (algebraMap O B)).inertiaDeg D := by
  have h1 := Ideal.inertiaDeg_tower (R := D) (S := O) (T := B) (m.under O) m
  have h2 := Ideal.inertiaDeg_tower (R := D) (S := A) (T := B) (m.under A) m
  have : (m.under A).IsPrime := Ideal.IsPrime.under A m
  rw [inertiaDeg_eq_one_of_isLocalization (Algebra.algebraMapSubmonoid O M) m, mul_one] at h1
  rw [inertiaDeg_eq_one_of_isLocalization M (m.under A), one_mul] at h2
  rw [← h2, h1]

end Localization

variable {D : Type u} [CommRing D] [IsDomain D] [IsNoetherianRing D] (Q : Ideal D) [Q.IsPrime]

/-- **Lengths at a prime via the normalization.** Let `D` be a Noetherian domain whose integral
closure `O` in its fraction field is a finite `D`-module, and `Q` a prime with `dim D_Q = 1`.
For `a ≠ 0` in `D`, `ℓ_{D_Q}(D_Q / a) = ∑_𝔔 ord_{O_𝔔}(a) [κ(𝔔) : κ(Q)]` over the primes `𝔔` of
`O` lying over `Q`. -/
theorem length_quotient_eq_finsum_primesOver (hQ : ringKrullDim (Localization.AtPrime Q) = 1)
    [Module.Finite D (integralClosure D (FractionRing D))] {a : D} (ha : a ≠ 0) :
    Module.length (Localization.AtPrime Q)
        (Localization.AtPrime Q ⧸ Ideal.span {algebraMap D (Localization.AtPrime Q) a}) =
      ∑ᶠ 𝔔 ∈ {𝔔 : PrimeSpectrum (integralClosure D (FractionRing D)) |
          𝔔.asIdeal.comap (algebraMap D _) = Q},
        Ring.ord (Localization.AtPrime 𝔔.asIdeal) (algebraMap D _ a) *
          (𝔔.asIdeal.inertiaDeg D : ℕ∞) := by
  classical
  let K := FractionRing D
  let A := Localization.AtPrime Q
  let O := integralClosure D K
  let φAK := Localization.mapToFractionRing K Q.primeCompl A Q.primeCompl_le_nonZeroDivisors
  let _ : Algebra A K := φAK.toRingHom.toAlgebra
  have : IsScalarTower D A K := IsScalarTower.of_algebraMap_eq fun d ↦ (φAK.commutes d).symm
  have : IsFractionRing A K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization Q.primeCompl A K
  let B := integralClosure A K
  -- the inclusion `O → B`
  let ι : O →+* B :=
    { toFun := fun x ↦ ⟨x, IsIntegral.tower_top (A := A) x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  let _ : Algebra O B := ι.toAlgebra
  have : IsScalarTower O B K := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower D O B := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower D A B := IsScalarTower.of_algebraMap_eq fun d ↦ by
    apply Subtype.ext
    exact IsScalarTower.algebraMap_apply D A K d
  have : IsLocalization (Algebra.algebraMapSubmonoid K Q.primeCompl) K :=
    IsLocalization.self fun x ⟨d, hd, hx⟩ ↦ by
      rw [← hx]
      exact (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (Q.primeCompl_le_nonZeroDivisors hd)).isUnit
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid O Q.primeCompl) B :=
    IsLocalization.integralClosure (R := D) (S := K) (Rf := A) (Sf := K) Q.primeCompl
  have : Module.Finite A B := Module.Finite.of_isLocalization D O Q.primeCompl
  have ha' : algebraMap D A a ≠ 0 :=
    (map_ne_zero_iff _ (IsLocalization.injective A Q.primeCompl_le_nonZeroDivisors)).mpr ha
  rw [NormalizationOrderLength.length_quotient_eq_finsum_ord_mul_inertiaDeg K hQ ha',
    ← finsum_mem_univ]
  -- reindex the maximal ideals of `B` by the primes of `O` over `Q`
  let e : MaximalSpectrum B → PrimeSpectrum O := fun m ↦
    ⟨m.asIdeal.comap (algebraMap O B), Ideal.IsPrime.comap _⟩
  have hdisj : ∀ 𝔔 : PrimeSpectrum O, 𝔔.asIdeal.comap (algebraMap D O) = Q →
      Disjoint (Algebra.algebraMapSubmonoid O Q.primeCompl : Set O) 𝔔.asIdeal := by
    intro 𝔔 h𝔔
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨s, hs, rfl⟩ hs𝔔
    exact hs (h𝔔 ▸ (Ideal.mem_comap.mpr hs𝔔))
  have hcomapA : ∀ m : MaximalSpectrum B, m.asIdeal.comap (algebraMap A B) = maximalIdeal A :=
    fun m ↦ NormalizationOrderLength.comap_eq_maximalIdeal K m.asIdeal
  have hcomapD : ∀ m : MaximalSpectrum B, m.asIdeal.comap (algebraMap D B) = Q := by
    intro m
    rw [IsScalarTower.algebraMap_eq D A B, ← Ideal.comap_comap, hcomapA]
    exact IsLocalization.AtPrime.under_maximalIdeal A Q
  refine finsum_mem_eq_of_bijOn e ⟨?_, ?_, ?_⟩ ?_
  · intro m _
    change Ideal.comap _ (Ideal.comap _ _) = Q
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq, hcomapD]
  · intro m _ m' _ hmm'
    apply MaximalSpectrum.ext
    have h := congrArg PrimeSpectrum.asIdeal hmm'
    change m.asIdeal.comap _ = m'.asIdeal.comap _ at h
    rw [← IsLocalization.map_under (Algebra.algebraMapSubmonoid O Q.primeCompl) B m.asIdeal,
      ← IsLocalization.map_under (Algebra.algebraMapSubmonoid O Q.primeCompl) B m'.asIdeal]
    exact congrArg (Ideal.map (algebraMap O B)) h
  · intro 𝔔 h𝔔
    change 𝔔.asIdeal.comap _ = Q at h𝔔
    let m := 𝔔.asIdeal.map (algebraMap O B)
    have hmprime : m.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint
      (Algebra.algebraMapSubmonoid O Q.primeCompl) B _ 𝔔.isPrime (hdisj 𝔔 h𝔔)
    have hcomap : m.comap (algebraMap O B) = 𝔔.asIdeal :=
      IsLocalization.under_map_of_isPrime_disjoint _ B 𝔔.isPrime (hdisj 𝔔 h𝔔)
    have hmA : m.comap (algebraMap A B) = maximalIdeal A := by
      have : (m.comap (algebraMap A B)).IsPrime := Ideal.IsPrime.comap _
      apply (IsLocalization.orderEmbedding Q.primeCompl A).injective
      change Ideal.comap _ _ = Ideal.comap _ _
      rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq D O B,
        ← Ideal.comap_comap, hcomap, h𝔔]
      exact (IsLocalization.AtPrime.under_maximalIdeal A Q).symm
    have hmmax : m.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _
      (by rw [hmA]; exact maximalIdeal.isMaximal A)
    exact ⟨⟨m, hmmax⟩, trivial, PrimeSpectrum.ext hcomap⟩
  · intro m _
    set 𝔔 := e m
    have h𝔔 : 𝔔.asIdeal = m.asIdeal.comap (algebraMap O B) := rfl
    have hx : algebraMap B (Localization.AtPrime m.asIdeal) (algebraMap A B (algebraMap D A a)) =
        algebraMap O (Localization.AtPrime m.asIdeal) (algebraMap D O a) := by
      rw [← IsScalarTower.algebraMap_apply D A B, IsScalarTower.algebraMap_apply D O B,
        ← IsScalarTower.algebraMap_apply O B (Localization.AtPrime m.asIdeal)]
    have hy : algebraMap D (Localization.AtPrime 𝔔.asIdeal) a =
        algebraMap O (Localization.AtPrime 𝔔.asIdeal) (algebraMap D O a) :=
      IsScalarTower.algebraMap_apply D O _ a
    rw [hx, hy, ring_ord_localization_atPrime_eq (S := B)
      (Algebra.algebraMapSubmonoid O Q.primeCompl) m.asIdeal,
      inertiaDeg_eq_of_isLocalization (O := O) (B := B) Q.primeCompl m.asIdeal]

/-- Under the hypotheses of `length_quotient_eq_finsum_primesOver`, every prime `𝔔` of `O` lying
over `Q` has `dim O_𝔔 = 1`: `O_𝔔` is the localization of the semilocal Dedekind domain `B` at a
maximal ideal. -/
theorem ringKrullDim_localization_of_comap_eq (hQ : ringKrullDim (Localization.AtPrime Q) = 1)
    [Module.Finite D (integralClosure D (FractionRing D))]
    (𝔔 : PrimeSpectrum (integralClosure D (FractionRing D)))
    (h𝔔 : 𝔔.asIdeal.comap (algebraMap D _) = Q) :
    ringKrullDim (Localization.AtPrime 𝔔.asIdeal) = 1 := by
  classical
  let K := FractionRing D
  let A := Localization.AtPrime Q
  let O := integralClosure D K
  let φAK := Localization.mapToFractionRing K Q.primeCompl A Q.primeCompl_le_nonZeroDivisors
  let _ : Algebra A K := φAK.toRingHom.toAlgebra
  have : IsScalarTower D A K := IsScalarTower.of_algebraMap_eq fun d ↦ (φAK.commutes d).symm
  have : IsFractionRing A K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization Q.primeCompl A K
  let B := integralClosure A K
  let ι : O →+* B :=
    { toFun := fun x ↦ ⟨x, IsIntegral.tower_top (A := A) x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  let _ : Algebra O B := ι.toAlgebra
  have : IsScalarTower O B K := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower D O B := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower D A B := IsScalarTower.of_algebraMap_eq fun d ↦ by
    apply Subtype.ext
    exact IsScalarTower.algebraMap_apply D A K d
  have : IsLocalization (Algebra.algebraMapSubmonoid K Q.primeCompl) K :=
    IsLocalization.self fun x ⟨d, hd, hx⟩ ↦ by
      rw [← hx]
      exact (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (Q.primeCompl_le_nonZeroDivisors hd)).isUnit
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid O Q.primeCompl) B :=
    IsLocalization.integralClosure (R := D) (S := K) (Rf := A) (Sf := K) Q.primeCompl
  have : Module.Finite A B := Module.Finite.of_isLocalization D O Q.primeCompl
  have hdisj : Disjoint (Algebra.algebraMapSubmonoid O Q.primeCompl : Set O) 𝔔.asIdeal := by
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨s, hs, rfl⟩ hs𝔔
    exact hs (h𝔔 ▸ (Ideal.mem_comap.mpr hs𝔔))
  let m := 𝔔.asIdeal.map (algebraMap O B)
  have hmprime : m.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint
    (Algebra.algebraMapSubmonoid O Q.primeCompl) B _ 𝔔.isPrime hdisj
  have hcomap : m.comap (algebraMap O B) = 𝔔.asIdeal :=
    IsLocalization.under_map_of_isPrime_disjoint _ B 𝔔.isPrime hdisj
  have hmA : m.comap (algebraMap A B) = maximalIdeal A := by
    have : (m.comap (algebraMap A B)).IsPrime := Ideal.IsPrime.comap _
    apply (IsLocalization.orderEmbedding Q.primeCompl A).injective
    change Ideal.comap _ _ = Ideal.comap _ _
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq D O B,
      ← Ideal.comap_comap, hcomap, h𝔔]
    exact (IsLocalization.AtPrime.under_maximalIdeal A Q).symm
  have hmmax : m.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _
    (by rw [hmA]; exact maximalIdeal.isMaximal A)
  have := NormalizationOrderLength.isDiscreteValuationRing_localization K hQ m
  let 𝔔' : PrimeSpectrum O := ⟨m.comap (algebraMap O B), Ideal.IsPrime.comap _⟩
  have h𝔔' : 𝔔' = 𝔔 := PrimeSpectrum.ext hcomap
  have : IsLocalization.AtPrime (Localization.AtPrime m) 𝔔'.asIdeal :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid O Q.primeCompl) (Localization.AtPrime m) m
  let e := IsLocalization.algEquiv 𝔔'.asIdeal.primeCompl (Localization.AtPrime m)
    (Localization.AtPrime 𝔔'.asIdeal)
  have h : ringKrullDim (Localization.AtPrime 𝔔'.asIdeal) = 1 := by
    rw [← ringKrullDim_eq_of_ringEquiv e.toRingEquiv]
    exact IsDiscreteValuationRing.ringKrullDim_eq_one (Localization.AtPrime m)
  exact h𝔔' ▸ h

end Hartshorne.NormalizationLocalOrder

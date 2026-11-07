/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.Differentials.FieldDifferentialsDimension
import Hartshorne.Scheme.Differentials.LocalCotangentViaDifferentials
import Hartshorne.Dimension.DimFormula
import Hartshorne.Dimension.FgDomain
import Hartshorne.Scheme.RegularLocalCohenMacaulay
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# The regular-local differential criterion

Hartshorne, *Algebraic Geometry*, II.8, Theorem 8.8 and Lemma 8.9 (pp. 174–175).

Let `(B, 𝔪)` be a local ring which is a localization of a finitely generated algebra over a
perfect field `k`, with `k ≅ B/𝔪`. Hartshorne's Theorem 8.8 says that `Ω_{B/k}` is a free
`B`-module of rank `dim B` if and only if `B` is a regular local ring.

## Main results

* `Hartshorne.free_of_finrank_residueField_eq_finrank_fractionField` (Lemma 8.9): a finite module
  over a local domain whose fibres at the closed and the generic point have the same dimension `r`
  is free of rank `r`. The Noetherian hypothesis of Hartshorne's statement is not needed.
* `Hartshorne.isRegularLocalRing_of_free_kaehlerDifferential`: if `Ω_{B/k}` is free of rank
  `dim B`, then `B` is regular. By Proposition 8.7 the fibre `Ω_{B/k} ⊗ k` is the cotangent space
  `𝔪/𝔪²`, so its dimension is `dim B`.
* `Hartshorne.free_kaehlerDifferential_of_isRegularLocalRing_of_isDomain`: if `B` is a regular
  local domain, then `Ω_{B/k}` is free of rank `dim B`. With `K` the fraction field of `B`, the
  generic fibre is `Ω_{K/k}`, whose dimension is `trdeg_k K` because `K/k` is separably generated
  (`k` is perfect); and `trdeg_k K = dim B` by the dimension theory of finitely generated domains.
  Lemma 8.9 then applies.

* `Hartshorne.free_kaehlerDifferential_of_isRegularLocalRing`: the same without the domain
  hypothesis, since a regular local ring is a domain (`Hartshorne.RegularLocal.isDomain`).
* `Hartshorne.isRegularLocalRing_iff_free_kaehlerDifferential` (Theorem 8.8): `Ω_{B/k}` is free of
  rank `dim B` if and only if `B` is regular. Both rings live in one universe, because the
  dimension theory of finitely generated domains used here is single-universe.
-/

namespace Hartshorne

noncomputable section

open TensorProduct IsLocalRing

universe u v w

/-- **Hartshorne II, Lemma 8.9.** Let `R` be a local domain with residue field `κ` and fraction
field `K`, and let `M` be a finitely generated `R`-module. If `dim_κ (M ⊗ κ) = dim_K (M ⊗ K) = r`,
then `M` is free of rank `r`. -/
theorem free_of_finrank_residueField_eq_finrank_fractionField
    {R : Type u} [CommRing R] [IsLocalRing R] [IsDomain R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (K : Type w) [Field K] [Algebra R K] [IsFractionRing R K] {r : ℕ}
    (hk : Module.finrank (ResidueField R) (ResidueField R ⊗[R] M) = r)
    (hK : Module.finrank K (K ⊗[R] M) = r) :
    Module.Free R M ∧ Module.finrank R M = r := by
  -- lift a basis of the closed fibre; by Nakayama the lifts generate `M`
  let b : Module.Basis (Fin r) (ResidueField R) (ResidueField R ⊗[R] M) :=
    (Module.finBasis _ _).reindex (finCongr hk)
  choose f hf using fun i =>
    TensorProduct.mk_surjective R M (ResidueField R) Ideal.Quotient.mk_surjective (b i)
  have hspan : Submodule.span R (Set.range f) = ⊤ :=
    span_eq_top_of_tmul_eq_basis f b hf
  let φ : (Fin r → R) →ₗ[R] M := Fintype.linearCombination R f
  have hsurj : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hspan]
  -- on the generic fibre `φ` is a surjection between spaces of the same dimension
  have hsurjK : Function.Surjective (φ.baseChange K) :=
    LinearMap.lTensor_surjective K hsurj
  have hfin : Module.finrank K (K ⊗[R] (Fin r → R)) = Module.finrank K (K ⊗[R] M) := by
    rw [Module.finrank_baseChange, hK]; simp
  have hinjK : Function.Injective (φ.baseChange K) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).2 hsurjK
  -- so the kernel of `φ` is torsion, hence zero
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    rw [LinearMap.mem_ker] at hv
    have h1 : (1 : K) ⊗ₜ[R] v = 0 := by
      apply hinjK
      rw [LinearMap.baseChange_tmul, hv, tmul_zero, map_zero]
    funext i
    have h2 := congrFun (congrArg (TensorProduct.piScalarRightHom R K K (Fin r)) h1) i
    simp only [piScalarRightHom_tmul, map_zero, Pi.zero_apply, Algebra.smul_def, mul_one] at h2
    exact IsFractionRing.injective R K (by simpa using h2)
  let e : (Fin r → R) ≃ₗ[R] M := LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩
  exact ⟨Module.Free.of_equiv e, by rw [← e.finrank_eq]; simp⟩

section

variable (k : Type u) (B : Type v) [Field k] [CommRing B] [IsLocalRing B] [Algebra k B]

/-- When `k` maps isomorphically onto the residue field, the cotangent space `𝔪/𝔪²` and the closed
fibre of `Ω_{B/k}` have the same dimension (Proposition 8.7). -/
theorem finrank_cotangentSpace_eq_finrank_residueField_tensor_kaehlerDifferential
    (h : Function.Bijective (algebraMap k (ResidueField B))) :
    Module.finrank (ResidueField B) (CotangentSpace B) =
      Module.finrank (ResidueField B) (ResidueField B ⊗[B] Ω[B⁄k]) := by
  have : IsScalarTower k (ResidueField B) (CotangentSpace B) :=
    IsScalarTower.of_algebraMap_smul fun c v => by
      rw [IsScalarTower.algebraMap_apply k B (ResidueField B), algebraMap_smul,
        algebraMap_smul]
  have h1 : Module.finrank k (ResidueField B) = 1 :=
    (AlgEquiv.ofBijective (Algebra.ofId k _) h).toLinearEquiv.finrank_eq.symm.trans
      (Module.finrank_self k)
  have hc := Module.finrank_mul_finrank k (ResidueField B) (CotangentSpace B)
  have hΩ := Module.finrank_mul_finrank k (ResidueField B) (ResidueField B ⊗[B] Ω[B⁄k])
  rw [h1, one_mul] at hc hΩ
  rw [hc, hΩ, (localCotangentEquivDifferentials k B h).finrank_eq]
  exact ((TensorProduct.comm B Ω[B⁄k] (ResidueField B)).restrictScalars k).finrank_eq

/-- **One direction of Hartshorne II, Theorem 8.8.** If `B` is a local ring essentially of finite
type over a field `k ≅ B/𝔪` and `Ω_{B/k}` is free of rank `dim B`, then `B` is a regular local
ring. -/
theorem isRegularLocalRing_of_free_kaehlerDifferential [Algebra.EssFiniteType k B]
    (h : Function.Bijective (algebraMap k (ResidueField B))) [Module.Free B Ω[B⁄k]]
    (hr : (Module.finrank B Ω[B⁄k] : WithBot ℕ∞) = ringKrullDim B) :
    IsRegularLocalRing B := by
  have := Algebra.EssFiniteType.isNoetherianRing k B
  rw [IsRegularLocalRing.iff_finrank_cotangentSpace,
    finrank_cotangentSpace_eq_finrank_residueField_tensor_kaehlerDifferential k B h,
    Module.finrank_baseChange, hr]

end

section

variable (k B : Type u) [Field k] [CommRing B] [IsDomain B] [Algebra k B]
  [Algebra.EssFiniteType k B]

/-- A local domain `B`, essentially of finite type over a field `k` that maps onto the residue
field, has dimension equal to the transcendence degree of its fraction field over `k`. -/
theorem exists_ringKrullDim_eq_trdeg_of_essFiniteType [IsLocalRing B]
    (h : Function.Surjective (algebraMap k (ResidueField B))) :
    ∃ s : ℕ, ringKrullDim B = s ∧ Algebra.trdeg k (FractionRing B) = s := by
  let A := Algebra.EssFiniteType.subalgebra k B
  let p : Ideal A := (maximalIdeal B).comap (algebraMap A B)
  -- `p` is the kernel of the surjection `A → B/𝔪`, hence maximal
  let φ : A →+* ResidueField B := (residue B).comp (algebraMap A B)
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨c, rfl⟩ := h y
    exact ⟨algebraMap k A c, by
      simp [φ, IsScalarTower.algebraMap_apply k B (ResidueField B)]⟩
  have hker : RingHom.ker φ = p := by
    rw [← RingHom.comap_ker, ker_residue]
  have : p.IsMaximal := hker ▸ RingHom.ker_isMaximal_of_surjective φ hφ
  -- `B` is the localization of `A` at `p`
  have hsub : Algebra.EssFiniteType.submonoid k B = p.primeCompl := by
    ext x
    simp [Algebra.EssFiniteType.submonoid, p, Ideal.primeCompl, mem_maximalIdeal,
      mem_nonunits_iff, IsUnit.mem_submonoid_iff]
  have : IsLocalization.AtPrime B p := by
    rw [IsLocalization.AtPrime, ← hsub]; infer_instance
  -- the fraction field of `B` is a fraction field of `A`
  have : IsFractionRing A (FractionRing B) := by
    have := IsLocalization.localization_localization_isLocalization_of_has_all_units
      p.primeCompl (nonZeroDivisors B) (FractionRing B)
      (fun x hx => mem_nonZeroDivisors_of_ne_zero hx.ne_zero)
    convert this using 1
    ext x
    simp only [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
    exact (map_ne_zero_iff _ (IsLocalization.injective B p.primeCompl_le_nonZeroDivisors)).symm
  obtain ⟨s, hs, htr⟩ := exists_ringKrullDim_eq_trdeg k A (FractionRing B)
  refine ⟨s, ?_, htr⟩
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p B, height_eq_ringKrullDim_of_isMaximal k A p,
    hs]

/-- **The other direction of Hartshorne II, Theorem 8.8, for a domain.** If `B` is a regular local
domain, essentially of finite type over a perfect field `k ≅ B/𝔪`, then `Ω_{B/k}` is free of rank
`dim B`. -/
theorem free_kaehlerDifferential_of_isRegularLocalRing_of_isDomain [PerfectField k]
    [IsRegularLocalRing B] (h : Function.Bijective (algebraMap k (ResidueField B))) :
    Module.Free B Ω[B⁄k] ∧ (Module.finrank B Ω[B⁄k] : WithBot ℕ∞) = ringKrullDim B := by
  obtain ⟨s, hdim, htr⟩ := exists_ringKrullDim_eq_trdeg_of_essFiniteType k B h.2
  -- closed fibre: the cotangent space, of dimension `dim B` by regularity
  have hk : Module.finrank (ResidueField B) (ResidueField B ⊗[B] Ω[B⁄k]) = s := by
    rw [← finrank_cotangentSpace_eq_finrank_residueField_tensor_kaehlerDifferential k B h]
    have := (IsRegularLocalRing.iff_finrank_cotangentSpace B).mp inferInstance
    rw [hdim] at this
    exact_mod_cast this
  -- generic fibre: `Ω_{K/k}`, of dimension `trdeg_k K` since `K/k` is separably generated
  have hK : Module.finrank (FractionRing B) (FractionRing B ⊗[B] Ω[B⁄k]) = s := by
    have : Algebra.FormallyEtale B (FractionRing B) :=
      .of_isLocalization (nonZeroDivisors B)
    have : Algebra.EssFiniteType B (FractionRing B) :=
      .of_isLocalization (FractionRing B) (nonZeroDivisors B)
    have : Algebra.EssFiniteType k (FractionRing B) := .comp k B _
    rw [(KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k B (FractionRing B)).finrank_eq]
    obtain ⟨t, ht, hsep⟩ :=
      exists_isTranscendenceBasis_and_isSeparable_of_perfectField k (FractionRing B)
    have hrank := ((trdeg_le_rank_kaehlerDifferential (IntermediateField.fg_top_iff.mpr
      inferInstance)).2.1).mpr ⟨(t : Set (FractionRing B)), ht, hsep⟩
    exact Module.finrank_eq_of_rank_eq (hrank.symm.trans htr)
  obtain ⟨hfree, hrank⟩ := free_of_finrank_residueField_eq_finrank_fractionField
    (FractionRing B) hk hK
  exact ⟨hfree, by rw [hrank, hdim]⟩

end

section

variable (k B : Type u) [Field k] [CommRing B] [Algebra k B] [Algebra.EssFiniteType k B]

/-- **The forward direction of Hartshorne II, Theorem 8.8.** If `B` is a regular local ring,
essentially of finite type over a perfect field `k ≅ B/𝔪`, then `Ω_{B/k}` is free of rank `dim B`.
This removes the domain hypothesis of
`free_kaehlerDifferential_of_isRegularLocalRing_of_isDomain`, since a regular local ring is a
domain (`Hartshorne.RegularLocal.isDomain`). -/
theorem free_kaehlerDifferential_of_isRegularLocalRing [PerfectField k]
    [IsRegularLocalRing B] (h : Function.Bijective (algebraMap k (ResidueField B))) :
    Module.Free B Ω[B⁄k] ∧ (Module.finrank B Ω[B⁄k] : WithBot ℕ∞) = ringKrullDim B := by
  have := RegularLocal.isDomain B
  exact free_kaehlerDifferential_of_isRegularLocalRing_of_isDomain k B h

/-- **Hartshorne II, Theorem 8.8.** Let `B` be a local ring, essentially of finite type over a
perfect field `k` with `k ≅ B/𝔪`. Then `Ω_{B/k}` is a free `B`-module of rank `dim B` if and only
if `B` is a regular local ring. -/
theorem isRegularLocalRing_iff_free_kaehlerDifferential [PerfectField k] [IsLocalRing B]
    (h : Function.Bijective (algebraMap k (ResidueField B))) :
    IsRegularLocalRing B ↔
      Module.Free B Ω[B⁄k] ∧ (Module.finrank B Ω[B⁄k] : WithBot ℕ∞) = ringKrullDim B :=
  ⟨fun _ => free_kaehlerDifferential_of_isRegularLocalRing k B h,
    fun ⟨_, hr⟩ => isRegularLocalRing_of_free_kaehlerDifferential k B h hr⟩

end

end

end Hartshorne

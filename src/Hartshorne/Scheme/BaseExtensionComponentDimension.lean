/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Dimension.Integral
import Hartshorne.Scheme.BaseExtension
import Hartshorne.Scheme.DimensionCodimension
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.Topology.KrullDimension

/-!
# Dimension after extending the ground field

Hartshorne, *Algebraic Geometry*, Exercise II.3.20(f) (p. 95).

Let `X` be an integral scheme of finite type over a field `k` and let `k ⊆ k'` be a field
extension. Every irreducible component of `X ×_k k'` has dimension `dim X`. The dimension of a
component is the Krull dimension of the component as a topological subspace of `X ×_k k'`.

## Algebra

For a finitely generated `k`-domain `A` and a minimal prime `P` of `A ⊗_k k'`, the quotient
`(A ⊗_k k') / P` has dimension `dim A`. Choose a Noether normalization
`R = k[y₁, …, y_s] ↪ A`, so that `dim A = s`. Then `A ⊗_k k'` is isomorphic to
`R' ⊗_R A` with `R' = R ⊗_k k' ≅ k'[y₁, …, y_s]` a domain that is flat over `R`. Base change of
the torsion-free `R`-module `A` along the flat extension of domains `R → R'` is torsion-free
over `R'`: it embeds in `R' ⊗_R (K ⊗_R A)`, `K = Frac R`, which is flat over `R'`. Elements of
a minimal prime are zero divisors, so `P` meets `R'` only in `0`, and `(R' ⊗_R A) / P` is an
integral extension of `R'`, of dimension `dim R' = s`.

## Gluing

Every point of `X ×_k k'` lies in the open subscheme over an affine open `U = Spec A` of `X`,
which is `Spec (A ⊗_k k')`; and every nonempty affine open of `X` has dimension `dim X`. The
trace of a component `Z` on such a chart is an irreducible component of `Spec (A ⊗_k k')`,
that is, the closed set of a minimal prime, so it has dimension `dim X`. A space covered by
open subspaces of dimension at most `n` has dimension at most `n`, which gives `dim Z ≤ dim X`;
any one chart meeting `Z` gives the reverse inequality.

## Main results

* `Hartshorne.baseExtension_irreducibleComponent_topologicalKrullDim`
-/

namespace Hartshorne

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
open AlgebraicGeometry TensorProduct

universe u v

namespace BaseExtensionComponentDimension

/-- Base change of a torsion-free module over a domain along a flat algebra is torsion-free. -/
theorem isTorsionFree_baseChange_of_flat
    {R R' M : Type*} [CommRing R] [IsDomain R] [CommRing R'] [Algebra R R']
    [Module.Flat R R'] [AddCommGroup M] [Module R M] [Module.IsTorsionFree R M] :
    Module.IsTorsionFree R' (R' ⊗[R] M) := by
  let K := FractionRing R
  let i : M →ₗ[R] K ⊗[R] M := TensorProduct.mk R K M 1
  have hi : Function.Injective i := by
    rw [IsLocalizedModule.injective_iff_isRegular (nonZeroDivisors R)]
    intro c
    exact Module.IsTorsionFree.isSMulRegular
      (IsRegular.of_ne_zero (nonZeroDivisors.coe_ne_zero c))
  have hinj : Function.Injective (LinearMap.baseChange R' i) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap i hi
  have : Module.Flat R (K ⊗[R] M) := Module.Flat.trans R K _
  have : Module.Flat R' (R' ⊗[R] (K ⊗[R] M)) := inferInstance
  exact hinj.moduleIsTorsionFree _ (fun r x => (LinearMap.baseChange R' i).map_smul r x)

/-- Let `A` be a domain integral over a domain `R` and `R'` a domain flat over `R`. For every
minimal prime `P` of `R' ⊗_R A`, the quotient by `P` has the dimension of `R'`. -/
theorem ringKrullDim_quotient_baseChange_of_mem_minimalPrimes
    {R A R' : Type*} [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [Algebra R A]
    [Algebra.IsIntegral R A] [FaithfulSMul R A] [CommRing R'] [IsDomain R'] [Algebra R R']
    [Module.Flat R R'] {P : Ideal (R' ⊗[R] A)} (hP : P ∈ minimalPrimes (R' ⊗[R] A)) :
    ringKrullDim (R' ⊗[R] A ⧸ P) = ringKrullDim R' := by
  have : Module.IsTorsionFree R' (R' ⊗[R] A) := isTorsionFree_baseChange_of_flat
  have : P.IsPrime := hP.1.1
  -- the contraction of `P` to `R'` is zero
  have hker : P.comap (algebraMap R' (R' ⊗[R] A)) = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun r hr => ?_
    by_contra hr0
    apply notMem_nonZeroDivisors_of_mem_mem_minimalPrimes (Ideal.mem_comap.1 hr) hP
    rw [mem_nonZeroDivisors_iff_right]
    intro c hc
    have hrc : r • c = 0 := by rw [Algebra.smul_def, mul_comm]; exact hc
    exact (Module.IsTorsionFree.isSMulRegular (IsRegular.of_ne_zero hr0)).right_eq_zero_of_smul
      hrc
  have : FaithfulSMul R' (R' ⊗[R] A ⧸ P) := by
    refine (faithfulSMul_iff_algebraMap_injective R' (R' ⊗[R] A ⧸ P)).2 ?_
    rw [injective_iff_map_eq_zero]
    intro r hr
    rw [IsScalarTower.algebraMap_apply R' (R' ⊗[R] A) (R' ⊗[R] A ⧸ P),
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] at hr
    have : r ∈ P.comap (algebraMap R' (R' ⊗[R] A)) := hr
    rwa [hker] at this
  exact ringKrullDim_eq_of_isIntegral R' (R' ⊗[R] A ⧸ P)

/-- A ring isomorphism carries minimal primes to minimal primes and preserves the dimensions of
the quotients. -/
theorem map_mem_minimalPrimes_and_ringKrullDim_quotient_of_ringEquiv
    {S T : Type*} [CommRing S] [CommRing T] (e : S ≃+* T) {P : Ideal S}
    (hP : P ∈ minimalPrimes S) :
    P.map (e : S →+* T) ∈ minimalPrimes T ∧
      ringKrullDim (S ⧸ P) = ringKrullDim (T ⧸ P.map (e : S →+* T)) := by
  refine ⟨?_, ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv P _ e rfl)⟩
  have h := Ideal.minimalPrimes_comap_of_surjective (f := (e.symm : T →+* S))
    e.symm.surjective hP
  have h1 : Ideal.comap (e.symm : T →+* S) P = P.map (e : S →+* T) := by
    rw [Ideal.map_comap_of_equiv]; rfl
  have h0 : Ideal.comap (e.symm : T →+* S) ⊥ = ⊥ :=
    Ideal.comap_bot_of_injective _ e.symm.injective
  rwa [h1, h0] at h

/-- For a finitely generated `k`-domain `A`, a field extension `k'` of `k`, and a minimal prime
`P` of `A ⊗_k k'`, the quotient `(A ⊗_k k') / P` has dimension `dim A`. -/
theorem ringKrullDim_quotient_tensor_of_mem_minimalPrimes
    (k A k' : Type*) [Field k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    [Field k'] [Algebra k k'] {P : Ideal (A ⊗[k] k')} (hP : P ∈ minimalPrimes (A ⊗[k] k')) :
    ringKrullDim (A ⊗[k] k' ⧸ P) = ringKrullDim A := by
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg k A
  let _ : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
  have : IsScalarTower k (MvPolynomial (Fin s) k) A :=
    IsScalarTower.of_algebraMap_eq fun c => (g.commutes c).symm
  have : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := ⟨hint⟩
  have : FaithfulSMul (MvPolynomial (Fin s) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have hdimA : ringKrullDim A = s := by
    rw [ringKrullDim_eq_of_isIntegral (MvPolynomial (Fin s) k) A,
      MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  -- `k[y] ⊗ k'` is a polynomial ring over `k'`
  let eR : MvPolynomial (Fin s) k ⊗[k] k' ≃+* MvPolynomial (Fin s) k' :=
    (Algebra.TensorProduct.comm k (MvPolynomial (Fin s) k) k').toRingEquiv.trans
      (MvPolynomial.algebraTensorAlgEquiv k k').toRingEquiv
  have : IsDomain (MvPolynomial (Fin s) k ⊗[k] k') :=
    MulEquiv.isDomain (MvPolynomial (Fin s) k') eR.toMulEquiv
  have hdimR' : ringKrullDim (MvPolynomial (Fin s) k ⊗[k] k') = s := by
    rw [ringKrullDim_eq_of_ringEquiv eR, MvPolynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_field]
    simp
  let e : A ⊗[k] k' ≃+* (MvPolynomial (Fin s) k ⊗[k] k') ⊗[MvPolynomial (Fin s) k] A :=
    (Algebra.TensorProduct.cancelBaseChange k (MvPolynomial (Fin s) k) A A k').symm.toRingEquiv
      |>.trans
      (Algebra.TensorProduct.comm (MvPolynomial (Fin s) k) A
        (MvPolynomial (Fin s) k ⊗[k] k')).toRingEquiv
  obtain ⟨hP', hq⟩ := map_mem_minimalPrimes_and_ringKrullDim_quotient_of_ringEquiv
    (T := (MvPolynomial (Fin s) k ⊗[k] k') ⊗[MvPolynomial (Fin s) k] A) e hP
  rw [hq, ringKrullDim_quotient_baseChange_of_mem_minimalPrimes hP', hdimR', hdimA]

/-- A space each of whose points lies in an open subspace of dimension at most `n` has dimension
at most `n`. -/
theorem topologicalKrullDim_le_of_forall_isOpenEmbedding {Y : Type*} [TopologicalSpace Y]
    (n : WithBot ℕ∞)
    (h : ∀ y : Y, ∃ (W : Type v) (_ : TopologicalSpace W) (e : W → Y),
      IsOpenEmbedding e ∧ y ∈ Set.range e ∧ topologicalKrullDim W ≤ n) :
    topologicalKrullDim Y ≤ n := by
  refine iSup_le fun l => ?_
  obtain ⟨y, hy⟩ := (l 0).isIrreducible.nonempty
  obtain ⟨W, _, e, he, ⟨w, rfl⟩, hW⟩ := h y
  let φ := IrreducibleCloseds.orderIsoOfIsOpenEmbedding e he
  have hmeet : ∀ i, (e ⁻¹' (l i : Set Y)).Nonempty := fun i =>
    ⟨w, (show (l 0 : Set Y) ⊆ l i from l.monotone (Fin.zero_le i)) hy⟩
  let l' : LTSeries (IrreducibleCloseds W) :=
    ⟨l.length, fun i => φ.symm ⟨l i, hmeet i⟩, fun i => φ.symm.strictMono (l.step i)⟩
  exact le_trans (Order.LTSeries.length_le_krullDim l') hW

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k']

/-- Charts of a base extension. Every point of `X ×_k k'` lies in an open subscheme
`Spec (A ⊗_k k')`, where `A` is a finitely generated `k`-domain of dimension `dim X` (the
sections over an affine open of `X`). -/
theorem exists_baseExtension_chart {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of k))
    (hf : FiniteType f) (g : Spec (.of k') ⟶ Spec (.of k))
    (hg : g = Spec.map (CommRingCat.ofHom (algebraMap k k'))) (z : (pullback f g : Scheme.{u})) :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : Algebra k A)
      (_ : Algebra.FiniteType k A) (ψ : Spec (.of (A ⊗[k] k')) ⟶ pullback f g),
      IsOpenImmersion ψ ∧ z ∈ Set.range ψ ∧ ringKrullDim A = topologicalKrullDim X := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show pullback.fst f g z ∈ (⊤ : X.Opens) from trivial) isOpen_univ
  replace hU : IsAffineOpen U := hU
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  obtain ⟨N, hNA, hNX⟩ := DimensionCodimension.exists_ringKrullDim_eq f hf U hU
  -- the `k`-algebra structure on `Γ(X, U)` coming from `f`
  let a : CommRingCat.of k ⟶ Γ(X, U) := Spec.preimage (hU.fromSpec ≫ f)
  let _ : Algebra k Γ(X, U) := a.hom.toAlgebra
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U))) = hU.fromSpec ≫ f := by
    change Spec.map (CommRingCat.ofHom a.hom) = _
    simp [a]
  have hft : Algebra.FiniteType k Γ(X, U) := by
    have : LocallyOfFiniteType f := hf.1
    have : LocallyOfFiniteType (Spec.map a) := by rw [Spec.map_preimage]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this
  -- `Spec (Γ(X, U) ⊗_k k')` is the pullback of `U ⟶ X` along the first projection
  let E : Spec (.of (Γ(X, U) ⊗[k] k')) ≅ pullback hU.fromSpec (pullback.fst f g) :=
    (pullbackSpecIso k Γ(X, U) k').symm ≪≫ pullback.congrHom hφ hg.symm ≪≫
      (pullbackRightPullbackFstIso f g hU.fromSpec).symm
  refine ⟨Γ(X, U), inferInstance, inferInstance, inferInstance, hft,
    E.hom ≫ pullback.snd hU.fromSpec (pullback.fst f g), inferInstance, ?_,
    hNA.trans hNX.symm⟩
  have hz : z ∈ Set.range (pullback.snd hU.fromSpec (pullback.fst f g)) := by
    rw [IsOpenImmersion.range_pullbackSnd]
    show pullback.fst f g z ∈ Set.range hU.fromSpec
    rw [hU.range_fromSpec]
    exact hxU
  obtain ⟨w, hw⟩ := hz
  exact ⟨E.inv w, by rw [← hw]; simp⟩

end BaseExtensionComponentDimension

open BaseExtensionComponentDimension

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k']

/-- **Hartshorne, Exercise II.3.20(f).** Let `X` be an integral scheme of finite type over a
field `k` and let `k ⊆ k'` be a field extension. Every irreducible component of the base
extension `X ×_k k'` has the dimension of `X`. The dimension of a component is its Krull
dimension as a topological subspace of `X ×_k k'`. -/
theorem baseExtension_irreducibleComponent_topologicalKrullDim {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) (hf : FiniteType f)
    {Z : Set (baseExtension f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))}
    (hZ : Z ∈ irreducibleComponents
      (baseExtension f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))) :
    topologicalKrullDim Z = topologicalKrullDim X := by
  have key : ∀ z (hz : z ∈ Z), ∃ (W : Type u) (_ : TopologicalSpace W) (e : W → Z),
      IsOpenEmbedding e ∧ (⟨z, hz⟩ : Z) ∈ Set.range e ∧
        topologicalKrullDim W = topologicalKrullDim X := by
    intro z hz
    obtain ⟨A, _, _, _, _, ψ, hψ, ⟨w, hw⟩, hA⟩ := exists_baseExtension_chart f hf _ rfl z
    have hψe : IsOpenEmbedding ψ := ψ.isOpenEmbedding
    have hT : ψ ⁻¹' Z ∈ irreducibleComponents (PrimeSpectrum (A ⊗[k] k')) :=
      preimage_mem_irreducibleComponents hZ hψe ⟨z, hz, w, hw⟩
    let P := PrimeSpectrum.vanishingIdeal (ψ ⁻¹' Z)
    have hP : P ∈ minimalPrimes (A ⊗[k] k') := by
      rw [← PrimeSpectrum.vanishingIdeal_irreducibleComponents]
      exact ⟨_, hT, rfl⟩
    have hTP : PrimeSpectrum.zeroLocus (P : Set (A ⊗[k] k')) = ψ ⁻¹' Z := by
      rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
      exact (isClosed_of_mem_irreducibleComponents _ hT).closure_eq
    let c := PrimeSpectrum.comap (Ideal.Quotient.mk P)
    have hc : IsClosedEmbedding c :=
      PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ _ Ideal.Quotient.mk_surjective
    have hcr : Set.range c = ψ ⁻¹' Z := by
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
        hTP]
    have hmem : ∀ q, ψ (c q) ∈ Z := fun q => by
      have : c q ∈ ψ ⁻¹' Z := hcr ▸ Set.mem_range_self q
      exact this
    let e : PrimeSpectrum (A ⊗[k] k' ⧸ P) → Z := fun q => ⟨ψ (c q), hmem q⟩
    have hrange : Set.range e = Subtype.val ⁻¹' Set.range ψ := by
      ext ⟨y, hy⟩
      constructor
      · rintro ⟨q, hq⟩
        exact ⟨c q, congrArg Subtype.val hq⟩
      · rintro ⟨t, ht⟩
        have : t ∈ Set.range c := by rw [hcr]; show ψ t ∈ Z; rw [ht]; exact hy
        obtain ⟨q, rfl⟩ := this
        exact ⟨q, Subtype.ext ht⟩
    have he : IsOpenEmbedding e := by
      refine ⟨(hψe.isEmbedding.comp hc.isEmbedding).codRestrict Z _, ?_⟩
      rw [hrange]
      exact hψe.isOpen_range.preimage continuous_subtype_val
    refine ⟨PrimeSpectrum (A ⊗[k] k' ⧸ P), inferInstance, e, he, ?_, ?_⟩
    · rw [hrange]
      exact ⟨w, hw⟩
    · rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
        ringKrullDim_quotient_tensor_of_mem_minimalPrimes k A k' hP, hA]
  apply le_antisymm
  · refine topologicalKrullDim_le_of_forall_isOpenEmbedding _ fun z => ?_
    obtain ⟨W, _, e, he, hz, hW⟩ := key z.1 z.2
    exact ⟨W, _, e, he, hz, hW.le⟩
  · obtain ⟨z, hz⟩ := hZ.1.nonempty
    obtain ⟨W, _, e, he, -, hW⟩ := key z hz
    rw [← hW]
    exact he.isInducing.topologicalKrullDim_le

end Hartshorne

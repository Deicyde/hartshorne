/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Hartshorne.Dimension.DimFormula
import Hartshorne.Intersection.AffineProductCoordinateRing
import Hartshorne.Intersection.RawCyclePushforward
import Hartshorne.Intersection.TensorProductDimension
import Hartshorne.Scheme.ClassGroupOpenRestriction

/-!
# External products of cycles

Hartshorne, *Algebraic Geometry*, Appendix A.1 (pp. 426–427): the product cycle `Y × Z` that
appears in axiom A5.

Let `k` be an algebraically closed field and `X`, `Y` integral schemes locally of finite type
over `k`, with product `X × Y = X ×_k Y`. Cycles are represented as in
`Hartshorne.codimensionCycles`: an irreducible closed subset is recorded by its generic point.

For points `x ∈ X` and `y ∈ Y`, with `V = closure {x}` and `W = closure {y}`, the set
`V × W = fst⁻¹ V ∩ snd⁻¹ W` is irreducible, and its generic point `externalProductPoint pX pY x y`
satisfies `codim (V × W) = codim V + codim W` (`closure_externalProductPoint`,
`codim_closure_externalProductPoint`). Sending `[V] ⊗ [W]` to `[V × W]` and extending bilinearly
gives the external product `Z^r(X) × Z^s(Y) → Z^{r+s}(X × Y)` (`externalProduct`,
`externalProduct_apply_of_eq_single`).

## Local computation

On affine opens `Spec A ⊆ X` and `Spec B ⊆ Y`, the open `fst⁻¹ (Spec A) ∩ snd⁻¹ (Spec B)` of
`X × Y` is `Spec (A ⊗_k B)`. For the primes `𝔭 ⊆ A` and `𝔮 ⊆ B` of `x` and `y`, the trace of
`V × W` is the closed set of the kernel `P` of `A ⊗_k B → A/𝔭 ⊗_k B/𝔮`. Over an algebraically
closed field the tensor product of finitely generated domains is a domain
(`isDomain_tensorProduct`, from the coordinate ring of an affine product), so `P` is prime. The
dimension formula in the domains `A ⊗_k B`, `A`, `B`, and the additivity of dimension for tensor
products of affine domains, give `ht P = ht 𝔭 + ht 𝔮` (`height_tensorKer`). Comparing the
generic points obtained from two such charts by their (finite, equal) coheights shows that the
chart-wise generic point is the generic point of all of `V × W`.
-/

namespace Hartshorne

open AlgebraicGeometry CategoryTheory Limits Order
open scoped TensorProduct

universe u

namespace ExternalProduct

section Algebra

variable (k : Type u) [Field k]

attribute [local instance 1100] Module.Free.of_divisionRing Module.Flat.of_free

/-- Over an algebraically closed field, the tensor product of two finitely generated domains is a
domain: both are coordinate rings of affine varieties, and the tensor product is the coordinate
ring of their product. -/
theorem isDomain_tensorProduct [IsAlgClosed k] (A B : Type u) [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] [CommRing B] [IsDomain B] [Algebra k B]
    [Algebra.FiniteType k B] : IsDomain (A ⊗[k] B) := by
  obtain ⟨m, V, hV, ⟨eV⟩⟩ := exists_isAffineVariety_coordinateRing_equiv (k := k) (B := A)
  obtain ⟨n, W, hW, ⟨eW⟩⟩ := exists_isAffineVariety_coordinateRing_equiv (k := k) (B := B)
  have : IsDomain (coordinateRing (affineProduct V W)) :=
    isDomain_coordinateRing (isAffineVariety_affineProduct hV hW)
  let e : A ⊗[k] B ≃ₐ[k] coordinateRing (affineProduct V W) :=
    (Algebra.TensorProduct.congr eV.symm eW.symm).trans (coordinateRing_affineProductEquiv V W).symm
  exact e.injective.isDomain e

variable {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]

/-- The kernel of `A ⊗_k B → A/𝔭 ⊗_k B/𝔮`, the ideal of `V(𝔭) × V(𝔮)` in `Spec (A ⊗_k B)`. -/
noncomputable def tensorKer (p : Ideal A) (q : Ideal B) : Ideal (A ⊗[k] B) :=
  RingHom.ker (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k p) (Ideal.Quotient.mkₐ k q))

/-- An ideal containing the extensions of `𝔭` and `𝔮` contains `tensorKer k 𝔭 𝔮`. -/
theorem tensorKer_le {p : Ideal A} {q : Ideal B} {Q : Ideal (A ⊗[k] B)}
    (hp : p ≤ Q.comap (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[k] B))
    (hq : q ≤ Q.comap (Algebra.TensorProduct.includeRight : B →ₐ[k] A ⊗[k] B)) :
    tensorKer k p q ≤ Q := by
  have hkp : RingHom.ker (Ideal.Quotient.mkₐ k p) = p := by
    ext; simp [Ideal.Quotient.eq_zero_iff_mem]
  have hkq : RingHom.ker (Ideal.Quotient.mkₐ k q) = q := by
    ext; simp [Ideal.Quotient.eq_zero_iff_mem]
  rw [tensorKer, Algebra.TensorProduct.map_ker _ _ (Ideal.Quotient.mkₐ_surjective k p)
    (Ideal.Quotient.mkₐ_surjective k q), hkp, hkq]
  exact sup_le (Ideal.map_le_iff_le_comap.2 hp) (Ideal.map_le_iff_le_comap.2 hq)

/-- `tensorKer k 𝔭 𝔮` lies over `𝔭`. -/
theorem comap_includeLeft_tensorKer (p : Ideal A) (q : Ideal B) [q.IsPrime] :
    (tensorKer k p q).comap (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[k] B) = p := by
  have hinj := Algebra.TensorProduct.includeLeft_injective (R := k) (S := k) (A := A ⧸ p)
    (B := B ⧸ q) (algebraMap k (B ⧸ q)).injective
  ext a
  simp only [Ideal.mem_comap, tensorKer, RingHom.mem_ker,
    Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.map_tmul,
    Ideal.Quotient.mkₐ_eq_mk, map_one]
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro h
    apply hinj
    simpa using h
  · intro h
    simp [h]

/-- `tensorKer k 𝔭 𝔮` lies over `𝔮`. -/
theorem comap_includeRight_tensorKer (p : Ideal A) [p.IsPrime] (q : Ideal B) :
    (tensorKer k p q).comap (Algebra.TensorProduct.includeRight : B →ₐ[k] A ⊗[k] B) = q := by
  have hinj := Algebra.TensorProduct.includeRight_injective (R := k) (A := A ⧸ p)
    (B := B ⧸ q) (algebraMap k (A ⧸ p)).injective
  ext b
  simp only [Ideal.mem_comap, tensorKer, RingHom.mem_ker,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul,
    Ideal.Quotient.mkₐ_eq_mk, map_one]
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro h
    apply hinj
    simpa using h
  · intro h
    simp [h]

variable [IsAlgClosed k] [Algebra.FiniteType k A] [Algebra.FiniteType k B]

/-- `tensorKer k 𝔭 𝔮` is prime: `A/𝔭 ⊗_k B/𝔮` is a domain. -/
theorem isPrime_tensorKer (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] :
    (tensorKer k p q).IsPrime := by
  have : Algebra.FiniteType k (A ⧸ p) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k p) Ideal.Quotient.mk_surjective
  have : Algebra.FiniteType k (B ⧸ q) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k q) Ideal.Quotient.mk_surjective
  have : IsDomain ((A ⧸ p) ⊗[k] (B ⧸ q)) := isDomain_tensorProduct k _ _
  exact RingHom.ker_isPrime _

variable [IsDomain A] [IsDomain B]

/-- **Height of a product.** For primes `𝔭 ⊆ A` and `𝔮 ⊆ B` of finitely generated domains over
an algebraically closed field, the prime of `V(𝔭) × V(𝔮)` in `A ⊗_k B` has height
`ht 𝔭 + ht 𝔮`. -/
theorem height_tensorKer (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] :
    (tensorKer k p q).height = p.height + q.height := by
  have : Algebra.FiniteType k (A ⧸ p) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k p) Ideal.Quotient.mk_surjective
  have : Algebra.FiniteType k (B ⧸ q) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k q) Ideal.Quotient.mk_surjective
  have : Algebra.FiniteType k (A ⊗[k] B) := Algebra.FiniteType.trans (S := A) ‹_› inferInstance
  have : IsDomain (A ⊗[k] B) := isDomain_tensorProduct k A B
  have : IsDomain ((A ⧸ p) ⊗[k] (B ⧸ q)) := isDomain_tensorProduct k _ _
  have : (tensorKer k p q).IsPrime := isPrime_tensorKer k p q
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  have : IsNoetherianRing (A ⊗[k] B) := Algebra.FiniteType.isNoetherianRing k _
  obtain ⟨h, hh⟩ : ∃ h : ℕ, (tensorKer k p q).height = h :=
    ENat.ne_top_iff_exists.mp Ideal.height_ne_top_of_isPrime |>.imp fun _ e => e.symm
  obtain ⟨a, ha⟩ : ∃ a : ℕ, p.height = a :=
    ENat.ne_top_iff_exists.mp Ideal.height_ne_top_of_isPrime |>.imp fun _ e => e.symm
  obtain ⟨b, hb⟩ : ∃ b : ℕ, q.height = b :=
    ENat.ne_top_iff_exists.mp Ideal.height_ne_top_of_isPrime |>.imp fun _ e => e.symm
  let e : ((A ⊗[k] B) ⧸ (tensorKer k p q : Ideal (A ⊗[k] B))) ≃ₐ[k] (A ⧸ p) ⊗[k] (B ⧸ q) :=
    Ideal.quotientKerAlgEquivOfSurjective (Algebra.TensorProduct.map_surjective _ _
      (Ideal.Quotient.mkₐ_surjective k p) (Ideal.Quotient.mkₐ_surjective k q))
  have h1 := height_add_ringKrullDim_quotient_eq k (A ⊗[k] B) (tensorKer k p q) h hh
  have h2 := height_add_ringKrullDim_quotient_eq k A p a ha
  have h3 := height_add_ringKrullDim_quotient_eq k B q b hb
  rw [RingEquiv.ringKrullDim e.toRingEquiv, ringKrullDim_tensorProduct k (A ⧸ p) (B ⧸ q),
    ringKrullDim_tensorProduct k A B] at h1
  obtain ⟨dA, hdA, -⟩ := exists_ringKrullDim_eq_trdeg k A (FractionRing A)
  obtain ⟨dB, hdB, -⟩ := exists_ringKrullDim_eq_trdeg k B (FractionRing B)
  obtain ⟨dA', hdA', -⟩ := exists_ringKrullDim_eq_trdeg k (A ⧸ p) (FractionRing (A ⧸ p))
  obtain ⟨dB', hdB', -⟩ := exists_ringKrullDim_eq_trdeg k (B ⧸ q) (FractionRing (B ⧸ q))
  rw [hdA, hdB, hdA', hdB'] at h1
  rw [hdA, hdA'] at h2
  rw [hdB, hdB'] at h3
  have h1' : h + (dA' + dB') = dA + dB := by exact_mod_cast h1
  have h2' : a + dA' = dA := by exact_mod_cast h2
  have h3' : b + dB' = dB := by exact_mod_cast h3
  rw [hh, ha, hb]
  exact_mod_cast (by omega : h = a + b)

end Algebra

section Scheme

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (pX : X ⟶ Spec (.of k))
  (pY : Y ⟶ Spec (.of k))

/-- **The product chart.** Let `Spec A = U ⊆ X` and `Spec B = V ⊆ Y` be affine opens containing
`x` and `y`. The point `ξ` of `Spec (A ⊗_k B) ⊆ X × Y` given by the prime of
`closure {x} × closure {y}` lies over `x` and `y`, has finite coheight
`coheight x + coheight y`, and specializes to every point of
`fst⁻¹ (closure {x} ∩ U) ∩ snd⁻¹ (closure {y} ∩ V)`. -/
theorem exists_chart [IsAlgClosed k] [IsIntegral X] [IsIntegral Y] [LocallyOfFiniteType pX]
    [LocallyOfFiniteType pY] {x : X} {y : Y} {U : X.Opens} (hU : IsAffineOpen U) (hxU : x ∈ U)
    {V : Y.Opens} (hV : IsAffineOpen V) (hyV : y ∈ V) :
    ∃ ξ : ↑(pullback pX pY), pullback.fst pX pY ξ = x ∧ pullback.snd pX pY ξ = y ∧
      coheight ξ ≠ ⊤ ∧ coheight ξ = coheight x + coheight y ∧
      ∀ z : ↑(pullback pX pY), pullback.fst pX pY z ∈ U → pullback.snd pX pY z ∈ V →
        x ⤳ pullback.fst pX pY z → y ⤳ pullback.snd pX pY z → ξ ⤳ z := by
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  have : Nonempty V := ⟨⟨y, hyV⟩⟩
  -- the `k`-algebra structures on `Γ(X, U)` and `Γ(Y, V)` coming from `pX` and `pY`
  let a : CommRingCat.of k ⟶ Γ(X, U) := Spec.preimage (hU.fromSpec ≫ pX)
  let _ : Algebra k Γ(X, U) := a.hom.toAlgebra
  have hφA : Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U))) = hU.fromSpec ≫ pX := by
    change Spec.map (CommRingCat.ofHom a.hom) = _
    simp [a]
  have : Algebra.FiniteType k Γ(X, U) := by
    have : LocallyOfFiniteType (Spec.map a) := by rw [Spec.map_preimage]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this
  let b : CommRingCat.of k ⟶ Γ(Y, V) := Spec.preimage (hV.fromSpec ≫ pY)
  let _ : Algebra k Γ(Y, V) := b.hom.toAlgebra
  have hφB : Spec.map (CommRingCat.ofHom (algebraMap k Γ(Y, V))) = hV.fromSpec ≫ pY := by
    change Spec.map (CommRingCat.ofHom b.hom) = _
    simp [b]
  have : Algebra.FiniteType k Γ(Y, V) := by
    have : LocallyOfFiniteType (Spec.map b) := by rw [Spec.map_preimage]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this
  have : IsNoetherianRing Γ(X, U) := Algebra.FiniteType.isNoetherianRing k _
  have : IsNoetherianRing Γ(Y, V) := Algebra.FiniteType.isNoetherianRing k _
  -- the chart `Spec (Γ(X, U) ⊗_k Γ(Y, V)) ⟶ X × Y`
  let E : Spec (.of (Γ(X, U) ⊗[k] Γ(Y, V))) ≅ pullback (hU.fromSpec ≫ pX) (hV.fromSpec ≫ pY) :=
    (pullbackSpecIso k Γ(X, U) Γ(Y, V)).symm ≪≫ pullback.congrHom hφA hφB
  let m : pullback (hU.fromSpec ≫ pX) (hV.fromSpec ≫ pY) ⟶ pullback pX pY :=
    pullback.map _ _ pX pY hU.fromSpec hV.fromSpec (𝟙 _) (by simp) (by simp)
  let ψ : Spec (.of (Γ(X, U) ⊗[k] Γ(Y, V))) ⟶ pullback pX pY := E.hom ≫ m
  have hψfst : ψ ≫ pullback.fst pX pY =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫ hU.fromSpec := by
    simp only [ψ, E, m, Iso.trans_hom, Iso.symm_hom, pullback.congrHom_hom, Category.assoc,
      pullback.lift_fst, pullback.lift_fst_assoc, Category.comp_id, pullbackSpecIso_inv_fst_assoc]
  have hψsnd : ψ ≫ pullback.snd pX pY =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        Γ(Y, V) →ₐ[k] Γ(X, U) ⊗[k] Γ(Y, V)).toRingHom) ≫ hV.fromSpec := by
    simp only [ψ, E, m, Iso.trans_hom, Iso.symm_hom, pullback.congrHom_hom, Category.assoc,
      pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id, pullbackSpecIso_inv_snd_assoc]
    rfl
  have hfst : ∀ w, pullback.fst pX pY (ψ w) = hU.fromSpec
      (Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) w) := fun w => by
    rw [← Scheme.Hom.comp_apply, hψfst, Scheme.Hom.comp_apply]
  have hsnd : ∀ w, pullback.snd pX pY (ψ w) = hV.fromSpec
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        Γ(Y, V) →ₐ[k] Γ(X, U) ⊗[k] Γ(Y, V)).toRingHom) w) := fun w => by
    rw [← Scheme.Hom.comp_apply, hψsnd, Scheme.Hom.comp_apply]
  -- the primes of `x` and `y`, and the prime of `closure {x} × closure {y}`
  let p : Spec Γ(X, U) := hU.primeIdealOf ⟨x, hxU⟩
  let q : Spec Γ(Y, V) := hV.primeIdealOf ⟨y, hyV⟩
  have hpx : hU.fromSpec p = x := hU.fromSpec_primeIdealOf ⟨x, hxU⟩
  have hqy : hV.fromSpec q = y := hV.fromSpec_primeIdealOf ⟨y, hyV⟩
  have := isPrime_tensorKer k p.asIdeal q.asIdeal
  let P : Spec (.of (Γ(X, U) ⊗[k] Γ(Y, V))) := ⟨tensorKer k p.asIdeal q.asIdeal, this⟩
  have hPl : Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) P = p := by
    rw [Spec.map_apply]
    exact PrimeSpectrum.ext (comap_includeLeft_tensorKer k p.asIdeal q.asIdeal)
  have hPr : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
      Γ(Y, V) →ₐ[k] Γ(X, U) ⊗[k] Γ(Y, V)).toRingHom) P = q := by
    rw [Spec.map_apply]
    exact PrimeSpectrum.ext (comap_includeRight_tensorKer k p.asIdeal q.asIdeal)
  -- coheights
  have hcohP : coheight (ψ P) = p.asIdeal.height + q.asIdeal.height := by
    have h1 : coheight (ψ P) = coheight P := coheight_eq_of_isOpenImmersion ψ
    have h2 : P.asIdeal.height = coheight P := idealHeight_eq_coheight _ P
    rw [← height_tensorKer k p.asIdeal q.asIdeal, h1, ← h2]
  have hcohx : coheight x = p.asIdeal.height := by
    have h1 : coheight (hU.fromSpec p) = coheight p := coheight_eq_of_isOpenImmersion hU.fromSpec
    have h2 : p.asIdeal.height = coheight p := idealHeight_eq_coheight _ p
    rw [h2, ← h1, hpx]
  have hcohy : coheight y = q.asIdeal.height := by
    have h1 : coheight (hV.fromSpec q) = coheight q := coheight_eq_of_isOpenImmersion hV.fromSpec
    have h2 : q.asIdeal.height = coheight q := idealHeight_eq_coheight _ q
    rw [h2, ← h1, hqy]
  refine ⟨ψ P, by rw [hfst, hPl, hpx], by rw [hsnd, hPr, hqy], ?_, by rw [hcohP, hcohx, hcohy],
    ?_⟩
  · rw [hcohP]
    exact WithTop.add_ne_top.2 ⟨Ideal.height_ne_top_of_isPrime, Ideal.height_ne_top_of_isPrime⟩
  · intro z hzU hzV hxz hyz
    -- `z` lies in the chart
    obtain ⟨w, hw⟩ : z ∈ Set.range m := by
      rw [Scheme.Pullback.range_map, hU.range_fromSpec, hV.range_fromSpec]
      exact ⟨hzU, hzV⟩
    have hψw : ψ (E.inv w) = z := by
      rw [← hw, ← Scheme.Hom.comp_apply]
      simp [ψ]
    rw [← hψw] at hxz hyz ⊢
    rw [hfst, ← hpx, hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff] at hxz
    rw [hsnd, ← hqy, hV.fromSpec.isOpenEmbedding.isInducing.specializes_iff] at hyz
    have hx' : p.asIdeal ≤ (E.inv w).asIdeal.comap
        (Algebra.TensorProduct.includeLeftRingHom : Γ(X, U) →+* Γ(X, U) ⊗[k] Γ(Y, V)) :=
      (PrimeSpectrum.le_iff_specializes _ _).2 hxz
    have hy' : q.asIdeal ≤ (E.inv w).asIdeal.comap
        (Algebra.TensorProduct.includeRight : Γ(Y, V) →ₐ[k] Γ(X, U) ⊗[k] Γ(Y, V)) :=
      (PrimeSpectrum.le_iff_specializes _ _).2 hyz
    exact Specializes.map ((PrimeSpectrum.le_iff_specializes P (E.inv w)).1
      (tensorKer_le k hx' hy')) ψ.continuous

/-- For `V = closure {x}` and `W = closure {y}`, the set `V × W = fst⁻¹ V ∩ snd⁻¹ W` is the
closure of a point whose coheight is `coheight x + coheight y`. -/
theorem exists_closure_eq_preimage_inter [IsAlgClosed k] [IsIntegral X] [IsIntegral Y]
    [LocallyOfFiniteType pX] [LocallyOfFiniteType pY] (x : X) (y : Y) :
    ∃ ξ : ↑(pullback pX pY), closure {ξ} =
        pullback.fst pX pY ⁻¹' closure {x} ∩ pullback.snd pX pY ⁻¹' closure {y} ∧
      coheight ξ = coheight x + coheight y := by
  have cover : ∀ {Z : Scheme.{u}} (z : Z), ∃ U : Z.Opens, IsAffineOpen U ∧ z ∈ U := by
    intro Z z
    obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ :=
      Z.isBasis_affineOpens.exists_subset_of_mem_open (show z ∈ (⊤ : Z.Opens) from trivial)
        isOpen_univ
    exact ⟨U, hU, hzU⟩
  obtain ⟨U, hU, hxU⟩ := cover x
  obtain ⟨V, hV, hyV⟩ := cover y
  obtain ⟨ξ, hξ1, hξ2, -, hcoh, -⟩ := exists_chart pX pY hU hxU hV hyV
  refine ⟨ξ, subset_antisymm ?_ ?_, hcoh⟩
  · refine closure_minimal (Set.singleton_subset_iff.2 ⟨?_, ?_⟩)
      ((isClosed_closure.preimage (pullback.fst pX pY).continuous).inter
        (isClosed_closure.preimage (pullback.snd pX pY).continuous))
    · rw [Set.mem_preimage, hξ1]
      exact subset_closure rfl
    · rw [Set.mem_preimage, hξ2]
      exact subset_closure rfl
  · rintro z ⟨hz1, hz2⟩
    have hxz : x ⤳ pullback.fst pX pY z := specializes_iff_mem_closure.2 hz1
    have hyz : y ⤳ pullback.snd pX pY z := specializes_iff_mem_closure.2 hz2
    obtain ⟨U', hU', hzU'⟩ := cover (pullback.fst pX pY z)
    obtain ⟨V', hV', hzV'⟩ := cover (pullback.snd pX pY z)
    have hxU' : x ∈ U' := hxz.mem_open U'.isOpen hzU'
    have hyV' : y ∈ V' := hyz.mem_open V'.isOpen hzV'
    obtain ⟨ξ', -, -, hfin', hcoh', hspec'⟩ := exists_chart pX pY hU' hxU' hV' hyV'
    have hξ'ξ : ξ' ⤳ ξ := hspec' ξ (by rwa [hξ1]) (by rwa [hξ2]) (by rw [hξ1]) (by rw [hξ2])
    have hξ'z : ξ' ⤳ z := hspec' z hzU' hzV' hxz hyz
    have heq : ξ' = ξ := by
      by_contra hne
      have hle : ξ ≤ ξ' := hξ'ξ
      have hlt : ξ < ξ' := lt_of_le_not_ge hle fun h => hne (hξ'ξ.antisymm h).eq
      have := coheight_strictAnti hlt (lt_top_iff_ne_top.2 hfin')
      rw [hcoh, hcoh'] at this
      exact lt_irrefl _ this
    rw [← heq]
    exact specializes_iff_mem_closure.1 hξ'z

end Scheme

end ExternalProduct

open ExternalProduct

section Scheme

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (pX : X ⟶ Spec (.of k))
  (pY : Y ⟶ Spec (.of k)) [IsAlgClosed k] [IsIntegral X] [IsIntegral Y] [LocallyOfFiniteType pX]
  [LocallyOfFiniteType pY]

/-- The generic point of `closure {x} × closure {y}` in `X ×_k Y`. -/
noncomputable def externalProductPoint (x : X) (y : Y) : ↑(pullback pX pY) :=
  (exists_closure_eq_preimage_inter pX pY x y).choose

/-- The closure of `externalProductPoint pX pY x y` is `closure {x} × closure {y}`, that is,
`fst⁻¹ (closure {x}) ∩ snd⁻¹ (closure {y})`. -/
theorem closure_externalProductPoint (x : X) (y : Y) :
    closure {externalProductPoint pX pY x y} =
      pullback.fst pX pY ⁻¹' closure {x} ∩ pullback.snd pX pY ⁻¹' closure {y} :=
  (exists_closure_eq_preimage_inter pX pY x y).choose_spec.1

theorem coheight_externalProductPoint (x : X) (y : Y) :
    coheight (externalProductPoint pX pY x y) = coheight x + coheight y :=
  (exists_closure_eq_preimage_inter pX pY x y).choose_spec.2

omit [IsAlgClosed k] [IsIntegral X] [IsIntegral Y] [LocallyOfFiniteType pX]
  [LocallyOfFiniteType pY] in
private theorem codim_closure_singleton {Z : Scheme.{u}} (z : Z) :
    codim (closure ({z} : Set Z)) = coheight z := by
  have hirr : IsIrreducible (closure ({z} : Set Z)) := isIrreducible_singleton.closure
  have h := Scheme.coheight_genericPoint_eq_codim hirr isClosed_closure
  have hgen : hirr.genericPoint = z := by
    have h1 := hirr.isGenericPoint_genericPoint_closure
    rw [closure_closure] at h1
    exact h1.eq (isGenericPoint_closure)
  rw [hgen] at h
  exact h.symm

/-- **Codimension of a product.** `codim (V × W, X × Y) = codim (V, X) + codim (W, Y)` for
`V = closure {x}` and `W = closure {y}`. -/
theorem codim_closure_externalProductPoint (x : X) (y : Y) :
    codim (closure {externalProductPoint pX pY x y}) =
      codim (closure ({x} : Set X)) + codim (closure ({y} : Set Y)) := by
  rw [codim_closure_singleton, codim_closure_singleton, codim_closure_singleton,
    coheight_externalProductPoint]

open scoped Classical in
/-- The product cycle `[V × W]` for `V = closure {x}` and `W = closure {y}`. -/
noncomputable def externalProductGenerator (x : X) (y : Y) : AlgebraicCycle (pullback pX pY) ℤ :=
  Function.locallyFinsuppWithin.single (externalProductPoint pX pY x y) 1

/-- The bilinear extension of `[V] ⊗ [W] ↦ [V × W]`, with values in all algebraic cycles. -/
noncomputable def externalProductUngraded (r s : ℕ) :
    codimensionCycles X r →+ codimensionCycles Y s →+ AlgebraicCycle (pullback pX pY) ℤ :=
  ((Finsupp.liftAddHom fun x => zmultiplesHom _
      (Finsupp.liftAddHom fun y => zmultiplesHom _ (externalProductGenerator pX pY x y))).compl₂
    (codimensionCyclesToFinsupp s)).comp (codimensionCyclesToFinsupp r)

theorem externalProductUngraded_apply {r s : ℕ} (c : codimensionCycles X r)
    (d : codimensionCycles Y s) :
    externalProductUngraded pX pY r s c d =
      ∑ x ∈ c.2.1.toFinset, ∑ y ∈ d.2.1.toFinset,
        ((c : AlgebraicCycle X ℤ) x * (d : AlgebraicCycle Y ℤ) y) •
          externalProductGenerator pX pY x y := by
  simp only [externalProductUngraded, AddMonoidHom.comp_apply, AddMonoidHom.compl₂_apply,
    Finsupp.liftAddHom_apply, Finsupp.sum, AddMonoidHom.finsetSum_apply, zmultiplesHom_apply,
    AddMonoidHom.coe_smul, Pi.smul_apply, Finset.smul_sum, smul_smul]
  rfl

/-- A point in the support of the external product of `c` and `d` is
`externalProductPoint pX pY x y` for `x` in the support of `c` and `y` in the support of `d`. -/
theorem exists_of_mem_support_externalProductUngraded {r s : ℕ} (c : codimensionCycles X r)
    (d : codimensionCycles Y s) {z : ↑(pullback pX pY)}
    (hz : z ∈ (externalProductUngraded pX pY r s c d).support) :
    ∃ x ∈ (c : AlgebraicCycle X ℤ).support, ∃ y ∈ (d : AlgebraicCycle Y ℤ).support,
      externalProductPoint pX pY x y = z := by
  classical
  have hz' : externalProductUngraded pX pY r s c d z ≠ 0 := hz
  rw [externalProductUngraded_apply, Function.locallyFinsuppWithin.coe_sum,
    Finset.sum_apply] at hz'
  obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz'
  rw [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply] at hne
  obtain ⟨y, hy, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  simp only [Function.locallyFinsuppWithin.coe_zsmul, Pi.smul_apply, externalProductGenerator,
    Function.locallyFinsuppWithin.single_apply, smul_eq_mul] at hne
  by_cases hzx : z = externalProductPoint pX pY x y
  · exact ⟨x, c.2.1.mem_toFinset.mp hx, y, d.2.1.mem_toFinset.mp hy, hzx.symm⟩
  · rw [if_neg hzx, mul_zero] at hne
    exact absurd rfl hne

/-- The external product of a codimension-`r` and a codimension-`s` cycle is a codimension-`(r + s)`
cycle. -/
theorem externalProductUngraded_mem {r s : ℕ} (c : codimensionCycles X r)
    (d : codimensionCycles Y s) :
    externalProductUngraded pX pY r s c d ∈ codimensionCycles (pullback pX pY) (r + s) := by
  refine ⟨((c.2.1.prod d.2.1).image fun xy => externalProductPoint pX pY xy.1 xy.2).subset
    fun z hz => ?_, fun z hz => ?_⟩
  · obtain ⟨x, hx, y, hy, rfl⟩ := exists_of_mem_support_externalProductUngraded pX pY c d hz
    exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩
  · obtain ⟨x, hx, y, hy, rfl⟩ := exists_of_mem_support_externalProductUngraded pX pY c d hz
    rw [codim_closure_externalProductPoint, c.2.2 x hx, d.2.2 y hy]
    norm_cast

/-- **External product of cycles**, the product cycle of Hartshorne, Appendix A.1, axiom A5.
Let `X` and `Y` be integral schemes locally of finite type over an algebraically closed field `k`.
Sending `[V] ⊗ [W]`, for irreducible closed subsets `V ⊆ X` of codimension `r` and `W ⊆ Y` of
codimension `s`, to the cycle `[V × W]` of `X ×_k Y` (`externalProductGenerator`, the irreducible
closed subset `fst⁻¹ V ∩ snd⁻¹ W` with coefficient one) and extending bilinearly gives a
bilinear map `Z^r(X) × Z^s(Y) → Z^{r+s}(X ×_k Y)`. -/
noncomputable def externalProduct (r s : ℕ) :
    codimensionCycles X r →+ codimensionCycles Y s →+
      codimensionCycles (pullback pX pY) (r + s) :=
  AddMonoidHom.mk' (fun c => (externalProductUngraded pX pY r s c).codRestrict _
      (externalProductUngraded_mem pX pY c))
    fun c c' => by
      ext d : 1
      apply Subtype.ext
      simp

/-- The external product is the bilinear extension of `[V] ⊗ [W] ↦ [V × W]`. -/
theorem coe_externalProduct {r s : ℕ} (c : codimensionCycles X r) (d : codimensionCycles Y s) :
    (externalProduct pX pY r s c d : AlgebraicCycle (pullback pX pY) ℤ) =
      ∑ x ∈ c.2.1.toFinset, ∑ y ∈ d.2.1.toFinset,
        ((c : AlgebraicCycle X ℤ) x * (d : AlgebraicCycle Y ℤ) y) •
          externalProductGenerator pX pY x y :=
  externalProductUngraded_apply pX pY c d

open scoped Classical in
/-- **Value on generators.** For the cycles `[V]` of `V = closure {x}` (of codimension `r`) and
`[W]` of `W = closure {y}` (of codimension `s`), the external product is the cycle `[V × W]` of
`closure {externalProductPoint pX pY x y} = fst⁻¹ V ∩ snd⁻¹ W`. -/
theorem externalProduct_apply_of_eq_single {r s : ℕ} {c : codimensionCycles X r}
    {d : codimensionCycles Y s} {x : X} {y : Y}
    (hc : (c : AlgebraicCycle X ℤ) = Function.locallyFinsuppWithin.single x 1)
    (hd : (d : AlgebraicCycle Y ℤ) = Function.locallyFinsuppWithin.single y 1) :
    (externalProduct pX pY r s c d : AlgebraicCycle (pullback pX pY) ℤ) =
      Function.locallyFinsuppWithin.single (externalProductPoint pX pY x y) 1 := by
  have hcx : ∀ x', (c : AlgebraicCycle X ℤ) x' = if x' = x then 1 else 0 := fun x' => by
    rw [hc, Function.locallyFinsuppWithin.single_apply]
  have hdy : ∀ y', (d : AlgebraicCycle Y ℤ) y' = if y' = y then 1 else 0 := fun y' => by
    rw [hd, Function.locallyFinsuppWithin.single_apply]
  have hxs : x ∈ c.2.1.toFinset := c.2.1.mem_toFinset.mpr (by simp [Function.mem_support, hcx])
  have hys : y ∈ d.2.1.toFinset := d.2.1.mem_toFinset.mpr (by simp [Function.mem_support, hdy])
  rw [coe_externalProduct, Finset.sum_eq_single_of_mem x hxs, Finset.sum_eq_single_of_mem y hys]
  · simp [hcx, hdy, externalProductGenerator]
  · intro y' _ hy'
    simp [hdy, hy']
  · intro x' _ hx'
    simp [hcx, hx']

end Scheme

end Hartshorne

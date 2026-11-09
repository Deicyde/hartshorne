/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Surface.LocalEquation
import Hartshorne.Scheme.AffineUFDClassGroup
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.LocalRing.Length

/-!
# Local intersection multiplicity of curves on a surface

Hartshorne, *Algebraic Geometry*, V.1, before Proposition 1.4 (p. 360).

For curves `C, D` on a surface and a point `P`, with local equations `f, g ∈ 𝒪_{X,P}`,
`(C.D)_P = length_{𝒪_{X,P}} (𝒪_{X,P} / (f, g))`
(`Hartshorne.Surface.localIntersectionMultiplicity`). It does not depend on the local equations
(`localIntersectionMultiplicity_eq`); when `C` and `D` have no common irreducible component it is
finite (`localIntersectionMultiplicity_ne_top`); at a closed point it is the dimension over `k` of
`𝒪_{X,P}/(f, g)` (`localIntersectionMultiplicity_eq_rank`). The definition makes sense at every
point `P`; it is `0` off `C ∩ D`.
-/

universe u

open AlgebraicGeometry CategoryTheory Limits Order TopologicalSpace IsLocalRing

namespace Hartshorne

namespace Surface

noncomputable section

variable {k : Type u} [Field k] [IsAlgClosed k] (S : Surface k)

/-- The **local intersection multiplicity** `(C.D)_P = length_{𝒪_{X,P}} (𝒪_{X,P} / (f, g))` for
local equations `f, g` of `C, D` at `P`. -/
def localIntersectionMultiplicity (C D : S.Curve) (P : S.X) : ℕ∞ :=
  Module.length (S.X.presheaf.stalk P) (S.X.presheaf.stalk P ⧸
    Ideal.span {(exists_isLocalEquation C P).choose, (exists_isLocalEquation D P).choose})

variable {S}

private theorem span_pair_eq {R : Type*} [CommRing R] [IsDomain R] {f f' g g' : R} (hf : Associated f f')
    (hg : Associated g g') : Ideal.span {f, g} = Ideal.span {f', g'} := by
  rw [Ideal.span_insert, Ideal.span_insert, Ideal.span_singleton_eq_span_singleton.2 hf,
    Ideal.span_singleton_eq_span_singleton.2 hg]

/-- **Independence of the local equations.** `(C.D)_P` is the length of `𝒪_{X,P}/(f, g)` for any
local equations `f, g` of `C, D` at `P`. -/
theorem localIntersectionMultiplicity_eq {C D : S.Curve} {P : S.X} {f g : S.X.presheaf.stalk P}
    (hf : S.IsLocalEquation C.1 P f) (hg : S.IsLocalEquation D.1 P g) :
    S.localIntersectionMultiplicity C D P =
      Module.length (S.X.presheaf.stalk P) (S.X.presheaf.stalk P ⧸ Ideal.span {f, g}) := by
  rw [localIntersectionMultiplicity,
    span_pair_eq ((exists_isLocalEquation C P).choose_spec.associated hf)
      ((exists_isLocalEquation D P).choose_spec.associated hg)]

/-- A prime `𝔭` of `𝒪_{X,P}` other than `0` and the maximal ideal comes from a codimension-one
point `z` of any affine neighbourhood `V` of `P`, at which every nonzero element of `𝔭` has
positive order. -/
theorem exists_codimOne_of_prime {P : S.X} {V : S.X.Opens} (hV : IsAffineOpen V) (hPV : P ∈ V)
    (𝔭 : Ideal (S.X.presheaf.stalk P)) [𝔭.IsPrime] (hm : 𝔭 ≠ maximalIdeal _) (h0 : 𝔭 ≠ ⊥) :
    ∃ z ∈ V, coheight z = 1 ∧ ∀ h ∈ 𝔭, h ≠ 0 →
      0 < S.X.ord (algebraMap (S.X.presheaf.stalk P) S.X.functionField h) z := by
  let A := Γ(S.X, V)
  let _ : Algebra A (S.X.presheaf.stalk P) :=
    TopCat.Presheaf.algebra_section_stalk S.X.presheaf ⟨P, hPV⟩
  have : Nonempty V := ⟨⟨P, hPV⟩⟩
  have : IsDomain A := inferInstance
  set m := (hV.primeIdealOf ⟨P, hPV⟩).asIdeal with hm_def
  have : IsLocalization.AtPrime (S.X.presheaf.stalk P) m := hV.isLocalization_stalk ⟨P, hPV⟩
  set q := 𝔭.comap (algebraMap A (S.X.presheaf.stalk P)) with hq_def
  have hq : q.IsPrime := Ideal.comap_isPrime _ _
  have hmap : q.map (algebraMap A (S.X.presheaf.stalk P)) = 𝔭 :=
    IsLocalization.map_under m.primeCompl _ 𝔭
  have hqm : q ≤ m := by
    intro a ha
    by_contra hna
    have hu : IsUnit (algebraMap A (S.X.presheaf.stalk P) a) :=
      IsLocalization.map_units (S.X.presheaf.stalk P) (⟨a, hna⟩ : m.primeCompl)
    exact (inferInstance : 𝔭.IsPrime).ne_top (Ideal.eq_top_of_isUnit_mem _ ha hu)
  have hqne : q ≠ m := by
    intro h
    apply hm
    rw [← hmap, h, IsLocalization.AtPrime.map_eq_maximalIdeal]
  have hq0 : q ≠ ⊥ := by
    intro h
    apply h0
    rw [← hmap, h, Ideal.map_bot]
  -- the point `z` of `q`
  set y : PrimeSpectrum A := ⟨q, hq⟩
  set z := hV.fromSpec y with hz_def
  have hzV : z ∈ V := by
    have : z ∈ (V : Set S.X) := hV.range_fromSpec ▸ ⟨y, rfl⟩
    exact this
  let _ : Algebra A (S.X.presheaf.stalk z) :=
    TopCat.Presheaf.algebra_section_stalk S.X.presheaf ⟨z, hzV⟩
  have : IsLocalization.AtPrime (S.X.presheaf.stalk z) q := hV.isLocalization_stalk' y hzV
  have hcoh_eq : (q.height : WithBot ℕ∞) = coheight z := by
    rw [← IsLocalization.AtPrime.ringKrullDim_eq_height q (S.X.presheaf.stalk z),
      ringKrullDim_stalk_eq_coheight]
  -- `z` specializes to `P` and is different from it
  have hPm : hV.fromSpec (hV.primeIdealOf ⟨P, hPV⟩) = P := hV.fromSpec_primeIdealOf ⟨P, hPV⟩
  have hzP : z ⤳ P := by
    rw [← hPm]
    exact (PrimeSpectrum.le_iff_specializes y (hV.primeIdealOf ⟨P, hPV⟩)).1 hqm |>.map
      hV.fromSpec.continuous
  have hzneP : z ≠ P := by
    intro h
    apply hqne
    have hinj := hV.fromSpec.isOpenEmbedding.injective
    have : y = hV.primeIdealOf ⟨P, hPV⟩ := hinj (by rw [hPm]; exact h)
    exact congrArg PrimeSpectrum.asIdeal this
  have hlt : P < z := ⟨hzP, fun h ↦ hzneP (hzP.antisymm h).eq⟩
  have hkd : krullDim S.X = 2 := by
    rw [← krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := S.X))]
    exact S.dim_eq
  have hP2 : (coheight P : WithBot ℕ∞) ≤ 2 := hkd ▸ coheight_le_krullDim P
  have hadd : coheight z + 1 ≤ coheight P := coheight_add_one_le hlt
  have hz1 : coheight z = 1 := by
    have hne0 : coheight z ≠ 0 := by
      intro h
      rw [h] at hcoh_eq
      exact hq0 (Ideal.height_eq_zero_iff_eq_bot.1 (by exact_mod_cast hcoh_eq))
    have hP2' : coheight P ≤ 2 := WithBot.coe_le_coe.mp hP2
    have hle : coheight z + 1 ≤ 2 := hadd.trans hP2'
    obtain ⟨n, hn⟩ : ∃ n : ℕ, coheight z = n := by
      cases h : coheight z using ENat.recTopCoe with
      | top =>
        rw [h, top_add] at hle
        exact absurd (top_le_iff.1 hle) (by simp)
      | coe n => exact ⟨n, rfl⟩
    rw [hn] at hle hne0 ⊢
    norm_cast at hle hne0 ⊢
    omega
  refine ⟨z, hzV, hz1, fun h hh hh0 ↦ ?_⟩
  -- positivity of the order
  have hstar := Scheme.satisfiesConditionStar_of_isLocallyFactorial S.isLocallyFactorial
  have : IsDiscreteValuationRing (S.X.presheaf.stalk z) :=
    S.X.codimensionOneStalk_isDiscreteValuationRing hstar hz1
  have : IsScalarTower A (S.X.presheaf.stalk z) S.X.functionField :=
    functionField_isScalarTower S.X V ⟨z, hzV⟩
  have : IsScalarTower A (S.X.presheaf.stalk P) S.X.functionField :=
    functionField_isScalarTower S.X V ⟨P, hPV⟩
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective m.primeCompl h
  set K := S.X.functionField
  have hspec := IsLocalization.mk'_spec (S.X.presheaf.stalk P) a s
  have haq : a ∈ q := by
    change algebraMap A _ a ∈ 𝔭
    rw [← hspec]
    exact Ideal.mul_mem_right _ _ hh
  have hsq : (s : A) ∉ q := fun hs ↦ s.2 (hqm hs)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at hspec
    have hsu : IsUnit (algebraMap A (S.X.presheaf.stalk P) s) :=
      IsLocalization.map_units (S.X.presheaf.stalk P) s
    exact hh0 ((hsu.mul_left_eq_zero).1 hspec)
  have hinjA : Function.Injective (algebraMap A K) := by
    rw [IsScalarTower.algebraMap_eq A (S.X.presheaf.stalk z) K]
    exact (IsFractionRing.injective _ _).comp
      (IsLocalization.injective _ q.primeCompl_le_nonZeroDivisors)
  have haK : algebraMap A K a ≠ 0 := (map_ne_zero_iff _ hinjA).2 ha0
  have hsK : algebraMap A K s ≠ 0 :=
    (map_ne_zero_iff _ hinjA).2 (fun h ↦ hsq (h ▸ q.zero_mem))
  have hhK : algebraMap (S.X.presheaf.stalk P) K
      (IsLocalization.mk' (S.X.presheaf.stalk P) a s) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hh0
  have hprod : algebraMap (S.X.presheaf.stalk P) K (IsLocalization.mk' (S.X.presheaf.stalk P) a s) *
      algebraMap A K s = algebraMap A K a := by
    rw [IsScalarTower.algebraMap_apply A (S.X.presheaf.stalk P) K s,
      IsScalarTower.algebraMap_apply A (S.X.presheaf.stalk P) K a, ← map_mul, hspec]
  have hords : S.X.ord (algebraMap A K s) z = 0 := by
    rw [S.X.ord_eq_iff hz1 hsK]
    change Ring.ordFrac (S.X.presheaf.stalk z) (algebraMap A K s) = _
    rw [ofAdd_zero, WithZero.coe_one,
      ordFrac_algebraMap_eq_one_iff_notMem_of_isLocalizationAtPrime (R := S.X.presheaf.stalk z)
        (K := K) q (s : A)]
    exact hsq
  have horda : 0 < S.X.ord (algebraMap A K a) z := by
    have h1 : 1 ≤ Ring.ordFrac (S.X.presheaf.stalk z) (algebraMap A K a) :=
      one_le_ordFrac_algebraMap_of_isLocalizationAtPrime (R := S.X.presheaf.stalk z) q ha0
    have h2 : Ring.ordFrac (S.X.presheaf.stalk z) (algebraMap A K a) ≠ 1 := by
      rw [Ne, ordFrac_algebraMap_eq_one_iff_notMem_of_isLocalizationAtPrime
        (R := S.X.presheaf.stalk z) (K := K) q a, not_not]
      exact haq
    have hord := (S.X.ord_eq_iff hz1 haK (n := S.X.ord (algebraMap A K a) z)).1 rfl
    change Ring.ordFrac (S.X.presheaf.stalk z) (algebraMap A K a) = _ at hord
    rw [hord] at h1 h2
    have h3 : (1 : WithZero (Multiplicative ℤ)) <
        ((Multiplicative.ofAdd (S.X.ord (algebraMap A K a) z) : Multiplicative ℤ) :
          WithZero (Multiplicative ℤ)) :=
      lt_of_le_of_ne h1 (Ne.symm h2)
    rw [← WithZero.coe_one, WithZero.coe_lt_coe, ← ofAdd_zero, Multiplicative.ofAdd_lt] at h3
    exact h3
  have hm := S.X.ord_mul (x := z) hhK hsK
  rw [hprod, hords, add_zero] at hm
  rw [← hm]
  exact horda

/-- **Finiteness.** If `C` and `D` have no common irreducible component, `(C.D)_P` is finite. -/
theorem localIntersectionMultiplicity_ne_top {C D : S.Curve}
    (hCD : ∀ y : S.X, coheight y = 1 → ¬ (0 < C.1.1 y ∧ 0 < D.1.1 y)) (P : S.X) :
    S.localIntersectionMultiplicity C D P ≠ ⊤ := by
  obtain ⟨f, hf⟩ := exists_isLocalEquation C P
  obtain ⟨g, hg⟩ := exists_isLocalEquation D P
  rw [localIntersectionMultiplicity_eq hf hg]
  obtain ⟨hf0, U, hPU, hU⟩ := hf
  obtain ⟨hg0, U', hPU', hU'⟩ := hg
  obtain ⟨_, ⟨V, hV, rfl⟩, hPV, hVU⟩ :=
    S.X.isBasis_affineOpens.exists_subset_of_mem_open (show P ∈ U ⊓ U' from ⟨hPU, hPU'⟩)
      (U ⊓ U').isOpen
  have hprime : ∀ 𝔭 : Ideal (S.X.presheaf.stalk P), 𝔭.IsPrime → Ideal.span {f, g} ≤ 𝔭 →
      𝔭 = maximalIdeal (S.X.presheaf.stalk P) := by
    intro 𝔭 _ hI
    by_contra hm
    have hf𝔭 : f ∈ 𝔭 := hI (Ideal.subset_span (Set.mem_insert _ _))
    have hg𝔭 : g ∈ 𝔭 := hI (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
    have h0 : 𝔭 ≠ ⊥ := fun h ↦ hf0 (by rw [h] at hf𝔭; exact (Submodule.mem_bot _).1 hf𝔭)
    obtain ⟨z, hzV, hz1, hpos⟩ := exists_codimOne_of_prime hV hPV 𝔭 hm h0
    have hzU := hVU hzV
    refine hCD z hz1 ⟨?_, ?_⟩
    · rw [← hU z hzU.1 hz1]
      exact hpos f hf𝔭 hf0
    · rw [← hU' z hzU.2 hz1]
      exact hpos g hg𝔭 hg0
  have : Ring.KrullDimLE 0 (S.X.presheaf.stalk P ⧸ Ideal.span {f, g}) := by
    rw [Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal]
    intro J hJ
    have := hJ.1.1
    rw [hprime J this hJ.1.2]
    exact maximalIdeal.isMaximal _
  have : IsArtinianRing (S.X.presheaf.stalk P ⧸ Ideal.span {f, g}) :=
    isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.2 ⟨inferInstance, inferInstance⟩
  rw [Module.length_eq_of_surjective (R := S.X.presheaf.stalk P ⧸ Ideal.span {f, g})
    Ideal.Quotient.mk_surjective, Module.length_ne_top_iff, ← isArtinianRing_iff_isFiniteLength]
  infer_instance

variable (S) in
/-- The `k`-algebra structure map `k → 𝒪_{X,P}` of the stalk. -/
def stalkStructureMap (P : S.X) : k →+* S.X.presheaf.stalk P :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ S.hom.appTop ≫ S.X.presheaf.germ ⊤ P trivial).hom

theorem specMap_structureMap (P : S.X) :
    Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ S.hom.appTop ≫ S.X.Γevaluation P) =
      S.X.fromSpecResidueField P ≫ S.hom := by
  apply ext_of_isAffine
  rw [← cancel_mono (Scheme.ΓSpecIso (S.X.residueField P)).hom, Scheme.ΓSpecIso_naturality]
  simp only [Scheme.fromSpecResidueField, Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop,
    Category.assoc]
  rw [Iso.hom_inv_id_assoc, Scheme.ΓSpecIso_naturality]
  simp
  rfl

/-- At a closed point `P`, the residue field of `𝒪_{X,P}` is `k`: the map `k → κ(P)` induced by
the structure map is surjective. -/
theorem surjective_residue_comp_stalkStructureMap {P : S.X} (hP : IsClosed ({P} : Set S.X)) :
    Function.Surjective ((IsLocalRing.residue (S.X.presheaf.stalk P)).comp
      (S.stalkStructureMap P)) := by
  have hft : LocallyOfFiniteType S.hom := S.finiteType.1
  set ψ := (Scheme.ΓSpecIso (.of k)).inv ≫ S.hom.appTop ≫ S.X.Γevaluation P
  have h1 : Spec.preimage (S.X.fromSpecResidueField P ≫ S.hom) = ψ := by
    apply Spec.map_injective
    rw [Spec.map_preimage, specMap_structureMap]
  have h2 : (residueFieldIsoBase S.hom P hP).inv = ψ := h1
  intro y
  refine ⟨(residueFieldIsoBase S.hom P hP).hom y, ?_⟩
  have h3 := ConcreteCategory.congr_hom (residueFieldIsoBase S.hom P hP).hom_inv_id y
  rw [h2] at h3
  exact h3

/-- **The `k`-dimension.** At a closed point `P`, `(C.D)_P` is the dimension over `k` of
`𝒪_{X,P}/(f, g)` for local equations `f, g` of `C, D` at `P`. -/
theorem localIntersectionMultiplicity_eq_rank {C D : S.Curve} {P : S.X}
    (hP : IsClosed ({P} : Set S.X)) {f g : S.X.presheaf.stalk P}
    (hf : S.IsLocalEquation C.1 P f) (hg : S.IsLocalEquation D.1 P g) :
    letI := (S.stalkStructureMap P).toAlgebra
    (Module.rank k (S.X.presheaf.stalk P ⧸ Ideal.span {f, g})).toENat =
      S.localIntersectionMultiplicity C D P := by
  let _ := (S.stalkStructureMap P).toAlgebra
  have : IsLocalHom (algebraMap k (S.X.presheaf.stalk P)) := by
    refine ⟨fun a ha ↦ ?_⟩
    by_contra h0
    rw [isUnit_iff_ne_zero, not_not] at h0
    rw [h0, map_zero] at ha
    exact not_isUnit_zero ha
  have hsurj : Function.Surjective
      (algebraMap (ResidueField k) (ResidueField (S.X.presheaf.stalk P))) := by
    intro y
    obtain ⟨c, hc⟩ := surjective_residue_comp_stalkStructureMap hP y
    exact ⟨residue k c, by rw [IsLocalRing.ResidueField.algebraMap_residue]; exact hc⟩
  let e : ResidueField k ≃ₗ[ResidueField k] ResidueField (S.X.presheaf.stalk P) :=
    LinearEquiv.ofBijective
      (Algebra.linearMap (ResidueField k) (ResidueField (S.X.presheaf.stalk P)))
      ⟨RingHom.injective _, hsurj⟩
  have : IsSimpleModule (ResidueField k) (ResidueField (S.X.presheaf.stalk P)) :=
    IsSimpleModule.congr e.symm
  rw [localIntersectionMultiplicity_eq hf hg, ← Module.length_eq_rank,
    IsLocalRing.length_restrictScalars k (S.X.presheaf.stalk P),
    Module.length_eq_one (ResidueField k) (ResidueField (S.X.presheaf.stalk P)), mul_one]

end

end Surface

end Hartshorne

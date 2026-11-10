/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.RationalEquivalence
import Hartshorne.Scheme.AbsoluteNormalizationUniversal
import Hartshorne.Scheme.ClassGroupOpenRestriction

/-!
# Codimension-one rational equivalence on a normal variety is linear equivalence

Hartshorne, *Algebraic Geometry*, Appendix A.1 (p. 426).

Let `X` be a normal variety: a normal integral scheme, separated and of finite type over a field
`k`, of dimension `n`. Then `X` satisfies Hartshorne's condition `(*)`
(`satisfiesConditionStar_of_isNormal_of_finiteType`), so its Weil divisors are exactly its
codimension-one cycles (`weilDivisorToCodimOneCycles_bijective`). The only integral closed subscheme
of codimension `0` is `X` itself (`isIso_of_isClosedImmersion_of_codim_eq_zero`), and since `X` is
normal its normalization map is an isomorphism; the pushforward along an isomorphism sends the
principal divisor of a rational function to the principal divisor of the corresponding rational
function (`rawCyclePushforwardUngraded_principalDivisor_of_isIso`). Hence the rational-equivalence
subgroup of `Z^1(X)` is the subgroup of principal divisors
(`rationalEquivalenceSubgroup_one_eq_map_principalDivisorSubgroup`), rational equivalence of
codimension-one cycles is linear equivalence of Weil divisors
(`rationallyEquivalent_weilDivisorToCodimOneCycles_iff`), and `Z^1(X)` modulo rational equivalence
is the Weil divisor class group (`codimOneCycleClassEquivWeilClassGroup`).
-/

namespace Hartshorne

open AlgebraicGeometry CategoryTheory Limits Order TopologicalSpace

universe u

section Isomorphism

variable {X Y : Scheme.{u}}

/-- A scheme isomorphic to a normal scheme is normal. -/
theorem isNormal_of_isIso (e : Y ⟶ X) [IsIso e] [IsNormal X] : IsNormal Y where
  isDomain_stalk y := (asIso (e.stalkMap y)).symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  isIntegrallyClosed_stalk y :=
    IsIntegrallyClosed.of_equiv (asIso (e.stalkMap y)).commRingCatIsoToRingEquiv

/-- An open immersion induces isomorphisms of residue fields, so its residue degrees are `1`. -/
theorem residueDegree_eq_one_of_isOpenImmersion (f : Y ⟶ X) [IsOpenImmersion f] (y : Y) :
    f.residueDegree y = 1 := by
  let _ := (f.residueFieldMap y).hom.toAlgebra
  exact Module.finrank_of_bijective_algebraMap
    (IsLocalRing.ResidueField.mapEquiv (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv).bijective

variable {k : Type u} [Field k]

/-- The raw pushforward coefficients of an isomorphism of schemes of finite type over `k` are
all `1`. -/
theorem rawCyclePushforwardCoeff_eq_one_of_isIso (p : X ⟶ Spec (.of k)) (hp : FiniteType p)
    (e : Y ⟶ X) [IsIso e] (y : Y) : rawCyclePushforwardCoeff e y = 1 := by
  have := hp.1
  have := hp.2
  have hp' : FiniteType (e ≫ p) := ⟨inferInstance, inferInstance⟩
  have h1 := height_apply_le (e ≫ p) p hp' hp e rfl y
  have h2 := height_apply_le p (e ≫ p) hp hp' (inv e) (by simp) (e y)
  have hinv : (inv e) (e y) = y := by
    rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]; rfl
  rw [hinv] at h2
  have heq : height (e y) = height y := le_antisymm h1 h2
  rw [rawCyclePushforwardCoeff, rawCyclePushforward_closure_image_eq,
    FlatEquidimensional.topologicalKrullDim_closure_singleton,
    FlatEquidimensional.topologicalKrullDim_closure_singleton, heq, if_neg (lt_irrefl _),
    residueDegree_eq_one_of_isOpenImmersion, Nat.cast_one]

/-- The raw pushforward along an isomorphism `e` of schemes of finite type over `k` takes the
value `c y` at `e y`. -/
theorem rawCyclePushforwardUngraded_apply_of_isIso (p : X ⟶ Spec (.of k)) (hp : FiniteType p)
    (e : Y ⟶ X) [IsIso e] (r : ℕ) (c : codimensionCycles Y r) (y : Y) :
    rawCyclePushforwardUngraded e r c (e y) = (c : AlgebraicCycle Y ℤ) y := by
  classical
  have hinj : Function.Injective e.base := e.isOpenEmbedding.injective
  rw [rawCyclePushforwardUngraded_apply, Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply]
  simp only [Function.locallyFinsuppWithin.coe_zsmul, Pi.smul_apply, rawCyclePushforwardGenerator,
    Function.locallyFinsuppWithin.single_apply, smul_eq_mul, hinj.eq_iff,
    rawCyclePushforwardCoeff_eq_one_of_isIso p hp e, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with hy
  · rfl
  · exact (Function.notMem_support.mp fun h => hy (c.2.1.mem_toFinset.mpr h)).symm

/-- **Pushforward of principal divisors along an isomorphism.** Let `e : Y ⟶ X` be an isomorphism
of schemes satisfying `(*)`, with `X` of finite type over `k`. If the rational functions `f` on `X`
and `g` on `Y` correspond under the function field isomorphism, then the pushforward of the
principal divisor of `g` is the principal divisor of `f`. -/
theorem rawCyclePushforwardUngraded_principalDivisor_of_isIso (p : X ⟶ Spec (.of k))
    (hp : FiniteType p) [IsIntegral X] [IsIntegral Y] (hX : X.SatisfiesConditionStar)
    (hY : Y.SatisfiesConditionStar) (e : Y ⟶ X) [IsIso e] (f : X.functionFieldˣ)
    (g : Y.functionFieldˣ)
    (hfg : (functionFieldIsoOfIsOpenImmersion e).hom (f : X.functionField) = g) :
    rawCyclePushforwardUngraded e 1 (weilDivisorToCodimOneCycles hY (Y.principalDivisor hY g)) =
      (X.principalDivisor hX f).1 := by
  have := hX.isNoetherian
  have := hY.isNoetherian
  refine Function.locallyFinsuppWithin.ext fun x => ?_
  obtain ⟨y, rfl⟩ : ∃ y, e y = x := ⟨(inv e) x, by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩
  have h1 := Scheme.principalDivisor_apply hY g y
  have h2 := Scheme.principalDivisor_apply hX f (e y)
  rw [rawCyclePushforwardUngraded_apply_of_isIso p hp e, coe_weilDivisorToCodimOneCycles, h1, h2,
    ← hfg, ord_functionFieldIsoOfIsOpenImmersion_hom]

end Isomorphism

/-- On a scheme satisfying `(*)`, Weil divisors are exactly the codimension-one cycles. -/
theorem weilDivisorToCodimOneCycles_bijective {X : Scheme.{u}} (hX : X.SatisfiesConditionStar) :
    Function.Bijective (weilDivisorToCodimOneCycles hX) := by
  refine ⟨fun D E h => Subtype.ext ?_, fun c => ?_⟩
  · have := congrArg (fun c : codimensionCycles X 1 => (c : AlgebraicCycle X ℤ)) h
    simpa using this
  · refine ⟨⟨c.1, fun x hx => ?_⟩, Subtype.ext rfl⟩
    by_contra hcx
    have h := c.2.2 x hcx
    rw [codim_closure_singleton_eq_coheight] at h
    exact hx (by exact_mod_cast h)

/-- In an irreducible space, the whole space has codimension `0`. -/
theorem codim_univ_eq_zero {X : Type*} [TopologicalSpace X] [IrreducibleSpace X] :
    codim (Set.univ : Set X) = 0 := by
  let W : IrreducibleCloseds X := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  refine le_antisymm ?_ zero_le
  calc codim (Set.univ : Set X) ≤ coheight W :=
        iInf₂_le (f := fun (Z : IrreducibleCloseds X) (_ : (Z : Set X) ⊆ Set.univ) ↦
          coheight Z) W le_rfl
    _ = 0 := coheight_eq_zero.mpr fun Z _ => by
        change (Z : Set X) ⊆ Set.univ
        exact Set.subset_univ _

/-- A closed immersion into an integral scheme whose image has codimension `0` is an
isomorphism. -/
theorem isIso_of_isClosedImmersion_of_codim_eq_zero {X V : Scheme.{u}} [IsIntegral X]
    (i : V ⟶ X) [IsClosedImmersion i] (h : codim (Set.range i) = 0) : IsIso i := by
  have hsurj : Function.Surjective i.base := by
    by_contra hns
    have h1 : (1 : ℕ∞) ≤ codim (Set.range i) := by
      refine le_iInf₂ fun Z hZ => ?_
      rw [Order.one_le_iff_ne_zero]
      intro hZ0
      let W : IrreducibleCloseds X :=
        ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
      have hZW : Z = W := (coheight_eq_zero.mp hZ0).eq_of_le (by
        change (Z : Set X) ⊆ Set.univ
        exact Set.subset_univ _)
      apply hns
      intro x
      have hx : x ∈ (Z : Set X) := by
        rw [hZW]
        trivial
      exact hZ hx
    rw [h] at h1
    exact absurd h1 (by decide)
  have : Surjective i := ⟨hsurj⟩
  exact isIso_of_isClosedImmersion_of_surjective i

section Variety

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- A normal integral scheme, separated and of finite type over a field, satisfies Hartshorne's
condition `(*)`. -/
theorem satisfiesConditionStar_of_isNormal_of_finiteType (p : X ⟶ Spec (.of k)) [IsIntegral X]
    (hp : FiniteType p) [IsSeparated p] [IsNormal X] : X.SatisfiesConditionStar := by
  have := hp.1
  have := hp.2
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : IsNoetherian X := {}
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from p]; infer_instance⟩
  exact satisfiesConditionStar_of_isNormal

/-- **Codimension-one rational equivalence on a normal variety** (Hartshorne, Appendix A.1). Let
`X` be a normal variety (a normal integral scheme, separated and of finite type over a field `k`) of
dimension `n`. The rational-equivalence subgroup of the codimension-one cycles `Z^1(X)` is the
subgroup of principal Weil divisors, viewed as codimension-one cycles. -/
theorem rationalEquivalenceSubgroup_one_eq_map_principalDivisorSubgroup (p : X ⟶ Spec (.of k))
    [IsIntegral X] (hp : FiniteType p) [IsSeparated p] [IsNormal X] {n : ℕ}
    (hn : topologicalKrullDim X = n) :
    rationalEquivalenceSubgroup p hp hn 1 =
      (X.principalDivisorSubgroup (satisfiesConditionStar_of_isNormal_of_finiteType p hp)).map
        (weilDivisorToCodimOneCycles (satisfiesConditionStar_of_isNormal_of_finiteType p hp)) := by
  set hX := satisfiesConditionStar_of_isNormal_of_finiteType p hp
  apply le_antisymm
  · rw [rationalEquivalenceSubgroup, AddSubgroup.closure_le]
    rintro c ⟨V, hVi, i, hi, hV, D, D', hDD', rfl⟩
    set hY := satisfiesConditionStar_absoluteNormalization p hp i
    obtain ⟨g, hg⟩ := (Scheme.WeilDivisor.linearEquivalent_iff hY D D').1 hDD'
    have hcodim : codim (Set.range i) = 0 := by
      have h1 : codim (Set.range i) + 1 = 0 + 1 := by rw [hV]; rfl
      exact (ENat.add_left_injective_of_ne_top ENat.one_ne_top) h1
    have := isIso_of_isClosedImmersion_of_codim_eq_zero i hcodim
    have : IsNormal V := isNormal_of_isIso i
    have : IsIso (absoluteNormalizationMap V) := isIso_fromNormalization_of_isNormal V
    have : IsIso (subvarietyNormalizationMap i) := by
      unfold subvarietyNormalizationMap
      infer_instance
    let φ := functionFieldIsoOfIsOpenImmersion (subvarietyNormalizationMap i)
    let f : X.functionFieldˣ :=
      Units.map (φ.symm.commRingCatIsoToRingEquiv : _ →* X.functionField) g
    refine ⟨X.principalDivisor hX f, ⟨Additive.ofMul f, rfl⟩, ?_⟩
    rw [← map_sub, ← map_sub, hg]
    apply Subtype.ext
    rw [coe_subvarietyNormalizationPushforward, ← rawCyclePushforwardUngraded_apply,
      rawCyclePushforwardUngraded_principalDivisor_of_isIso p hp hX hY _ f g,
      coe_weilDivisorToCodimOneCycles]
    change φ.hom (φ.inv g) = g
    exact Iso.inv_hom_id_apply φ _
  · rintro c ⟨D, hD, rfl⟩
    change D ∈ (X.principalDivisorHom hX).range at hD
    obtain ⟨f, rfl⟩ := hD
    have hV : codim (Set.range (𝟙 X : X ⟶ X)) + 1 = ((1 : ℕ) : ℕ∞) := by
      have : Set.range (𝟙 X : X ⟶ X) = Set.univ :=
        Set.range_eq_univ.mpr fun x => ⟨x, rfl⟩
      rw [this, codim_univ_eq_zero]
      rfl
    set hY := satisfiesConditionStar_absoluteNormalization p hp (𝟙 X)
    have : IsIso (absoluteNormalizationMap X) := isIso_fromNormalization_of_isNormal X
    have : IsIso (subvarietyNormalizationMap (𝟙 X)) := by
      unfold subvarietyNormalizationMap
      infer_instance
    let φ := functionFieldIsoOfIsOpenImmersion (subvarietyNormalizationMap (𝟙 X))
    let g : (absoluteNormalization X).functionFieldˣ :=
      Units.map (φ.commRingCatIsoToRingEquiv : X.functionField →* _) f.toMul
    apply AddSubgroup.subset_closure
    refine ⟨X, inferInstance, 𝟙 X, inferInstance, hV, (absoluteNormalization X).principalDivisor hY g,
      0, (Scheme.WeilDivisor.linearEquivalent_iff _ _ _).2 ⟨g, sub_zero _⟩, ?_⟩
    rw [map_zero, map_zero, sub_zero]
    apply Subtype.ext
    rw [coe_subvarietyNormalizationPushforward, ← rawCyclePushforwardUngraded_apply,
      rawCyclePushforwardUngraded_principalDivisor_of_isIso p hp hX hY _ f.toMul g rfl,
      coe_weilDivisorToCodimOneCycles]
    rfl

/-- **Rational equivalence is linear equivalence in codimension one on a normal variety**
(Hartshorne, Appendix A.1). On a normal variety `X`, two Weil divisors are rationally equivalent as
codimension-one cycles if and only if they are linearly equivalent. -/
theorem rationallyEquivalent_weilDivisorToCodimOneCycles_iff (p : X ⟶ Spec (.of k))
    [IsIntegral X] (hp : FiniteType p) [IsSeparated p] [IsNormal X] {n : ℕ}
    (hn : topologicalKrullDim X = n) (D E : X.WeilDivisor) :
    RationallyEquivalent p hp hn
        (weilDivisorToCodimOneCycles (satisfiesConditionStar_of_isNormal_of_finiteType p hp) D)
        (weilDivisorToCodimOneCycles (satisfiesConditionStar_of_isNormal_of_finiteType p hp) E) ↔
      Scheme.WeilDivisor.LinearEquivalent (satisfiesConditionStar_of_isNormal_of_finiteType p hp)
        D E := by
  rw [RationallyEquivalent, ← map_sub,
    rationalEquivalenceSubgroup_one_eq_map_principalDivisorSubgroup p hp hn,
    AddSubgroup.mem_map_iff_mem (weilDivisorToCodimOneCycles_bijective _).1]
  rfl

/-- **The codimension-one Chow group of a normal variety is the Weil divisor class group**
(Hartshorne, Appendix A.1). On a normal variety `X`, the quotient of the codimension-one cycles
`Z^1(X)` by rational equivalence is isomorphic to the Weil divisor class group `Cl X`, the class of
a Weil divisor `D` corresponding to the class of `D` (`codimOneCycleClassEquivWeilClassGroup_mk`). -/
noncomputable def codimOneCycleClassEquivWeilClassGroup (p : X ⟶ Spec (.of k)) [IsIntegral X]
    (hp : FiniteType p) [IsSeparated p] [IsNormal X] {n : ℕ} (hn : topologicalKrullDim X = n) :
    codimensionCycles X 1 ⧸ rationalEquivalenceSubgroup p hp hn 1 ≃+
      X.WeilClassGroup (satisfiesConditionStar_of_isNormal_of_finiteType p hp) :=
  (QuotientAddGroup.congr _ _
    (AddEquiv.ofBijective _ (weilDivisorToCodimOneCycles_bijective
      (satisfiesConditionStar_of_isNormal_of_finiteType p hp)))
    (rationalEquivalenceSubgroup_one_eq_map_principalDivisorSubgroup p hp hn).symm).symm

/-- The isomorphism `Z^1(X) / Rat ≃ Cl X` sends the class of a Weil divisor, viewed as a
codimension-one cycle, to its divisor class. -/
theorem codimOneCycleClassEquivWeilClassGroup_mk (p : X ⟶ Spec (.of k)) [IsIntegral X]
    (hp : FiniteType p) [IsSeparated p] [IsNormal X] {n : ℕ} (hn : topologicalKrullDim X = n)
    (D : X.WeilDivisor) :
    codimOneCycleClassEquivWeilClassGroup p hp hn
        (weilDivisorToCodimOneCycles (satisfiesConditionStar_of_isNormal_of_finiteType p hp) D :
          codimensionCycles X 1 ⧸ rationalEquivalenceSubgroup p hp hn 1) =
      X.weilDivisorClassHom (satisfiesConditionStar_of_isNormal_of_finiteType p hp) D := by
  rw [codimOneCycleClassEquivWeilClassGroup, AddEquiv.symm_apply_eq]
  rfl

end Variety

end Hartshorne

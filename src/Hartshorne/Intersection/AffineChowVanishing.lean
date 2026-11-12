/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.AffineNormalizationSpec
import Hartshorne.Intersection.LinearNoetherNormalization
import Hartshorne.Intersection.MonicPrimeDivisorAlgebra
import Hartshorne.Intersection.ProjectiveLinearSubspaceCycle
import Hartshorne.Intersection.RationalEquivalenceLocalization

/-!
# Subvarieties in Noether position are rationally equivalent to zero

Let `X = Spec S[t]` be a variety over `k` and `Y = V(P)` an integral subvariety whose ideal
contains a monic polynomial in `t`, so that the projection forgetting `t` is finite on `Y`. Let
`P' = P ∩ S`, `R = S / P'`, and `B` the integral closure of `R` in its fraction field. Then
`C = V(P' S[t]) = Spec R[t]` contains `Y` as a prime divisor, the normalization of `C` is
`Spec B[t]` (`exists_isIso_absoluteNormalization_spec`), and for the minimal polynomial `g` of
the image of `t` in `K(Y)` over `B` the ideal `(g)` is prime with contraction `P`
(`exists_minpoly_span_isPrime_comap_eq`). Hence `div g` is the single prime divisor `(g)` with
multiplicity one, mapping onto `Y` with residue degree one, and `ν_* div g = [Y]`
(`pointCodimensionCycle_mem_rationalEquivalenceSubgroup_of_monic`).

For `k` infinite, a linear change of coordinates puts any integral subvariety of positive
codimension of `𝔸ⁿ⁺¹_k = Spec k[x₁, …, xₙ, t]` in this position
(`exists_optionShear_leadingCoeff_eq_C`), and rational equivalence is transported along
isomorphisms (`pointCodimensionCycle_mem_rationalEquivalenceSubgroup_of_isIso`). Hence every
cycle of positive codimension on a variety isomorphic to affine space is rationally equivalent to
zero (`mem_rationalEquivalenceSubgroup_of_isIso_spec_mvPolynomial`).
-/

namespace Hartshorne

open AlgebraicGeometry CategoryTheory Order Polynomial

universe u

/-- Arithmetic in `WithBot ℕ∞` for the codimension count. -/
private theorem add_one_eq_of_add_eq {a c : ℕ∞} {r n : ℕ} (h1 : (a : WithBot ℕ∞) + (r : ℕ∞) = n)
    (h2 : (a : WithBot ℕ∞) + 1 + (c : WithBot ℕ∞) = n) : c + 1 = r := by
  have h1' : a + r = n := by exact_mod_cast h1
  have h2' : a + 1 + c = n := by exact_mod_cast h2
  obtain ⟨a, rfl⟩ := ENat.ne_top_iff_exists.mp
    (ne_top_of_le_ne_top (ENat.natCast_ne_top n) (le_self_add.trans_eq h1'))
  obtain ⟨c, rfl⟩ := ENat.ne_top_iff_exists.mp
    (ne_top_of_le_ne_top (ENat.natCast_ne_top n) (le_add_self.trans_eq h2'))
  have e1 : a + r = n := by exact_mod_cast h1'
  have e2 : a + 1 + c = n := by exact_mod_cast h2'
  have : c + 1 = r := by omega
  exact_mod_cast this

/-- A point of `Spec O` given by a prime ideal. -/
private abbrev specPoint {O : Type u} [CommRing O] (I : Ideal O) [I.IsPrime] : Spec (.of O) :=
  ⟨I, inferInstance⟩

open scoped Classical in
/-- On `Spec R` for a Noetherian domain `R` satisfying `(*)`, a nonzero `g` generating a prime
ideal has principal divisor `[(g)]`: the point `(g)` has codimension one, `g` has order one
there and order zero at every other point. -/
theorem exists_ord_eq_ite_of_span_isPrime (R : CommRingCat.{u}) [IsDomain R] [IsNoetherianRing R]
    (hO : (Spec R).SatisfiesConditionStar) {g : R} (hg0 : g ≠ 0)
    (hgprime : (Ideal.span {g}).IsPrime) :
    ∃ gK : (Spec R).functionField, gK ≠ 0 ∧ coheight (α := Spec R) ⟨Ideal.span {g}, hgprime⟩ = 1 ∧
      ∀ x : Spec R, (Spec R).ord gK x = if x = ⟨Ideal.span {g}, hgprime⟩ then 1 else 0 := by
  let z : Spec R := ⟨Ideal.span {g}, hgprime⟩
  have hzh : z.asIdeal.height = 1 := by
    refine le_antisymm ?_ ?_
    · have : (Ideal.span {g}).IsPrincipal := ⟨g, rfl⟩
      exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {g}) _
        (by rw [Ideal.minimalPrimes_eq_subsingleton_self]; rfl)
    · rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
      change Ideal.span {g} ≠ ⊥
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact hg0
  have hcoh : coheight z = 1 := by
    rw [← idealHeight_eq_coheight]
    exact hzh
  -- the principal divisor of `g` on `Spec R` is `[z]`
  let gK : (Spec R).functionField := algebraMap R _ g
  have hgK : gK ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hg0)
  have hdiv : ∀ x : Spec R, (Spec R).ord gK x = if x = z then 1 else 0 := by
    intro x
    have : x.asIdeal.IsPrime := x.isPrime
    by_cases hx : coheight x = 1
    · by_cases hgx : g ∈ x.asIdeal
      · have hxz : x = z := by
          have hle : z.asIdeal ≤ x.asIdeal := (Ideal.span_singleton_le_iff_mem _).mpr hgx
          have hxh : x.asIdeal.height = 1 := by rw [idealHeight_eq_coheight]; exact hx
          by_contra hne
          have hlt : z.asIdeal < x.asIdeal := lt_of_le_of_ne hle fun h =>
            hne (PrimeSpectrum.ext h.symm)
          have := Ideal.height_strict_mono_of_isPrime_of_isPrime hlt
          rw [hzh, hxh] at this
          exact lt_irrefl _ this
        subst hxz
        rw [if_pos rfl]
        exact spec_ord_algebraMap_eq_one_of_span_eq hO hcoh rfl
      · rw [if_neg (by rintro rfl; exact hgx (Ideal.subset_span rfl))]
        exact (spec_ord_algebraMap_eq_zero_iff hO hx hg0).mpr hgx
    · rw [Scheme.ord_eq_zero_of_coheight_neq_one hx, if_neg (by rintro rfl; exact hx hcoh)]
  exact ⟨gK, hgK, hcoh, hdiv⟩

variable {k : Type u} [Field k] {S : Type u} [CommRing S] [IsDomain S] [IsNoetherianRing S]

/-- **Subvarieties in Noether position are rationally equivalent to zero.** Let
`X = Spec S[t]` be a variety over `k` of dimension `n`, and let `Y = closure {P}` be an integral
subvariety of codimension `r` whose ideal `P` contains a monic polynomial in `t`. Then `[Y]` is
rationally equivalent to zero: it is the pushforward of the principal divisor of the minimal
polynomial of `t` on the normalization of `π(Y) × 𝔸¹`. -/
theorem pointCodimensionCycle_mem_rationalEquivalenceSubgroup_of_monic
    (p : Spec (.of S[X]) ⟶ Spec (.of k)) (hp : FiniteType p) [IsSeparated p] {n : ℕ}
    (hn : topologicalKrullDim (Spec (.of S[X])) = n) (P : Spec (.of S[X])) {h : S[X]}
    (hmon : h.Monic) (hP : h ∈ P.asIdeal) {r : ℕ} (hr : codim (closure ({P} : Set _)) = r) :
    pointCodimensionCycle P hr ∈ rationalEquivalenceSubgroup p hp hn r := by
  classical
  let X := Spec (.of S[X])
  have : P.asIdeal.IsPrime := P.isPrime
  set P' := P.asIdeal.comap (C : S →+* S[X])
  let R := S ⧸ P'
  let B := integralClosure R (FractionRing R)
  let q : S[X] →+* R[X] := mapRingHom (Ideal.Quotient.mk P')
  let j : R[X] →+* B[X] := mapRingHom (algebraMap R B)
  obtain ⟨g, hg0, hgprime, hgcomap⟩ := exists_minpoly_span_isPrime_comap_eq P.asIdeal hmon hP
  have : IsDomain (CommRingCat.of R[X]) := inferInstanceAs (IsDomain R[X])
  have : IsDomain (CommRingCat.of B[X]) := inferInstanceAs (IsDomain B[X])
  let V := Spec (.of R[X])
  let i : V ⟶ X := Spec.map (CommRingCat.ofHom q)
  have : IsClosedImmersion i := IsClosedImmersion.spec_of_surjective _
    (Polynomial.map_surjective _ Ideal.Quotient.mk_surjective)
  -- the normalization of `V`
  have hbir : ∀ a : B[X], ∃ d₁ d₂ : R[X], d₂ ≠ 0 ∧ j d₂ * a = j d₁ := by
    intro a
    obtain ⟨b, hb, d, hd⟩ := exists_C_mul_eq_map_integralClosure a
    refine ⟨d, C b, Polynomial.C_ne_zero.mpr hb, ?_⟩
    change (C b).map (algebraMap R B) * a = d.map (algebraMap R B)
    rw [Polynomial.map_C]
    exact hd
  obtain ⟨e, he, heν⟩ := exists_isIso_absoluteNormalization_spec (D := R[X]) (O := B[X]) j
    injective_mapRingHom_integralClosure isIntegral_mapRingHom_integralClosure hbir
  let ν' := subvarietyNormalizationMap i
  have hfin : IsFinite ν' := isFinite_subvarietyNormalizationMap p hp i
  have hfinν := isFinite_absoluteNormalizationMap_of_isClosedImmersion p hp i
  have hp' := finiteType_subvarietyNormalizationMap_comp p hp i
  have hVs := satisfiesConditionStar_absoluteNormalization p hp i
  have := (absoluteNormalization_isNormal_and_isIntegral V).2
  -- `B[t]` is Noetherian and `Spec B[t]` satisfies `(*)`
  have hjfin : @RingHom.Finite R[X] B[X] _ _ j := by
    have h : IsFinite (Spec.map (CommRingCat.ofHom (R := R[X]) (S := B[X]) j)) := by
      rw [← heν]
      infer_instance
    exact (IsFinite.SpecMap_iff (CommRingCat.ofHom (R := R[X]) (S := B[X]) j)).mp h
  have : IsNoetherianRing B[X] := by
    let _ : Algebra R[X] B[X] := j.toAlgebra
    have : Module.Finite R[X] B[X] := hjfin
    exact isNoetherian_of_tower R[X] (isNoetherian_of_isNoetherianRing_of_finite R[X] B[X])
  have : IsNoetherianRing (CommRingCat.of B[X]) := inferInstanceAs (IsNoetherianRing B[X])
  have : IsIntegrallyClosed (CommRingCat.of B[X]) := inferInstanceAs (IsIntegrallyClosed B[X])
  have : IsNormal (Spec (.of B[X])) := isNormal_spec_of_isIntegrallyClosed (.of B[X])
  have hO : (Spec (.of B[X])).SatisfiesConditionStar := satisfiesConditionStar_of_isNormal
  have := hVs.isNoetherian
  have := hO.isNoetherian
  -- the point `z = (g)` of `Spec B[t]`, of height one, lying over `P`
  let jC := CommRingCat.ofHom (R := R[X]) (S := B[X]) j
  let z : Spec (.of B[X]) := ⟨Ideal.span {g}, hgprime⟩
  have hzP : i (Spec.map jC z) = P := by
    apply PrimeSpectrum.ext
    change Ideal.comap q (Ideal.comap j (Ideal.span {g})) = P.asIdeal
    rw [Ideal.comap_comap]
    exact hgcomap
  obtain ⟨gK, hgK, hcoh, hdiv⟩ := exists_ord_eq_ite_of_span_isPrime (CommRingCat.of B[X]) hO hg0
    hgprime
  -- transport to the normalization of `V`
  let φ := functionFieldIsoOfIsOpenImmersion e
  let G : (Spec (.of B[X])).functionFieldˣ := Units.mk0 gK hgK
  let f : (absoluteNormalization V).functionFieldˣ := Units.map φ.inv.hom.toMonoidHom G
  have hebij := ConcreteCategory.bijective_of_isIso e.base
  have hD : ∀ w, ((absoluteNormalization V).principalDivisor hVs f).1 w =
      if w = e z then 1 else 0 := by
    intro w
    obtain ⟨x, rfl⟩ := hebij.2 w
    have h1 := ord_functionFieldIsoOfIsOpenImmersion_hom e
      (f : (absoluteNormalization V).functionField) x
    have h2 : φ.hom (f : (absoluteNormalization V).functionField) = gK := by
      change φ.hom (φ.inv gK) = gK
      rw [← CommRingCat.comp_apply, Iso.inv_hom_id]
      rfl
    rw [h2, hdiv] at h1
    rw [Scheme.principalDivisor_apply, ← h1]
    by_cases hxz : x = z
    · rw [if_pos hxz, if_pos (by rw [hxz])]
    · rw [if_neg hxz, if_neg (fun h => hxz (hebij.1 h))]
  -- heights and residue degree at `e z`
  have hνez : ν' (e z) = P := by
    rw [← hzP]
    change (absoluteNormalizationMap V ≫ i) (e z) = _
    rw [← Scheme.Hom.comp_apply, ← Category.assoc, heν]
    rfl
  have hmin : ∀ w', w' ≤ e z → ν' w' = ν' (e z) → w' = e z := fun w' hw' hw'z =>
    (ν'.isDiscrete_preimage_singleton (ν' (e z))).eq_of_specializes
      (show e z ⤳ w' from hw') rfl hw'z |>.symm
  have hheight : height (e z) = height P := by
    rw [FlatEquidimensional.height_eq_height_of_forall (ν' ≫ p) p hp' hp ν' (e z) hmin, hνez]
  have happrox : ∀ a : B[X], ∃ d₁ d₂ : R[X], j d₂ ∉ z.asIdeal ∧ j d₂ * a - j d₁ ∈ z.asIdeal := by
    intro a
    obtain ⟨b, hb, d, hd⟩ := exists_C_mul_eq_map_integralClosure a
    refine ⟨d, C b, ?_, ?_⟩
    · intro hmem
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective b
      have hq : q (C s) = C (Ideal.Quotient.mk P' s) := Polynomial.map_C _
      have : C s ∈ P.asIdeal := by
        rw [← hgcomap]
        change j (q (C s)) ∈ Ideal.span {g}
        rw [hq]
        exact hmem
      exact hb (Ideal.Quotient.eq_zero_iff_mem.mpr this)
    · have h0 : (C b).map (algebraMap R B) * a - d.map (algebraMap R B) = 0 := by
        rw [Polynomial.map_C]
        exact sub_eq_zero.mpr hd
      change (C b).map (algebraMap R B) * a - d.map (algebraMap R B) ∈ _
      rw [h0]
      exact zero_mem _
  have hres : ν'.residueDegree (e z) = 1 := by
    have h1 := residueDegree_comp e ν' z
    rw [residueDegree_eq_one_of_isOpenImmersion e z, mul_one] at h1
    have h2 : e ≫ ν' = Spec.map jC ≫ i := by
      change e ≫ absoluteNormalizationMap V ≫ i = _
      rw [← Category.assoc, heν]
    rw [h2, residueDegree_comp, residueDegree_SpecMap_eq_one j z happrox, mul_one] at h1
    have h3 := rawCyclePushforwardCoeff_eq_one_of_isClosedImmersion i (Spec.map jC z)
    rw [rawCyclePushforwardCoeff_eq_ite] at h3
    split_ifs at h3 with h4
    · exact absurd h3 zero_ne_one
    · rw [← h1]
      exact_mod_cast h3
  have hcoeff : rawCyclePushforwardCoeff ν' (e z) = 1 := by
    rw [rawCyclePushforwardCoeff_eq_ite, if_neg (by rw [hνez, hheight]; exact lt_irrefl _), hres,
      Nat.cast_one]
  -- the codimension of `V`
  have hXd := dimension_codimension_formula p hp (closure {P}) isClosed_closure
    ⟨P, subset_closure rfl⟩
  rw [FlatEquidimensional.topologicalKrullDim_closure_singleton, hr, hn] at hXd
  have hVd := dimension_codimension_formula (ν' ≫ p) hp' (closure {e z}) isClosed_closure
    ⟨e z, subset_closure rfl⟩
  rw [FlatEquidimensional.topologicalKrullDim_closure_singleton,
    codim_closure_singleton_eq_coheight,
    coheight_eq_of_isOpenImmersion e, hcoh, hheight] at hVd
  have hsum := topologicalKrullDim_absoluteNormalization_add_codim p hp i
  rw [hn] at hsum
  change topologicalKrullDim (absoluteNormalization V) + _ = _ at hsum
  rw [← hVd] at hsum
  have hV : codim (Set.range i) + 1 = r := add_one_eq_of_add_eq hXd (by exact_mod_cast hsum)
  -- the generator `ν_* div f` is `[Y]`
  have hgen : subvarietyNormalizationPushforward p hp hn i hV
      (weilDivisorToCodimOneCycles hVs ((absoluteNormalization V).principalDivisor hVs f)) =
      pointCodimensionCycle P hr := by
    apply Subtype.ext
    refine Function.locallyFinsuppWithin.ext fun y => ?_
    rw [coe_subvarietyNormalizationPushforward, Function.locallyFinsuppWithin.coe_sum,
      Finset.sum_apply, pointCodimensionCycle_apply]
    have hmem : e z ∈ (weilDivisorToCodimOneCycles hVs
        ((absoluteNormalization V).principalDivisor hVs f)).2.1.toFinset := by
      rw [Set.Finite.mem_toFinset]
      change ((absoluteNormalization V).principalDivisor hVs f).1 (e z) ≠ 0
      rw [hD, if_pos rfl]
      exact one_ne_zero
    rw [Finset.sum_eq_single_of_mem (e z) hmem fun w _ hw => by
      simp only [Function.locallyFinsuppWithin.coe_zsmul, Pi.smul_apply]
      change ((absoluteNormalization V).principalDivisor hVs f).1 w • _ = 0
      rw [hD, if_neg hw, zero_smul]]
    simp only [Function.locallyFinsuppWithin.coe_zsmul, Pi.smul_apply]
    change ((absoluteNormalization V).principalDivisor hVs f).1 (e z) •
      rawCyclePushforwardGenerator ν' (e z) y = _
    rw [hD, if_pos rfl, one_smul, rawCyclePushforwardGenerator,
      Function.locallyFinsuppWithin.single_apply, hcoeff]
    change (if y = ν' (e z) then (1 : ℤ) else 0) = _
    rw [hνez]
  rw [rationalEquivalenceSubgroup_eq_closure_principalDivisor, ← hgen]
  exact AddSubgroup.subset_closure ⟨V, inferInstance, i, inferInstance, hV, f, rfl⟩

section Transport

variable {k : Type u} [Field k]

/-- Membership in rational equivalence depends only on the underlying cycle, not on the
codimension index it is regarded in. -/
theorem mem_rationalEquivalenceSubgroup_of_coe_eq {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    [IsIntegral X] (hp : FiniteType p) [IsSeparated p] {n : ℕ} (hn : topologicalKrullDim X = n)
    {a b : ℕ} (hab : a = b) {c : codimensionCycles X a} {d : codimensionCycles X b}
    (hcd : (c : AlgebraicCycle X ℤ) = d) (hc : c ∈ rationalEquivalenceSubgroup p hp hn a) :
    d ∈ rationalEquivalenceSubgroup p hp hn b := by
  subst hab
  rwa [← Subtype.ext hcd]

open scoped Classical in
/-- An additive subgroup of the codimension-`r` cycles containing the cycle of every
codimension-`r` point contains every codimension-`r` cycle. -/
theorem mem_of_forall_pointCodimensionCycle_mem {X : Scheme.{u}} {r : ℕ}
    (H : AddSubgroup (codimensionCycles X r))
    (hpt : ∀ (x : X) (hx : codim (closure ({x} : Set X)) = r), pointCodimensionCycle x hx ∈ H)
    (c : codimensionCycles X r) : c ∈ H := by
  have hc : c = ∑ x ∈ c.2.1.toFinset.attach, (c : AlgebraicCycle X ℤ) x.1 •
      pointCodimensionCycle x.1 (c.2.2 x.1 (c.2.1.mem_toFinset.mp x.2)) := by
    apply Subtype.ext
    refine Function.locallyFinsuppWithin.ext fun w => ?_
    rw [AddSubgroup.val_finsetSum, Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply]
    simp only [AddSubgroup.coe_zsmul, Function.locallyFinsuppWithin.coe_zsmul, Pi.smul_apply,
      pointCodimensionCycle_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_attach c.2.1.toFinset (fun x => if w = x then (c : AlgebraicCycle X ℤ) x else 0),
      Finset.sum_ite_eq]
    split_ifs with hw
    · rfl
    · exact Function.notMem_support.mp fun h => hw (c.2.1.mem_toFinset.mpr h)
  rw [hc]
  exact AddSubgroup.sum_mem _ fun x _ => AddSubgroup.zsmul_mem _ (hpt _ _) _

/-- A codimension-`r` cycle is rationally equivalent to zero when every codimension-`r` point
is. -/
theorem mem_rationalEquivalenceSubgroup_of_forall_point {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    [IsIntegral X] (hp : FiniteType p) [IsSeparated p] {n : ℕ} (hn : topologicalKrullDim X = n)
    {r : ℕ} (hpt : ∀ (x : X) (hx : codim (closure ({x} : Set X)) = r),
      pointCodimensionCycle x hx ∈ rationalEquivalenceSubgroup p hp hn r)
    (c : codimensionCycles X r) : c ∈ rationalEquivalenceSubgroup p hp hn r :=
  mem_of_forall_pointCodimensionCycle_mem _ hpt c

open scoped Classical in
/-- The pushforward of the cycle of a point along a closed immersion is the cycle of its
image. -/
theorem coe_rawCyclePushforward_pointCodimensionCycle {X Y : Scheme.{u}} (p : X ⟶ Spec (.of k))
    [IsIntegral X] [IsIntegral Y] (hp : FiniteType p) {n m : ℕ} (hn : topologicalKrullDim X = n)
    (hm : topologicalKrullDim Y = m) (e : Y ⟶ X) [IsClosedImmersion e] (y : Y) {r r' : ℕ}
    (hy : codim (closure ({y} : Set Y)) = r) (hey : codim (closure ({e y} : Set X)) = r') :
    (rawCyclePushforward (e ≫ p) p (finiteType_comp_of_isClosedImmersion p hp e) hp e rfl hm hn r
      (pointCodimensionCycle y hy) : AlgebraicCycle X ℤ) = pointCodimensionCycle (e y) hey := by
  refine Function.locallyFinsuppWithin.ext fun w => ?_
  change rawCyclePushforwardUngraded e r _ w = _
  rw [rawCyclePushforwardUngraded_apply_apply, pointCodimensionCycle_apply]
  have hmem : y ∈ (pointCodimensionCycle y hy).2.1.toFinset := by
    rw [Set.Finite.mem_toFinset]
    change (pointCodimensionCycle y hy : AlgebraicCycle Y ℤ) y ≠ 0
    rw [pointCodimensionCycle_apply, if_pos rfl]
    exact one_ne_zero
  rw [Finset.sum_eq_single_of_mem y hmem fun x _ hx => by
    rw [pointCodimensionCycle_apply, if_neg hx, zero_mul]]
  rw [pointCodimensionCycle_apply, if_pos rfl, one_mul,
    rawCyclePushforwardCoeff_eq_one_of_isClosedImmersion]

/-- **Transport along an isomorphism.** If `e : Y ⟶ X` is an isomorphism and the cycle of a point
`y` of `Y` is rationally equivalent to zero on `Y` (over `k` through `e`), then so is the cycle of
`e y` on `X`. -/
theorem pointCodimensionCycle_mem_rationalEquivalenceSubgroup_of_isIso {X Y : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsIntegral X] (hp : FiniteType p) [IsSeparated p] {n : ℕ}
    (hn : topologicalKrullDim X = n) [IsIntegral Y] (hm : topologicalKrullDim Y = n)
    (e : Y ⟶ X) [IsIso e] (y : Y) {r : ℕ} (hy : codim (closure ({y} : Set Y)) = r)
    (hey : codim (closure ({e y} : Set X)) = r)
    (h : pointCodimensionCycle y hy ∈ rationalEquivalenceSubgroup (e ≫ p)
      (finiteType_comp_of_isClosedImmersion p hp e) hm r) :
    pointCodimensionCycle (e y) hey ∈ rationalEquivalenceSubgroup p hp hn r := by
  have h1 := map_rationalEquivalenceSubgroup_le_of_isClosedImmersion p hp hn e hm r
    (AddSubgroup.mem_map_of_mem _ h)
  exact mem_rationalEquivalenceSubgroup_of_coe_eq p hp hn (Nat.add_sub_cancel r n)
    (coe_rawCyclePushforward_pointCodimensionCycle p hp hn hm e y hy _) h1

end Transport

section AffineSpace

variable {k : Type u} [Field k] {τ : Type} [Finite τ]

/-- **Cycles of positive codimension on affine space are rationally equivalent to zero.** Let
`k` be infinite and `X` a variety over `k` of dimension `n` isomorphic to affine space
`Spec k[x_i, t]`. Every codimension-`r` cycle on `X` with `r > 0` is rationally equivalent to
zero: after a linear change of coordinates, an integral subvariety of positive codimension lies
in Noether position. -/
theorem mem_rationalEquivalenceSubgroup_of_isIso_spec_mvPolynomial [Infinite k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsIntegral X] (hp : FiniteType p) [IsSeparated p] {n : ℕ}
    (hn : topologicalKrullDim X = n) (e : Spec (.of (MvPolynomial (Option τ) k)) ⟶ X) [IsIso e]
    {r : ℕ} (hr : 0 < r) (c : codimensionCycles X r) :
    c ∈ rationalEquivalenceSubgroup p hp hn r := by
  refine mem_rationalEquivalenceSubgroup_of_forall_point p hp hn (fun x hx => ?_) c
  let A := MvPolynomial (Option τ) k
  let S := MvPolynomial τ k
  have hehomeo := ConcreteCategory.bijective_of_isIso e.base
  obtain ⟨y, rfl⟩ := hehomeo.2 x
  -- the prime of `y` is nonzero
  have hy0 : y.asIdeal ≠ ⊥ := by
    intro hbot
    have hgen : y = genericPoint (Spec (.of A)) := by
      rw [genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext hbot
    have : codim (closure ({e y} : Set X)) = 0 := by
      rw [codim_closure_singleton_eq_coheight, coheight_eq_of_isOpenImmersion e, hgen,
        coheight_eq_zero]
      intro b hb
      exact (genericPoint_spec (Spec (.of A))).specializes trivial
    rw [hx] at this
    exact hr.ne' (by exact_mod_cast this)
  obtain ⟨f, hfy, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hy0
  obtain ⟨c₀, u, hu, hlead⟩ := exists_optionShear_leadingCoeff_eq_C hf0
  -- the coordinate change `A ≃ S[t]`
  let ψ : A ≃+* S[X] := ((optionShear c₀).trans (MvPolynomial.optionEquivLeft k τ)).toRingEquiv
  let E : Spec (.of S[X]) ⟶ Spec (.of A) := Spec.map ψ.toCommRingCatIso.hom
  have : IsIso E := inferInstance
  let P : Spec (.of S[X]) := (inv E) y
  have hEP : E P = y := by
    change (inv E ≫ E) y = y
    rw [IsIso.inv_hom_id]
    rfl
  have hPa : P.asIdeal = y.asIdeal.comap ψ.symm.toRingHom := by
    have h1 : (Spec.map ψ.toCommRingCatIso.hom) P = y := hEP
    rw [← h1]
    ext a
    change a ∈ P.asIdeal ↔ ψ (ψ.symm a) ∈ P.asIdeal
    rw [RingEquiv.apply_symm_apply]
  -- a monic polynomial in `P`
  have hψf : (ψ f).leadingCoeff = MvPolynomial.C u := hlead
  let hmonic := C (MvPolynomial.C u⁻¹) * ψ f
  have hmon : hmonic.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff_C_mul_of_isUnit, hψf, ← map_mul,
      inv_mul_cancel₀ hu, map_one]
    exact (isUnit_iff_ne_zero.mpr (inv_ne_zero hu)).map MvPolynomial.C
  have hmemP : hmonic ∈ P.asIdeal := by
    rw [hPa]
    refine Ideal.mul_mem_left _ _ ?_
    change ψ.symm (ψ f) ∈ y.asIdeal
    rw [RingEquiv.symm_apply_apply]
    exact hfy
  -- apply the Noether-position case on `Spec S[t]` and transport
  have hEe : IsIso (E ≫ e) := inferInstance
  have hdimS : topologicalKrullDim (Spec (.of S[X])) = n := by
    rw [← hn]
    exact IsHomeomorph.topologicalKrullDim_eq _
      (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso (asIso (E ≫ e)))).isHomeomorph
  have hPr : codim (closure ({P} : Set (Spec (.of S[X])))) = r := by
    rw [codim_closure_singleton_eq_coheight, ← coheight_eq_of_isOpenImmersion (E ≫ e),
      ← codim_closure_singleton_eq_coheight, Scheme.Hom.comp_apply, hEP]
    exact hx
  have hcore := pointCodimensionCycle_mem_rationalEquivalenceSubgroup_of_monic ((E ≫ e) ≫ p)
    (finiteType_comp_of_isClosedImmersion p hp (E ≫ e)) hdimS P hmon hmemP hPr
  have := pointCodimensionCycle_mem_rationalEquivalenceSubgroup_of_isIso p hp hn hdimS (E ≫ e) P
    hPr (by rw [Scheme.Hom.comp_apply, hEP]; exact hx) hcore
  convert this using 2
  rw [Scheme.Hom.comp_apply, hEP]

end AffineSpace

end Hartshorne

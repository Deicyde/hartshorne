/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.RationalEquivalencePrincipal
import Hartshorne.Intersection.ChowGroups
import Hartshorne.Intersection.RawCyclePushforwardFunctorial
import Hartshorne.Intersection.RationalEquivalenceCodimOne
import Hartshorne.Scheme.ReducedInducedSubscheme
import Hartshorne.Scheme.ImageReducedSource
import Hartshorne.Scheme.DimensionCodimension

/-!
# The localization sequence for rational equivalence

Fulton, *Intersection Theory*, Proposition 1.8, for the rational equivalence of Hartshorne,
Appendix A.1, defined through divisors on normalizations.

Let `X` be a variety over `k` of dimension `n`, `i : Y ⟶ X` the closed immersion of an integral
closed subvariety of dimension `m` (so of codimension `n - m`, `codim_range_eq_sub`), and `U` the
open complement of `Y`, assumed nonempty.

* `map_rationalEquivalenceSubgroup_le_of_isClosedImmersion`: the pushforward `i_*` of cycles
  (`[W] ↦ [W]`, the coefficients being `1`, `rawCyclePushforwardCoeff_eq_one_of_isClosedImmersion`)
  maps the rational-equivalence subgroup of `Y` into that of `X`: a generator `ν_* div g` attached
  to a subvariety `V` of `Y` is the generator attached to `V` as a subvariety of `X`.
* `map_rationalEquivalenceSubgroup_restrict_le`: the restriction `j^*` of cycles to `U`
  (`codimensionCyclesRestrict`, `[W] ↦ [W ∩ U]`) maps rational equivalence on `X` into rational
  equivalence on `U`: the normalization of `V ∩ U` is the preimage of `U` in the normalization of
  `V` (`exists_isOpenImmersion_absoluteNormalization`), so `j^* ν_* div g` is the generator
  attached to `V ∩ U` (`codimensionCyclesRestrict_subvarietyNormalizationPushforward`).
* Conversely every generator on `U` is the restriction of the generator attached to its closure
  in `X` with the reduced induced structure (`rationalEquivalenceSubgroup_le_map_restrict`), and a
  cycle on `X` restricting to zero on `U` is pushed forward from `Y`
  (`exists_rawCyclePushforward_eq_of_restrict_eq_zero`). Hence the sequence
  `A^r(Y) → A^(r + n - m)(X) → A^(r + n - m)(U) → 0` is exact (`chowGroup_localization_exact`,
  `chowGroupRestrict_surjective`), and `A^r(X) → A^r(U)` is injective for `r < n - m`
  (`chowGroupRestrict_injective_of_lt`).
-/

namespace Hartshorne

open AlgebraicGeometry CategoryTheory Order

universe u

variable {k : Type u} [Field k]

/-- Extract natural-number values from `a + b = m` in `WithBot ℕ∞`. -/
private theorem exists_nat_of_add_eq {a : WithBot ℕ∞} {b : ℕ∞} {m : ℕ}
    (h : a + (b : WithBot ℕ∞) = m) : ∃ d e : ℕ, a = d ∧ b = e ∧ d + e = m := by
  induction a using WithBot.recBotCoe with
  | bot => simp at h
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      have : ((⊤ : ℕ∞) : WithBot ℕ∞) + (b : WithBot ℕ∞) = ((⊤ : ℕ∞) : WithBot ℕ∞) := by
        rw [← WithBot.coe_add, top_add]
      rw [this] at h
      have h' : ((⊤ : ℕ∞) : WithBot ℕ∞) = ((m : ℕ∞) : WithBot ℕ∞) := h
      exact ENat.top_ne_natCast m (WithBot.coe_injective h')
    | coe d =>
      induction b using ENat.recTopCoe with
      | top =>
        exfalso
        have : ((d : ℕ∞) : WithBot ℕ∞) + ((⊤ : ℕ∞) : WithBot ℕ∞) = ((⊤ : ℕ∞) : WithBot ℕ∞) := by
          rw [← WithBot.coe_add, add_top]
        rw [this] at h
        have h' : ((⊤ : ℕ∞) : WithBot ℕ∞) = ((m : ℕ∞) : WithBot ℕ∞) := h
        exact ENat.top_ne_natCast m (WithBot.coe_injective h')
      | coe e =>
        refine ⟨d, e, rfl, rfl, ?_⟩
        exact_mod_cast h

/-- The raw pushforward of a cycle depends only on the underlying cycle, not on the
codimension index it is regarded in. -/
theorem coe_rawCyclePushforward_congr {X X' : Scheme.{u}} (p : X ⟶ Spec (.of k))
    (p' : X' ⟶ Spec (.of k)) [IsIntegral X] [IsIntegral X'] (hp : FiniteType p)
    (hp' : FiniteType p') (f : X ⟶ X') (hf : f ≫ p' = p) {n n' : ℕ}
    (hn : topologicalKrullDim X = n) (hn' : topologicalKrullDim X' = n') {r r' : ℕ}
    (c : codimensionCycles X r) (c' : codimensionCycles X r')
    (h : (c : AlgebraicCycle X ℤ) = c') :
    (rawCyclePushforward p p' hp hp' f hf hn hn' r c : AlgebraicCycle X' ℤ) =
      rawCyclePushforward p p' hp hp' f hf hn hn' r' c' := by
  rw [coe_rawCyclePushforward, coe_rawCyclePushforward]
  refine Finset.sum_congr ?_ fun x _ ↦ by rw [h]
  ext x
  simp only [Set.Finite.mem_toFinset]
  change x ∈ Function.support (c : X → ℤ) ↔ x ∈ Function.support (c' : X → ℤ)
  rw [show (c : X → ℤ) = (c' : X → ℤ) from congrArg DFunLike.coe h]

variable {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsIntegral X] (hp : FiniteType p)
  [IsSeparated p] {n : ℕ} (hn : topologicalKrullDim X = n)
  {Y : Scheme.{u}} [IsIntegral Y] (iY : Y ⟶ X) [IsClosedImmersion iY]

omit [IsIntegral X] [IsSeparated p] [IsIntegral Y] in
include hp in
theorem finiteType_comp_of_isClosedImmersion : FiniteType (iY ≫ p) := by
  have := hp.1
  have := hp.2
  exact ⟨inferInstance, inferInstance⟩

/-- **Closed-immersion pushforward preserves rational equivalence.** For a variety `X` over `k`
of dimension `n` and the closed immersion `i : Y ⟶ X` of an integral closed subvariety of
dimension `m`, the raw pushforward `i_*` maps the rational-equivalence subgroup of the
codimension-`r` cycles of `Y` into that of the codimension-`(r + n - m)` cycles of `X`. -/
theorem map_rationalEquivalenceSubgroup_le_of_isClosedImmersion {m : ℕ}
    (hm : topologicalKrullDim Y = m) (r : ℕ) :
    (rationalEquivalenceSubgroup (iY ≫ p) (finiteType_comp_of_isClosedImmersion p hp iY) hm
        r).map
      (rawCyclePushforward (iY ≫ p) p (finiteType_comp_of_isClosedImmersion p hp iY) hp iY rfl
        hm hn r) ≤
      rationalEquivalenceSubgroup p hp hn (r + n - m) := by
  have hpY := finiteType_comp_of_isClosedImmersion p hp iY
  rw [rationalEquivalenceSubgroup_eq_closure_principalDivisor, AddMonoidHom.map_closure,
    AddSubgroup.closure_le, rationalEquivalenceSubgroup_eq_closure_principalDivisor]
  rintro _ ⟨_, ⟨V, hVi, iV, hiV, hV, g, rfl⟩, rfl⟩
  -- codimension bookkeeping: `codim_X (V) = codim_Y (V) + n - m`
  have hY := topologicalKrullDim_absoluteNormalization_add_codim (iY ≫ p) hpY iV
  have hX := topologicalKrullDim_absoluteNormalization_add_codim p hp (iV ≫ iY)
  rw [hm] at hY
  rw [hn] at hX
  obtain ⟨d, e, hd, he, hde⟩ := exists_nat_of_add_eq hY
  obtain ⟨d', e', hd', he', hde'⟩ := exists_nat_of_add_eq hX
  rw [hd] at hd'
  have hdd : d = d' := by exact_mod_cast hd'
  have hr : e + 1 = r := by
    rw [he] at hV
    exact_mod_cast hV
  have hV' : codim (Set.range (iV ≫ iY)) + 1 = ((r + n - m : ℕ) : ℕ∞) := by
    rw [he']
    norm_cast
    omega
  refine AddSubgroup.subset_closure ⟨V, hVi, iV ≫ iY, inferInstance, hV', g, ?_⟩
  apply Subtype.ext
  set D := weilDivisorToCodimOneCycles (satisfiesConditionStar_absoluteNormalization (iY ≫ p) hpY iV)
    ((absoluteNormalization V).principalDivisor
      (satisfiesConditionStar_absoluteNormalization (iY ≫ p) hpY iV) g)
  -- `ν_*` on `Y` followed by `i_*` is `(ν ≫ i)_*`
  have hdimV := topologicalKrullDim_absoluteNormalization_eq (iY ≫ p) hpY hm iV hV
  rw [coe_rawCyclePushforward_congr (iY ≫ p) p hpY hp iY rfl hm hn
      (subvarietyNormalizationPushforward (iY ≫ p) hpY hm iV hV D)
      (rawCyclePushforward (subvarietyNormalizationMap iV ≫ iY ≫ p) (iY ≫ p)
        (finiteType_subvarietyNormalizationMap_comp (iY ≫ p) hpY iV) hpY
        (subvarietyNormalizationMap iV) rfl hdimV.1 hm 1 D) rfl,
    ← rawCyclePushforward_comp, coe_rawCyclePushforward, coe_subvarietyNormalizationPushforward]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  simp only [subvarietyNormalizationMap, Category.assoc]

section Restriction

variable {X : Scheme.{u}}

/-- The cycle with finitely supported coefficient function `c`. -/
private def cycleOfFiniteSupport {Z : Scheme.{u}} (c : Z → ℤ) (hc : (Function.support c).Finite) :
    AlgebraicCycle Z ℤ where
  toFun := c
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' := fun _ _ ↦ ⟨Set.univ, Filter.univ_mem, by simpa using hc⟩

/-- **Restriction of cycles to an open subscheme**, `j^* : Z^r(X) → Z^r(U)`,
`[W] ↦ [W ∩ U]` (zero when `W` misses `U`): the coefficient of a point of `U` is its coefficient
on `X`. Codimension is preserved since the generizations of a point of `U` lie in `U`. -/
noncomputable def codimensionCyclesRestrict (U : X.Opens) (r : ℕ) :
    codimensionCycles X r →+ codimensionCycles U r where
  toFun c := ⟨cycleOfFiniteSupport (fun x ↦ (c : AlgebraicCycle X ℤ) (U.ι x))
      (c.2.1.preimage U.ι.isOpenEmbedding.injective.injOn),
    c.2.1.preimage U.ι.isOpenEmbedding.injective.injOn, fun x hx ↦ by
      rw [codim_closure_singleton_eq_coheight, ← coheight_eq_of_isOpenImmersion U.ι,
        ← codim_closure_singleton_eq_coheight]
      exact c.2.2 _ hx⟩
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
lemma codimensionCyclesRestrict_apply (U : X.Opens) (r : ℕ) (c : codimensionCycles X r) (x : U) :
    (codimensionCyclesRestrict U r c : AlgebraicCycle U ℤ) x = (c : AlgebraicCycle X ℤ) (U.ι x) :=
  rfl

/-- Restriction of cycles to an open subscheme is surjective: extend by zero. -/
theorem codimensionCyclesRestrict_surjective (U : X.Opens) (r : ℕ) :
    Function.Surjective (codimensionCyclesRestrict U r) := by
  classical
  intro c
  let f : X → ℤ := fun x ↦ if h : x ∈ U then (c : AlgebraicCycle U ℤ) ⟨x, h⟩ else 0
  have hsupp : Function.support f ⊆ U.ι '' Function.support (c : AlgebraicCycle U ℤ) := by
    intro x hx
    by_cases h : x ∈ U
    · refine ⟨⟨x, h⟩, ?_, rfl⟩
      exact (by simpa [f, h] using hx : (c : AlgebraicCycle U ℤ) ⟨x, h⟩ ≠ 0)
    · simp [f, h] at hx
  have hfin : (Function.support f).Finite := (c.2.1.image _).subset hsupp
  refine ⟨⟨cycleOfFiniteSupport f hfin, hfin, fun x hx ↦ ?_⟩, ?_⟩
  · obtain ⟨y, hy, rfl⟩ := hsupp hx
    rw [codim_closure_singleton_eq_coheight, coheight_eq_of_isOpenImmersion U.ι,
      ← codim_closure_singleton_eq_coheight]
    exact c.2.2 y hy
  · refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
    change f (U.ι x) = _
    have hx : U.ι x ∈ U := x.2
    simp only [f, dif_pos hx]
    rfl

end Restriction

/-- **`j^* i_* = 0` on cycles.** If an open `U` misses the closed subvariety `Y`, the restriction
to `U` of a cycle pushed forward from `Y` vanishes. -/
theorem codimensionCyclesRestrict_rawCyclePushforward_eq_zero {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsIntegral X] (hp : FiniteType p) {n : ℕ}
    (hn : topologicalKrullDim X = n) {Y : Scheme.{u}} [IsIntegral Y] (iY : Y ⟶ X)
    [IsClosedImmersion iY] {m : ℕ} (hm : topologicalKrullDim Y = m) (U : X.Opens)
    (hU : ∀ y, iY y ∉ U) (r : ℕ) (c : codimensionCycles Y r) :
    codimensionCyclesRestrict U (r + n - m)
      (rawCyclePushforward (iY ≫ p) p (finiteType_comp_of_isClosedImmersion p hp iY) hp iY rfl
        hm hn r c) = 0 := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
  change rawCyclePushforwardUngraded iY r c (U.ι x) = 0
  by_contra hx
  obtain ⟨y, -, hy, -⟩ := exists_of_mem_support_rawCyclePushforwardUngraded iY c hx
  exact hU y (by rw [show iY y = U.ι x from hy]; exact x.2)

section OpenRestriction

/-- An open subscheme of a normal scheme is normal. -/
theorem isNormal_of_isOpenImmersion {X Y : Scheme.{u}} (e : Y ⟶ X) [IsOpenImmersion e]
    [IsNormal X] : IsNormal Y where
  isDomain_stalk y := (asIso (e.stalkMap y)).symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  isIntegrallyClosed_stalk y :=
    IsIntegrallyClosed.of_equiv (asIso (e.stalkMap y)).commRingCatIsoToRingEquiv

/-- The raw pushforward coefficients of an open immersion of schemes of finite type over `k` are
all `1`. -/
theorem rawCyclePushforwardCoeff_eq_one_of_isOpenImmersion {X Y : Scheme.{u}}
    (e : Y ⟶ X) [IsOpenImmersion e] (y : Y) : rawCyclePushforwardCoeff e y = 1 := by
  have hmono : StrictMono e.base := fun a b hab ↦ by
    refine lt_of_le_not_ge ?_ ?_
    · exact (show b ⤳ a from hab.le).map e.base.hom.continuous
    · intro hba
      exact hab.not_ge (e.isOpenEmbedding.isInducing.specializes_iff.mp hba)
  have h := height_le_height_apply_of_strictMono _ hmono y
  rw [rawCyclePushforwardCoeff_eq_ite, if_neg (not_lt.mpr h),
    residueDegree_eq_one_of_isOpenImmersion, Nat.cast_one]

/-- **Raw pushforward commutes with restriction to an open.** Let `f : Z ⟶ X` be a morphism of
schemes of finite type over `k`, `U ⊆ X` open, and `h : Z' ⟶ Z` an open immersion onto
`f⁻¹(U)`, with `f' : Z' ⟶ U` the induced morphism. If the cycle `c'` on `Z'` is the restriction of
`c` along `h`, then `f'_* c'` is the restriction of `f_* c` to `U`. -/
theorem rawCyclePushforwardUngraded_apply_ι {Z Z' X : Scheme.{u}} (pZ : Z ⟶ Spec (.of k))
    (pZ' : Z' ⟶ Spec (.of k)) (p : X ⟶ Spec (.of k)) (hpZ : FiniteType pZ)
    (hpZ' : FiniteType pZ') (hp : FiniteType p) (f : Z ⟶ X) (hf : f ≫ p = pZ) (U : X.Opens)
    (hpU : FiniteType (U.ι ≫ p)) (h : Z' ⟶ Z) [IsOpenImmersion h] (hh : h ≫ pZ = pZ')
    (hrange : Set.range h = f ⁻¹' U) (f' : Z' ⟶ U) (hf' : f' ≫ U.ι = h ≫ f) {r r' : ℕ}
    (c : codimensionCycles Z r) (c' : codimensionCycles Z' r')
    (hc : ∀ z, (c' : AlgebraicCycle Z' ℤ) z = (c : AlgebraicCycle Z ℤ) (h z)) (u : U.toScheme) :
    rawCyclePushforwardUngraded f r c (U.ι u) = rawCyclePushforwardUngraded f' r' c' u := by
  classical
  have hinj : Function.Injective h.base := h.isOpenEmbedding.injective
  have hfh : ∀ z, f (h z) = U.ι (f' z) := fun z ↦ by
    rw [← Scheme.Hom.comp_apply, ← hf', Scheme.Hom.comp_apply]
  have hcoeff : ∀ z, rawCyclePushforwardCoeff f (h z) = rawCyclePushforwardCoeff f' z := by
    intro z
    have h1 := rawCyclePushforwardCoeff_comp pZ' pZ p hpZ' hpZ hp h f hh hf z
    have h2 := rawCyclePushforwardCoeff_comp pZ' (U.ι ≫ p) p hpZ' hpU hp f' U.ι
      (by rw [← Category.assoc, hf', Category.assoc, hf, hh]) rfl z
    rw [rawCyclePushforwardCoeff_eq_one_of_isOpenImmersion h, mul_one] at h1
    rw [rawCyclePushforwardCoeff_eq_one_of_isOpenImmersion U.ι, one_mul] at h2
    rw [← h1, ← h2, hf']
  conv_rhs => rw [rawCyclePushforwardUngraded_apply_apply]
  rw [rawCyclePushforwardUngraded_apply_apply]
  rw [← Finset.sum_filter_of_ne (p := fun x ↦ x ∈ Set.range h.base)]
  · have hS : c.2.1.toFinset.filter (fun x ↦ x ∈ Set.range h.base) =
        c'.2.1.toFinset.image h.base := by
      ext x
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Function.mem_support,
        Finset.mem_image, Set.mem_range]
      constructor
      · rintro ⟨hx, z, rfl⟩
        exact ⟨z, by rwa [hc], rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨by rwa [← hc], z, rfl⟩
    rw [hS, Finset.sum_image fun a _ b _ hab ↦ hinj hab]
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    rw [hc, hfh, hcoeff]
    simp only [U.ι.isOpenEmbedding.injective.eq_iff]
  · intro x _ hx
    by_contra hxr
    apply hx
    rw [if_neg, mul_zero]
    intro hux
    apply hxr
    rw [hrange]
    change f x ∈ U
    rw [← hux]
    exact u.2

/-- The normalization of a nonempty open `W` of an integral scheme `V` is the preimage of `W` in
the normalization of `V`: there is an open immersion `W̃ ⟶ Ṽ` over `W ⟶ V` with image the
preimage of `W`. -/
theorem exists_isOpenImmersion_absoluteNormalization {V : Scheme.{u}} [IsIntegral V]
    (W : V.Opens) [Nonempty W] :
    ∃ h : absoluteNormalization W ⟶ absoluteNormalization V, IsOpenImmersion h ∧
      h ≫ absoluteNormalizationMap V = absoluteNormalizationMap W ≫ W.ι ∧
      Set.range h = absoluteNormalizationMap V ⁻¹' W := by
  let ν := absoluteNormalizationMap V
  let νW := absoluteNormalizationMap W
  have : IsIntegral (W : Scheme) := isIntegral_of_isOpenImmersion W.ι
  have hνdom := absoluteNormalizationMap_isDominant V
  have hνsurj : Function.Surjective ν := by
    have := surjective_of_isDominant_of_isClosed_range ν ν.isClosedMap.isClosed_range
    exact ν.surjective
  let Z1 := ν ⁻¹ᵁ W
  have : Nonempty Z1 := by
    obtain ⟨w⟩ := ‹Nonempty W›
    obtain ⟨z, hz⟩ := hνsurj w.1
    exact ⟨⟨z, by change ν z ∈ W; rw [hz]; exact w.2⟩⟩
  have : IsIntegral (Z1 : Scheme) := isIntegral_of_isOpenImmersion Z1.ι
  have : IsNormal (Z1 : Scheme) := isNormal_of_isOpenImmersion Z1.ι
  have hsurjW : Function.Surjective (ν ∣_ W) := by
    intro w
    obtain ⟨z, hz⟩ := hνsurj (W.ι w)
    have hzZ : z ∈ Z1 := by change ν z ∈ W; rw [hz]; exact w.2
    refine ⟨⟨z, hzZ⟩, W.ι.isOpenEmbedding.injective ?_⟩
    change ((ν ∣_ W) ≫ W.ι) ⟨z, hzZ⟩ = W.ι w
    rw [morphismRestrict_ι]
    exact hz
  have : IsDominant (ν ∣_ W) := ⟨hsurjW.denseRange⟩
  have : IsDominant W.ι := ⟨by
    change Dense (Set.range W.ι)
    rw [Scheme.Opens.range_ι]
    obtain ⟨w⟩ := ‹Nonempty W›
    exact W.isOpen.dense ⟨w.1, w.2⟩⟩
  have := absoluteNormalizationMap_isDominant (W : Scheme)
  have : IsDominant (νW ≫ W.ι) := inferInstance
  obtain ⟨φ, hφ, hφu⟩ := absoluteNormalization_existsUnique_lift (ν ∣_ W)
  obtain ⟨ψ0, hψ0, hψ0u⟩ := absoluteNormalization_existsUnique_lift (νW ≫ W.ι)
  have hψr : Set.range ψ0 ⊆ Set.range Z1.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change ν (ψ0 x) ∈ W
    rw [← Scheme.Hom.comp_apply, hψ0, Scheme.Hom.comp_apply]
    exact (νW x).2
  let ψ : absoluteNormalization W ⟶ Z1 := IsOpenImmersion.lift Z1.ι ψ0 hψr
  have hψ : ψ ≫ Z1.ι = ψ0 := IsOpenImmersion.lift_fac _ _ _
  have hψν : ψ ≫ (ν ∣_ W) = νW := by
    rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hψ, hψ0]
  -- uniqueness of lifts through `Ṽ ⟶ V` for maps out of `Z1`
  have : IsDominant (Z1.ι ≫ ν) := by
    rw [← morphismRestrict_ι]
    infer_instance
  obtain ⟨_, -, huniq⟩ := absoluteNormalization_existsUnique_lift (Z1.ι ≫ ν)
  have h1 : φ ≫ ψ = 𝟙 _ := by
    rw [← cancel_mono Z1.ι]
    have ha : (φ ≫ ψ ≫ Z1.ι) ≫ ν = Z1.ι ≫ ν := by
      rw [hψ, Category.assoc, hψ0, ← Category.assoc, hφ, morphismRestrict_ι]
    have hb : Z1.ι ≫ ν = Z1.ι ≫ ν := rfl
    rw [Category.assoc, Category.id_comp]
    exact (huniq _ ha).trans (huniq _ hb).symm
  obtain ⟨_, -, huniqW⟩ := absoluteNormalization_existsUnique_lift νW
  have h2 : ψ ≫ φ = 𝟙 _ := by
    have ha : (ψ ≫ φ) ≫ νW = νW := by rw [Category.assoc, hφ, hψν]
    exact (huniqW _ ha).trans (huniqW _ (Category.id_comp _)).symm
  have : IsIso ψ := ⟨⟨φ, h2, h1⟩⟩
  refine ⟨ψ0, ?_, hψ0, ?_⟩
  · rw [← hψ]
    infer_instance
  · rw [← hψ]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (ψ y).2
    · intro hx
      obtain ⟨y, hy⟩ := ψ.surjective ⟨x, hx⟩
      refine ⟨y, ?_⟩
      rw [Scheme.Hom.comp_apply, hy]
      rfl

/-- The range of a closed immersion of an irreducible scheme is the closure of the image of its
generic point. -/
theorem range_eq_closure_genericPoint {V X : Scheme.{u}} [IrreducibleSpace V] (i : V ⟶ X)
    [IsClosedImmersion i] : Set.range i = closure {i (genericPoint V)} := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    exact specializes_iff_mem_closure.mp
      (((genericPoint_spec V).specializes trivial).map i.base.hom.continuous)
  · exact closure_minimal (Set.singleton_subset_iff.mpr ⟨_, rfl⟩)
      i.isClosedEmbedding.isClosed_range

/-- The normalizations of isomorphic integral schemes are isomorphic over the isomorphism. -/
theorem exists_isIso_absoluteNormalization {V W : Scheme.{u}} [IsIntegral V] [IsIntegral W]
    (e : V ⟶ W) [IsIso e] :
    ∃ et : absoluteNormalization V ⟶ absoluteNormalization W, IsIso et ∧
      et ≫ absoluteNormalizationMap W = absoluteNormalizationMap V ≫ e := by
  have := absoluteNormalizationMap_isDominant V
  have := absoluteNormalizationMap_isDominant W
  have : IsDominant e := ⟨(ConcreteCategory.bijective_of_isIso e.base).2.denseRange⟩
  have : IsDominant (inv e) :=
    ⟨(ConcreteCategory.bijective_of_isIso (inv e).base).2.denseRange⟩
  obtain ⟨a, ha, -⟩ := absoluteNormalization_existsUnique_lift (absoluteNormalizationMap V ≫ e)
  obtain ⟨b, hb, -⟩ := absoluteNormalization_existsUnique_lift
    (absoluteNormalizationMap W ≫ inv e)
  obtain ⟨_, -, huV⟩ := absoluteNormalization_existsUnique_lift (absoluteNormalizationMap V)
  obtain ⟨_, -, huW⟩ := absoluteNormalization_existsUnique_lift (absoluteNormalizationMap W)
  have hab : a ≫ b = 𝟙 _ := by
    have h1 : (a ≫ b) ≫ absoluteNormalizationMap V = absoluteNormalizationMap V := by
      rw [Category.assoc, hb, ← Category.assoc, ha, Category.assoc, IsIso.hom_inv_id,
        Category.comp_id]
    exact (huV _ h1).trans (huV _ (Category.id_comp _)).symm
  have hba : b ≫ a = 𝟙 _ := by
    have h1 : (b ≫ a) ≫ absoluteNormalizationMap W = absoluteNormalizationMap W := by
      rw [Category.assoc, ha, ← Category.assoc, hb, Category.assoc, IsIso.inv_hom_id,
        Category.comp_id]
    exact (huW _ h1).trans (huW _ (Category.id_comp _)).symm
  exact ⟨a, ⟨⟨b, hab, hba⟩⟩, ha⟩

/-- **Generators of isomorphic subvarieties agree.** If `e : V ⟶ W` is an isomorphism of
integral closed subschemes of a variety `T` over `T` (`e ≫ iW = iV`), then every generator
attached to `V` is a generator attached to `W`. -/
theorem exists_subvarietyNormalizationPushforward_eq_of_isIso {T : Scheme.{u}}
    (pT : T ⟶ Spec (.of k)) [IsIntegral T] (hpT : FiniteType pT) [IsSeparated pT] {n : ℕ}
    (hnT : topologicalKrullDim T = n) {r : ℕ} {V W : Scheme.{u}} [IsIntegral V] [IsIntegral W]
    (iV : V ⟶ T) (iW : W ⟶ T) [IsClosedImmersion iV] [IsClosedImmersion iW] (e : V ⟶ W)
    [IsIso e] (he : e ≫ iW = iV) (hV : codim (Set.range iV) + 1 = r)
    (hW : codim (Set.range iW) + 1 = r) (g : (absoluteNormalization V).functionFieldˣ) :
    ∃ g' : (absoluteNormalization W).functionFieldˣ,
      subvarietyNormalizationPushforward pT hpT hnT iV hV
          (weilDivisorToCodimOneCycles (satisfiesConditionStar_absoluteNormalization pT hpT iV)
            ((absoluteNormalization V).principalDivisor
              (satisfiesConditionStar_absoluteNormalization pT hpT iV) g)) =
        subvarietyNormalizationPushforward pT hpT hnT iW hW
          (weilDivisorToCodimOneCycles (satisfiesConditionStar_absoluteNormalization pT hpT iW)
            ((absoluteNormalization W).principalDivisor
              (satisfiesConditionStar_absoluteNormalization pT hpT iW) g')) := by
  obtain ⟨et, het, hetν⟩ := exists_isIso_absoluteNormalization e
  let φ := functionFieldIsoOfIsOpenImmersion et
  refine ⟨Units.map φ.inv.hom.toMonoidHom g, ?_⟩
  set hVs := satisfiesConditionStar_absoluteNormalization pT hpT iV
  set hWs := satisfiesConditionStar_absoluteNormalization pT hpT iW
  set D := weilDivisorToCodimOneCycles hVs ((absoluteNormalization V).principalDivisor hVs g)
  set D' := weilDivisorToCodimOneCycles hWs ((absoluteNormalization W).principalDivisor hWs
    (Units.map φ.inv.hom.toMonoidHom g))
  have hmap : subvarietyNormalizationMap iV = et ≫ subvarietyNormalizationMap iW := by
    simp only [subvarietyNormalizationMap]
    rw [← Category.assoc, hetν, Category.assoc, he]
  have hpW := finiteType_subvarietyNormalizationMap_comp pT hpT iW
  have hpV : FiniteType (et ≫ subvarietyNormalizationMap iW ≫ pT) := by
    rw [← Category.assoc, ← hmap]
    exact finiteType_subvarietyNormalizationMap_comp pT hpT iV
  have hdV := topologicalKrullDim_absoluteNormalization_eq pT hpT hnT iV hV
  have hdW := topologicalKrullDim_absoluteNormalization_eq pT hpT hnT iW hW
  have hiso : (rawCyclePushforward (et ≫ subvarietyNormalizationMap iW ≫ pT)
      (subvarietyNormalizationMap iW ≫ pT) hpV hpW et rfl hdV.1 hdW.1 1 D :
        AlgebraicCycle (absoluteNormalization W) ℤ) =
        (D' : AlgebraicCycle (absoluteNormalization W) ℤ) := by
    change rawCyclePushforwardUngraded et 1 D = _
    rw [rawCyclePushforwardUngraded_principalDivisor_of_isIso (subvarietyNormalizationMap iW ≫ pT)
      hpW hWs hVs et (Units.map φ.inv.hom.toMonoidHom g) g (by
        change φ.hom (φ.inv (g : (absoluteNormalization V).functionField)) = g
        rw [← CommRingCat.comp_apply, Iso.inv_hom_id]
        rfl)]
    rfl
  apply Subtype.ext
  rw [coe_subvarietyNormalizationPushforward, coe_subvarietyNormalizationPushforward]
  have h1 := rawCyclePushforward_comp (et ≫ subvarietyNormalizationMap iW ≫ pT)
    (subvarietyNormalizationMap iW ≫ pT) pT hpV hpW hpT et (subvarietyNormalizationMap iW) rfl rfl
    hdV.1 hdW.1 hnT 1 D
  rw [coe_rawCyclePushforward, coe_rawCyclePushforward_congr (subvarietyNormalizationMap iW ≫ pT)
    pT hpW hpT (subvarietyNormalizationMap iW) rfl hdW.1 hnT _ D' hiso,
    coe_rawCyclePushforward] at h1
  rw [← h1]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [hmap]

section OpenVariety

/-- A closed subvariety `V` meeting the open `U` has the same codimension as `V ∩ U` in `U`. -/
theorem codim_range_morphismRestrict {X V : Scheme.{u}} [IsIntegral V] (iV : V ⟶ X)
    [IsClosedImmersion iV] (U : X.Opens) [IsIntegral (iV ⁻¹ᵁ U : Scheme)] :
    codim (Set.range (iV ∣_ U)) = codim (Set.range iV) := by
  have hgen : U.ι ((iV ∣_ U) (genericPoint (iV ⁻¹ᵁ U))) = iV (genericPoint V) := by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply,
      genericPoint_eq_of_isOpenImmersion]
  rw [range_eq_closure_genericPoint (iV ∣_ U), range_eq_closure_genericPoint iV,
    codim_closure_singleton_eq_coheight, codim_closure_singleton_eq_coheight, ← hgen,
    coheight_eq_of_isOpenImmersion U.ι]

/-- **Restriction of a generator.** The restriction to `U` of the generator `ν_* div g` attached
to a subvariety `V` meeting `U` is the generator attached to `V ∩ U` and the rational function
corresponding to `g`, the normalization of `V ∩ U` being an open of that of `V` (`h`). -/
theorem codimensionCyclesRestrict_subvarietyNormalizationPushforward {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsIntegral X] (hp : FiniteType p) [IsSeparated p] {n : ℕ}
    (hn : topologicalKrullDim X = n) (U : X.Opens) [IsIntegral (U : Scheme)]
    (hnU : topologicalKrullDim U = n) {r : ℕ} {V : Scheme.{u}} [IsIntegral V] (iV : V ⟶ X)
    [IsClosedImmersion iV] (hV : codim (Set.range iV) + 1 = r)
    [IsIntegral (iV ⁻¹ᵁ U : Scheme)]
    (h : absoluteNormalization (iV ⁻¹ᵁ U) ⟶ absoluteNormalization V) [IsOpenImmersion h]
    (hhν : h ≫ absoluteNormalizationMap V =
      absoluteNormalizationMap (iV ⁻¹ᵁ U) ≫ (iV ⁻¹ᵁ U).ι)
    (hhr : Set.range h = absoluteNormalizationMap V ⁻¹' (iV ⁻¹ᵁ U))
    (hcodim : codim (Set.range (iV ∣_ U)) + 1 = r)
    (g : (absoluteNormalization V).functionFieldˣ) :
    codimensionCyclesRestrict U r (subvarietyNormalizationPushforward p hp hn iV hV
      (weilDivisorToCodimOneCycles (satisfiesConditionStar_absoluteNormalization p hp iV)
        ((absoluteNormalization V).principalDivisor
          (satisfiesConditionStar_absoluteNormalization p hp iV) g))) =
    subvarietyNormalizationPushforward (U.ι ≫ p) (finiteType_opens_ι_comp p hp U) hnU (iV ∣_ U)
      hcodim (weilDivisorToCodimOneCycles
        (satisfiesConditionStar_absoluteNormalization (U.ι ≫ p) (finiteType_opens_ι_comp p hp U)
          (iV ∣_ U))
        ((absoluteNormalization (iV ⁻¹ᵁ U)).principalDivisor
          (satisfiesConditionStar_absoluteNormalization (U.ι ≫ p)
            (finiteType_opens_ι_comp p hp U) (iV ∣_ U))
          (Units.map (functionFieldIsoOfIsOpenImmersion h).hom.hom.toMonoidHom g))) := by
  have hpU := finiteType_opens_ι_comp p hp U
  set hVs := satisfiesConditionStar_absoluteNormalization p hp iV
  set D := weilDivisorToCodimOneCycles hVs ((absoluteNormalization V).principalDivisor hVs g)
  set hWs := satisfiesConditionStar_absoluteNormalization (U.ι ≫ p) hpU (iV ∣_ U)
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun u ↦ ?_)
  have hf' : subvarietyNormalizationMap (iV ∣_ U) ≫ U.ι = h ≫ subvarietyNormalizationMap iV := by
    simp only [subvarietyNormalizationMap, Category.assoc]
    rw [morphismRestrict_ι, ← Category.assoc, ← hhν, Category.assoc]
  change rawCyclePushforwardUngraded (subvarietyNormalizationMap iV) 1 D (U.ι u) =
    rawCyclePushforwardUngraded (subvarietyNormalizationMap (iV ∣_ U)) 1
      (weilDivisorToCodimOneCycles hWs ((absoluteNormalization (iV ⁻¹ᵁ U)).principalDivisor hWs
        (Units.map (functionFieldIsoOfIsOpenImmersion h).hom.hom.toMonoidHom g))) u
  refine rawCyclePushforwardUngraded_apply_ι (subvarietyNormalizationMap iV ≫ p)
    (subvarietyNormalizationMap (iV ∣_ U) ≫ U.ι ≫ p) p
    (finiteType_subvarietyNormalizationMap_comp p hp iV)
    (finiteType_subvarietyNormalizationMap_comp (U.ι ≫ p) hpU (iV ∣_ U)) hp
    (subvarietyNormalizationMap iV) rfl U hpU h
    (by rw [← Category.assoc, ← hf', Category.assoc]) ?_ (subvarietyNormalizationMap (iV ∣_ U))
    hf' D _ ?_ u
  · rw [hhr]
    rfl
  · intro z
    have := hVs.isNoetherian
    have := hWs.isNoetherian
    rw [coe_weilDivisorToCodimOneCycles, coe_weilDivisorToCodimOneCycles,
      Scheme.principalDivisor_apply, Scheme.principalDivisor_apply]
    exact ord_functionFieldIsoOfIsOpenImmersion_hom h (g : _) z

/-- **Restriction to an open preserves rational equivalence.** For a variety `X` over `k` of
dimension `n` and a nonempty open `U`, the restriction of cycles `j^* : Z^r(X) → Z^r(U)` maps the
rational-equivalence subgroup of `X` into that of `U`. A generator `ν_* div g` attached to a
subvariety `V` missing `U` restricts to `0`; otherwise it restricts to the generator attached to
`V ∩ U`, whose normalization is the preimage of `U` in that of `V`. -/
theorem map_rationalEquivalenceSubgroup_restrict_le {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    [IsIntegral X] (hp : FiniteType p) [IsSeparated p] {n : ℕ} (hn : topologicalKrullDim X = n)
    (U : X.Opens) [IsIntegral (U : Scheme)] (hnU : topologicalKrullDim U = n) (r : ℕ) :
    (rationalEquivalenceSubgroup p hp hn r).map (codimensionCyclesRestrict U r) ≤
      rationalEquivalenceSubgroup (U.ι ≫ p) (finiteType_opens_ι_comp p hp U) hnU r := by
  rw [rationalEquivalenceSubgroup_eq_closure_principalDivisor, AddMonoidHom.map_closure,
    AddSubgroup.closure_le, rationalEquivalenceSubgroup_eq_closure_principalDivisor]
  rintro _ ⟨_, ⟨V, hVi, iV, hiV, hV, g, rfl⟩, rfl⟩
  by_cases hmeet : ∃ v, iV v ∈ U
  swap
  · simp only [not_exists] at hmeet
    rw [show codimensionCyclesRestrict U r _ = 0 from ?_]
    · exact zero_mem _
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
    change rawCyclePushforwardUngraded (subvarietyNormalizationMap iV) 1 _ (U.ι x) = 0
    by_contra hx
    obtain ⟨y, -, hy, -⟩ := exists_of_mem_support_rawCyclePushforwardUngraded _ _ hx
    apply hmeet (absoluteNormalizationMap V y)
    have : iV (absoluteNormalizationMap V y) = U.ι x := hy
    rw [this]
    exact x.2
  obtain ⟨v, hv⟩ := hmeet
  have : Nonempty (iV ⁻¹ᵁ U) := ⟨⟨v, hv⟩⟩
  have : IsIntegral (iV ⁻¹ᵁ U : Scheme) := isIntegral_of_isOpenImmersion (iV ⁻¹ᵁ U).ι
  obtain ⟨h, hho, hhν, hhr⟩ := exists_isOpenImmersion_absoluteNormalization (iV ⁻¹ᵁ U)
  have hcodim : codim (Set.range (iV ∣_ U)) + 1 = r := by
    rw [codim_range_morphismRestrict, hV]
  rw [codimensionCyclesRestrict_subvarietyNormalizationPushforward p hp hn U hnU iV hV h hhν
    hhr hcodim]
  exact AddSubgroup.subset_closure ⟨_, inferInstance, iV ∣_ U, inferInstance, hcodim, _, rfl⟩

/-- **Generators on `U` lift.** Every generator of rational equivalence on a nonempty open `U` of
a variety `X` is the restriction of a generator on `X`, attached to the closure in `X` (with its
reduced induced structure) of the subvariety of `U`. -/
theorem rationalEquivalenceSubgroup_le_map_restrict {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    [IsIntegral X] (hp : FiniteType p) [IsSeparated p] {n : ℕ} (hn : topologicalKrullDim X = n)
    (U : X.Opens) [IsIntegral (U : Scheme)] (hnU : topologicalKrullDim U = n) (r : ℕ) :
    rationalEquivalenceSubgroup (U.ι ≫ p) (finiteType_opens_ι_comp p hp U) hnU r ≤
      (rationalEquivalenceSubgroup p hp hn r).map (codimensionCyclesRestrict U r) := by
  have hpU := finiteType_opens_ι_comp p hp U
  rw [rationalEquivalenceSubgroup_eq_closure_principalDivisor (U.ι ≫ p), AddSubgroup.closure_le]
  rintro _ ⟨V', hV'i, iV', hiV', hV', g, rfl⟩
  set y0 : (U : Scheme) := iV' (genericPoint V')
  set x0 : X := U.ι y0
  let Z : TopologicalSpace.Closeds X := ⟨closure {x0}, isClosed_closure⟩
  let iV := reducedInducedSubschemeι Z
  have hrange : Set.range iV = closure {x0} := range_reducedInducedSubschemeι Z
  have : IrreducibleSpace (reducedInducedSubscheme Z) := by
    have hirr : IsIrreducible (Set.range iV) := hrange ▸ isIrreducible_singleton.closure
    have := Subtype.irreducibleSpace hirr
    exact (Homeomorph.irreducibleSpace_iff iV.isClosedEmbedding.isEmbedding.toHomeomorph).mpr this
  have : IsIntegral (reducedInducedSubscheme Z) :=
    isIntegral_of_irreducibleSpace_of_isReduced _
  have hV : codim (Set.range iV) + 1 = r := by
    rw [hrange, codim_closure_singleton_eq_coheight, coheight_eq_of_isOpenImmersion U.ι,
      ← codim_closure_singleton_eq_coheight, ← range_eq_closure_genericPoint iV', hV']
  obtain ⟨v0, hv0⟩ : x0 ∈ Set.range iV := hrange ▸ subset_closure rfl
  have : Nonempty (iV ⁻¹ᵁ U) := ⟨⟨v0, by change iV v0 ∈ U; rw [hv0]; exact y0.2⟩⟩
  have : IsIntegral (iV ⁻¹ᵁ U : Scheme) := isIntegral_of_isOpenImmersion (iV ⁻¹ᵁ U).ι
  have hrW : Set.range (iV ∣_ U) = Set.range iV' := by
    rw [range_eq_closure_genericPoint iV']
    ext u
    rw [U.ι.isOpenEmbedding.isEmbedding.closure_eq_preimage_closure_image, Set.image_singleton]
    constructor
    · rintro ⟨w, rfl⟩
      change U.ι ((iV ∣_ U) w) ∈ closure {x0}
      rw [← hrange, ← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
      exact ⟨_, rfl⟩
    · intro hu
      change U.ι u ∈ closure {x0} at hu
      rw [← hrange] at hu
      obtain ⟨v, hv⟩ := hu
      have hvW : v ∈ iV ⁻¹ᵁ U := by change iV v ∈ U; rw [hv]; exact u.2
      refine ⟨⟨v, hvW⟩, U.ι.isOpenEmbedding.injective ?_⟩
      change ((iV ∣_ U) ≫ U.ι) ⟨v, hvW⟩ = U.ι u
      rw [morphismRestrict_ι]
      exact hv
  have hker : (iV ∣_ U).ker = iV'.ker := by
    simp only [ker_eq_vanishingIdeal_closure_range, hrW]
  let a : V' ⟶ (iV ⁻¹ᵁ U : Scheme) := IsClosedImmersion.lift (iV ∣_ U) iV' hker.le
  let b : (iV ⁻¹ᵁ U : Scheme) ⟶ V' := IsClosedImmersion.lift iV' (iV ∣_ U) hker.ge
  have ha : a ≫ (iV ∣_ U) = iV' := IsClosedImmersion.lift_fac _ _ _
  have hb : b ≫ iV' = iV ∣_ U := IsClosedImmersion.lift_fac _ _ _
  have : IsIso a := ⟨⟨b, by rw [← cancel_mono iV', Category.assoc, hb, ha, Category.id_comp],
    by rw [← cancel_mono (iV ∣_ U), Category.assoc, ha, hb, Category.id_comp]⟩⟩
  have hcodim : codim (Set.range (iV ∣_ U)) + 1 = r := by rw [hrW, hV']
  obtain ⟨g1, hg1⟩ := exists_subvarietyNormalizationPushforward_eq_of_isIso (U.ι ≫ p) hpU hnU
    iV' (iV ∣_ U) a ha hV' hcodim g
  obtain ⟨h, hho, hhν, hhr⟩ := exists_isOpenImmersion_absoluteNormalization (iV ⁻¹ᵁ U)
  let φ := functionFieldIsoOfIsOpenImmersion h
  rw [rationalEquivalenceSubgroup_eq_closure_principalDivisor p]
  refine ⟨_, AddSubgroup.subset_closure ⟨_, inferInstance, iV, inferInstance, hV,
    Units.map φ.inv.hom.toMonoidHom g1, rfl⟩, ?_⟩
  have hφ : Units.map φ.hom.hom.toMonoidHom (Units.map φ.inv.hom.toMonoidHom g1) = g1 := by
    apply Units.ext
    change φ.hom (φ.inv (g1 : (absoluteNormalization (iV ⁻¹ᵁ U)).functionField)) = g1
    rw [← CommRingCat.comp_apply, Iso.inv_hom_id]
    rfl
  rw [codimensionCyclesRestrict_subvarietyNormalizationPushforward p hp hn U hnU iV hV h hhν
    hhr hcodim, hg1]
  simp only [φ] at hφ
  rw [hφ]

end OpenVariety

end OpenRestriction

section SupportedOnClosed

/-- The raw pushforward coefficients of a closed immersion are all `1`. -/
theorem rawCyclePushforwardCoeff_eq_one_of_isClosedImmersion {X Y : Scheme.{u}}
    (e : Y ⟶ X) [IsClosedImmersion e] (y : Y) : rawCyclePushforwardCoeff e y = 1 := by
  have hmono : StrictMono e.base := fun a b hab ↦ by
    refine lt_of_le_not_ge ?_ ?_
    · exact (show b ⤳ a from hab.le).map e.base.hom.continuous
    · intro hba
      exact hab.not_ge (e.isClosedEmbedding.isInducing.specializes_iff.mp hba)
  have h := height_le_height_apply_of_strictMono _ hmono y
  rw [rawCyclePushforwardCoeff_eq_ite, if_neg (not_lt.mpr h)]
  have hsurj : Function.Surjective (e.residueFieldMap y) := by
    intro z
    obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective z
    obtain ⟨t, rfl⟩ := e.stalkMap_surjective y s
    exact ⟨X.residue (e y) t, ConcreteCategory.congr_hom (Scheme.residue_residueFieldMap e y) t⟩
  let _ := (e.residueFieldMap y).hom.toAlgebra
  rw [Scheme.Hom.residueDegree,
    Module.finrank_of_bijective_algebraMap ⟨(e.residueFieldMap y).hom.injective, hsurj⟩,
    Nat.cast_one]

omit [IsSeparated p] in
include hp hn in
/-- For a closed subvariety `Y` of dimension `m` of a variety `X` of dimension `n`, the
codimension in `X` of the closure of a point of `Y` is its codimension in `Y` plus `n - m`. -/
theorem codim_closure_apply_eq {m : ℕ} (hm : topologicalKrullDim Y = m) (y : Y) :
    ∃ e : ℕ, codim (closure ({y} : Set Y)) = e ∧
      codim (closure ({iY y} : Set X)) = ((e + (n - m) : ℕ) : ℕ∞) ∧ m ≤ n := by
  have hpY := finiteType_comp_of_isClosedImmersion p hp iY
  have hY := dimension_codimension_formula (iY ≫ p) hpY (closure {y}) isClosed_closure
    ⟨y, subset_closure rfl⟩
  have hX := dimension_codimension_formula p hp (closure {iY y}) isClosed_closure
    ⟨iY y, subset_closure rfl⟩
  rw [FlatEquidimensional.topologicalKrullDim_closure_singleton, hm] at hY
  rw [FlatEquidimensional.topologicalKrullDim_closure_singleton, hn] at hX
  have hmono : StrictMono iY.base := fun a b hab ↦ by
    refine lt_of_le_not_ge ?_ ?_
    · exact (show b ⤳ a from hab.le).map iY.base.hom.continuous
    · intro hba
      exact hab.not_ge (iY.isClosedEmbedding.isInducing.specializes_iff.mp hba)
  have hh : height (iY y) = height y :=
    le_antisymm (height_apply_le (iY ≫ p) p hpY hp iY rfl y)
      (height_le_height_apply_of_strictMono _ hmono y)
  rw [hh] at hX
  obtain ⟨d, e, hd, he, hde⟩ := exists_nat_of_add_eq hY
  obtain ⟨d', e', hd', he', hde'⟩ := exists_nat_of_add_eq hX
  have hdd : d = d' := by rw [hd] at hd'; exact_mod_cast hd'
  have hmn : m ≤ n := by
    have h := iY.isClosedEmbedding.isInducing.topologicalKrullDim_le
    rw [hm, hn] at h
    exact_mod_cast h
  refine ⟨e, he, ?_, hmn⟩
  rw [he']
  norm_cast
  omega

omit [IsSeparated p] in
/-- **Cycles supported on `Y` are pushed forward from `Y`.** A codimension-`(r + n - m)` cycle on
`X` whose restriction to an open `U` vanishes, where `U` contains every point outside `Y`, is the
pushforward of a codimension-`r` cycle on `Y`. -/
theorem exists_rawCyclePushforward_eq_of_restrict_eq_zero {m : ℕ}
    (hm : topologicalKrullDim Y = m) (U : X.Opens) (hU : ∀ x, x ∉ U → x ∈ Set.range iY) (r : ℕ)
    (δ : codimensionCycles X (r + n - m)) (hδ : codimensionCyclesRestrict U (r + n - m) δ = 0) :
    ∃ γ : codimensionCycles Y r, rawCyclePushforward (iY ≫ p) p
      (finiteType_comp_of_isClosedImmersion p hp iY) hp iY rfl hm hn r γ = δ := by
  classical
  have hinj : Function.Injective iY.base := iY.isClosedEmbedding.injective
  have hδU : ∀ x ∈ U, (δ : AlgebraicCycle X ℤ) x = 0 := fun x hx ↦
    congrArg (fun c : codimensionCycles U (r + n - m) ↦ (c : AlgebraicCycle U ℤ) ⟨x, hx⟩) hδ
  have hfin := δ.2.1.preimage hinj.injOn
  refine ⟨⟨cycleOfFiniteSupport (fun y ↦ (δ : AlgebraicCycle X ℤ) (iY y)) hfin, hfin,
    fun y hy ↦ ?_⟩, ?_⟩
  · obtain ⟨e, he, he', hmn⟩ := codim_closure_apply_eq p hp hn iY hm y
    have h := δ.2.2 (iY y) hy
    rw [he'] at h
    rw [he]
    have : e + (n - m) = r + n - m := by exact_mod_cast h
    norm_cast
    omega
  · refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
    change rawCyclePushforwardUngraded iY r _ x = _
    rw [rawCyclePushforwardUngraded_apply_apply]
    simp only [rawCyclePushforwardCoeff_eq_one_of_isClosedImmersion, mul_ite, mul_one, mul_zero]
    by_cases hx : x ∈ Set.range iY
    · obtain ⟨y0, rfl⟩ := hx
      simp only [hinj.eq_iff]
      rw [Finset.sum_ite_eq]
      split_ifs with hy0
      · rfl
      · exact (Function.notMem_support.mp fun h ↦ hy0 (Set.Finite.mem_toFinset _ |>.mpr h)).symm
    · rw [Finset.sum_eq_zero fun y _ ↦ if_neg fun h ↦ hx ⟨y, h.symm⟩]
      exact (hδU x (by by_contra h; exact hx (hU x h))).symm

omit [IsSeparated p] in
include hp hn in
/-- Below codimension `n - m`, a cycle on `X` whose restriction to the complement of `Y`
vanishes is zero. -/
theorem eq_zero_of_restrict_eq_zero_of_lt {m : ℕ} (hm : topologicalKrullDim Y = m)
    (U : X.Opens) (hU : ∀ x, x ∉ U → x ∈ Set.range iY) {r : ℕ} (hr : r < n - m)
    (δ : codimensionCycles X r) (hδ : codimensionCyclesRestrict U r δ = 0) : δ = 0 := by
  have hδU : ∀ x ∈ U, (δ : AlgebraicCycle X ℤ) x = 0 := fun x hx ↦
    congrArg (fun c : codimensionCycles U r ↦ (c : AlgebraicCycle U ℤ) ⟨x, hx⟩) hδ
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
  change (δ : AlgebraicCycle X ℤ) x = 0
  by_contra hx
  have hxU : x ∉ U := fun h ↦ hx (hδU x h)
  obtain ⟨y, rfl⟩ := hU x hxU
  obtain ⟨e, -, he', -⟩ := codim_closure_apply_eq p hp hn iY hm y
  have h := δ.2.2 (iY y) hx
  rw [he'] at h
  have : e + (n - m) = r := by exact_mod_cast h
  omega

end SupportedOnClosed

section Chow

omit [IsSeparated p] in
include hp hn in
/-- The codimension of `Y` in `X` is `dim X - dim Y`. -/
theorem codim_range_eq_sub {m : ℕ} (hm : topologicalKrullDim Y = m) :
    codim (Set.range iY) = ((n - m : ℕ) : ℕ∞) := by
  have h := dimension_codimension_formula p hp (Set.range iY) iY.isClosedEmbedding.isClosed_range
    (Set.range_nonempty _)
  have hdim : topologicalKrullDim (Set.range iY) = m := by
    rw [← hm]
    exact (iY.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph.topologicalKrullDim_eq).symm
  rw [hdim, hn] at h
  obtain ⟨d, e, hd, he, hde⟩ := exists_nat_of_add_eq h
  have : d = m := by exact_mod_cast hd.symm
  rw [he]
  norm_cast
  omega

/-- The closed-immersion pushforward `i_* : A^r(Y) → A^(r + n - m)(X)` on Chow groups. -/
noncomputable def chowGroupPushforward {m : ℕ} (hm : topologicalKrullDim Y = m) (r : ℕ) :
    chowGroup (iY ≫ p) (finiteType_comp_of_isClosedImmersion p hp iY) hm r →+
      chowGroup p hp hn (r + n - m) :=
  QuotientAddGroup.map _ _ _ (AddSubgroup.map_le_iff_le_comap.mp
    (map_rationalEquivalenceSubgroup_le_of_isClosedImmersion p hp hn iY hm r))

omit [IsIntegral Y] [IsClosedImmersion iY] in
/-- The restriction `j^* : A^r(X) → A^r(U)` to a nonempty open `U` on Chow groups. -/
noncomputable def chowGroupRestrict (U : X.Opens) [IsIntegral (U : Scheme)] (r : ℕ) :
    chowGroup p hp hn r →+ chowGroup (U.ι ≫ p) (finiteType_opens_ι_comp p hp U)
      (topologicalKrullDim_opens_eq p hp hn U) r :=
  QuotientAddGroup.map _ _ _ (AddSubgroup.map_le_iff_le_comap.mp
    (map_rationalEquivalenceSubgroup_restrict_le p hp hn U _ r))

omit [IsIntegral Y] [IsClosedImmersion iY] in
/-- `j^* : A^r(X) → A^r(U)` is surjective. -/
theorem chowGroupRestrict_surjective (U : X.Opens) [IsIntegral (U : Scheme)] (r : ℕ) :
    Function.Surjective (chowGroupRestrict p hp hn U r) := by
  intro y
  obtain ⟨c, rfl⟩ := QuotientAddGroup.mk_surjective y
  obtain ⟨d, rfl⟩ := codimensionCyclesRestrict_surjective U r c
  exact ⟨QuotientAddGroup.mk d, rfl⟩

omit [IsIntegral Y] [IsClosedImmersion iY] in
/-- If `j^* α` is rationally equivalent to zero on `U`, then `α` is rationally equivalent on `X`
to a cycle restricting to zero on `U`. -/
theorem exists_sub_mem_rationalEquivalenceSubgroup_of_restrict (U : X.Opens)
    [IsIntegral (U : Scheme)] {r : ℕ} (α : codimensionCycles X r)
    (hα : chowGroupRestrict p hp hn U r (QuotientAddGroup.mk α) = 0) :
    ∃ β ∈ rationalEquivalenceSubgroup p hp hn r, codimensionCyclesRestrict U r (α - β) = 0 := by
  have hα' : codimensionCyclesRestrict U r α ∈ rationalEquivalenceSubgroup (U.ι ≫ p)
      (finiteType_opens_ι_comp p hp U) (topologicalKrullDim_opens_eq p hp hn U) r :=
    (QuotientAddGroup.eq_zero_iff _).mp hα
  obtain ⟨β, hβ, hβα⟩ := rationalEquivalenceSubgroup_le_map_restrict p hp hn U _ r hα'
  exact ⟨β, hβ, by rw [map_sub, hβα, sub_self]⟩

/-- **Localization sequence, exactness in the middle.** For a variety `X` of dimension `n`, the
closed immersion `i : Y ⟶ X` of an integral closed subvariety of dimension `m` (codimension
`n - m`, `codim_range_eq_sub`), and the open complement `U` of `Y` (nonempty), the sequence
`A^r(Y) → A^(r + n - m)(X) → A^(r + n - m)(U)` is exact. -/
theorem chowGroup_localization_exact {m : ℕ} (hm : topologicalKrullDim Y = m) (U : X.Opens)
    [IsIntegral (U : Scheme)] (hU : (U : Set X) = (Set.range iY)ᶜ) (r : ℕ) :
    Function.Exact (chowGroupPushforward p hp hn iY hm r)
      (chowGroupRestrict p hp hn U (r + n - m)) := by
  have hU' : ∀ x, x ∉ U → x ∈ Set.range iY := fun x hx ↦ by
    by_contra h
    exact hx (show x ∈ (U : Set X) by rw [hU]; exact h)
  have hU'' : ∀ y, iY y ∉ U := fun y h ↦ by
    have : iY y ∈ (U : Set X) := h
    rw [hU] at this
    exact this ⟨y, rfl⟩
  intro y
  obtain ⟨α, rfl⟩ := QuotientAddGroup.mk_surjective y
  constructor
  · intro hα
    obtain ⟨β, hβ, hαβ⟩ := exists_sub_mem_rationalEquivalenceSubgroup_of_restrict p hp hn U α hα
    obtain ⟨γ, hγ⟩ := exists_rawCyclePushforward_eq_of_restrict_eq_zero p hp hn iY hm U hU' r
      (α - β) hαβ
    refine ⟨QuotientAddGroup.mk γ, ?_⟩
    change QuotientAddGroup.mk (rawCyclePushforward _ _ _ hp iY rfl hm hn r γ) = _
    rw [hγ, QuotientAddGroup.eq_iff_sub_mem]
    simpa using neg_mem hβ
  · rintro ⟨z, hz⟩
    rw [← hz]
    obtain ⟨γ, rfl⟩ := QuotientAddGroup.mk_surjective z
    change QuotientAddGroup.mk (codimensionCyclesRestrict U (r + n - m)
      (rawCyclePushforward _ _ _ hp iY rfl hm hn r γ)) = 0
    rw [codimensionCyclesRestrict_rawCyclePushforward_eq_zero p hp hn iY hm U hU'' r γ]
    rfl

/-- **Localization sequence below the codimension of `Y`.** In codimension `r < n - m` (where
`A^(r - c)(Y)` is zero), `j^* : A^r(X) → A^r(U)` is injective, hence an isomorphism. -/
theorem chowGroupRestrict_injective_of_lt {m : ℕ} (hm : topologicalKrullDim Y = m)
    (U : X.Opens) [IsIntegral (U : Scheme)] (hU : (U : Set X) = (Set.range iY)ᶜ) {r : ℕ}
    (hr : r < n - m) : Function.Injective (chowGroupRestrict p hp hn U r) := by
  have hU' : ∀ x, x ∉ U → x ∈ Set.range iY := fun x hx ↦ by
    by_contra h
    exact hx (show x ∈ (U : Set X) by rw [hU]; exact h)
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨α, rfl⟩ := QuotientAddGroup.mk_surjective y
  obtain ⟨β, hβ, hαβ⟩ := exists_sub_mem_rationalEquivalenceSubgroup_of_restrict p hp hn U α hy
  have h0 := eq_zero_of_restrict_eq_zero_of_lt p hp hn iY hm U hU' hr (α - β) hαβ
  rw [sub_eq_zero] at h0
  rw [h0]
  exact (QuotientAddGroup.eq_zero_iff _).mpr hβ

end Chow

end Hartshorne

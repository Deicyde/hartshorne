/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.Differentials.BertiniIncidenceCorrespondence
import Hartshorne.Scheme.ProperImage
import Hartshorne.Scheme.SerreRegularity
import Hartshorne.Intersection.ProjectiveLinearSubspaceCycle
import Hartshorne.Cohomology.FlatFamilies.NormalFamilyFlat

/-!
# Bertini's theorem: regular hyperplane sections

Hartshorne, *Algebraic Geometry*, II.8, Theorem 8.18 (pp. 179–180).

Let `k` be algebraically closed and `X ⊆ ℙⁿ_k` a nonsingular closed subvariety. The hyperplanes
`H` of `ℙⁿ_k` not containing `X` for which `H ∩ X` is regular at every point form a dense open
subset of the complete linear system `|H| = (ℙⁿ_k)^∨`.

## Proof

A hyperplane is good exactly when it is bad at no closed point of `X`: if `H ∩ X` is singular at
some point, it is singular at a closed point specializing it, because local rings of a scheme at
generizations are localizations and localizations of regular local rings are regular.

Let `r = dim X`. If `r < n`, let `B ⊆ X ×_k (ℙⁿ_k)^∨` be the closed irreducible incidence set of
dimension `n - 1` whose closed points are the pairs `(x, H)` with `H` bad at `x`. Since `X` is
projective, the second projection is proper, so the image `p₂(B)` is closed, and a closed map
does not raise dimension, so `dim p₂(B) ≤ n - 1 < n = dim (ℙⁿ_k)^∨`. Hence `p₂(B)` is a proper
closed subset of the irreducible space `(ℙⁿ_k)^∨` and its complement is dense open. A closed
point `H` lies in `p₂(B)` exactly when `H` is bad at some closed point of `X`.

If `r ≥ n`, the space of hyperplanes bad at a closed point `x` has dimension `n - r = 0`, so no
hyperplane is bad anywhere and all hyperplanes are good.

## Main result

* `Hartshorne.BertiniIncidence.bertini_regular_hyperplane_section`
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
  IsLocalRing Topology

namespace Hartshorne

universe u

/-! ### Closed maps do not raise dimension -/

section Topology

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

/-- For a closed continuous map `f` onto a quasi-sober space, an irreducible closed subset
contained in the image of a closed set `C` is the image of an irreducible closed subset
of `C`. -/
theorem exists_irreducibleCloseds_image_eq [QuasiSober β] {f : α → β} (hf : Continuous f)
    (hcl : IsClosedMap f) (T : IrreducibleCloseds β) {C : Set α} (hC : IsClosed C)
    (hTC : (T : Set β) ⊆ f '' C) :
    ∃ C' : IrreducibleCloseds α, (C' : Set α) ⊆ C ∧ f '' C' = T := by
  obtain ⟨y, hy⟩ := QuasiSober.sober T.isIrreducible T.isClosed
  obtain ⟨z, hzC, rfl⟩ := hTC hy.mem
  refine ⟨⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩,
    closure_minimal (Set.singleton_subset_iff.mpr hzC) hC, ?_⟩
  change f '' closure {z} = T
  refine le_antisymm ?_ ?_
  · refine (image_closure_subset_closure_image hf).trans ?_
    rw [Set.image_singleton, hy.def]
  · rw [← hy.def]
    exact closure_minimal (Set.singleton_subset_iff.mpr ⟨z, subset_closure rfl, rfl⟩)
      (hcl _ isClosed_closure)

/-- **A closed continuous surjection onto a quasi-sober space does not raise dimension.** Chains
of irreducible closed subsets of the target lift to chains in the source, from the top down. -/
theorem topologicalKrullDim_le_of_isClosedMap [QuasiSober β] {f : α → β} (hf : Continuous f)
    (hcl : IsClosedMap f) (hsurj : Function.Surjective f) :
    topologicalKrullDim β ≤ topologicalKrullDim α := by
  have lift : ∀ (m : ℕ) (p : LTSeries (IrreducibleCloseds β)), p.length = m →
      ∀ C : IrreducibleCloseds α, f '' C = p.last →
        ∃ q : LTSeries (IrreducibleCloseds α), q.length = m ∧ q.last = C := by
    intro m
    induction m with
    | zero => exact fun _ _ C _ => ⟨RelSeries.singleton _ C, rfl, rfl⟩
    | succ m ih =>
      intro p hp C hC
      have hp0 : p.length ≠ 0 := by omega
      have hlt : p.eraseLast.last < p.last := p.eraseLast_last_rel_last hp0
      obtain ⟨C', hC'C, hC'⟩ := exists_irreducibleCloseds_image_eq hf hcl p.eraseLast.last
        C.isClosed (by rw [hC]; exact hlt.le)
      obtain ⟨q, hq, hqC⟩ := ih p.eraseLast (by simp [hp]) C' hC'
      have hCC : q.last < C := by
        rw [hqC]
        refine lt_of_le_of_ne hC'C fun h => hlt.ne (SetLike.coe_injective ?_)
        rw [← hC', ← hC, h]
      exact ⟨q.snoc C hCC, by simp [hq], by simp⟩
  refine iSup_le fun p => ?_
  obtain ⟨C, -, hC⟩ := exists_irreducibleCloseds_image_eq hf hcl p.last isClosed_univ
    (by rw [Set.image_univ_of_surjective hsurj]; exact Set.subset_univ _)
  obtain ⟨q, hq, -⟩ := lift p.length p rfl C hC
  rw [← hq]
  exact Order.LTSeries.length_le_krullDim q

/-- If `f` is continuous and maps closed subsets of the closed set `Z` to closed sets, and the
target is quasi-sober, then `dim f(Z) ≤ dim Z`. -/
theorem topologicalKrullDim_image_le [QuasiSober β] {f : α → β} (hf : Continuous f) {Z : Set α}
    (hZ : IsClosed Z) (hcl : ∀ C : Set α, IsClosed C → C ⊆ Z → IsClosed (f '' C)) :
    topologicalKrullDim (f '' Z) ≤ topologicalKrullDim Z := by
  have : QuasiSober (f '' Z) := (hcl Z hZ le_rfl).isClosedEmbedding_subtypeVal.quasiSober
  let g : Z → f '' Z := (Set.mapsTo_image f Z).restrict f Z (f '' Z)
  refine topologicalKrullDim_le_of_isClosedMap (f := g) (hf.restrict _) ?_ ?_
  · intro C hC
    obtain ⟨C₀, hC₀, rfl⟩ := isClosed_induced_iff.mp hC
    have hC₀Z : IsClosed (C₀ ∩ Z) := hC₀.inter hZ
    refine isClosed_induced_iff.mpr ⟨_, hcl _ hC₀Z Set.inter_subset_right, ?_⟩
    ext y
    constructor
    · rintro ⟨x, ⟨hx, hxZ⟩, hxy⟩
      exact ⟨⟨x, hxZ⟩, hx, Subtype.ext hxy⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.1, ⟨hx, x.2⟩, rfl⟩
  · rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

end Topology

/-! ### Regularity at generizations -/

/-- If `x ⤳ y` and `X` is regular at `y`, then `X` is regular at `x`: the local ring at `x` is a
localization of the local ring at `y` at a prime (Theorem II.8.14A). -/
theorem isRegularAt_of_specializes {X : Scheme.{u}} {x y : X} (h : x ⤳ y)
    (hy : X.IsRegularAt y) : X.IsRegularAt x := by
  let : Algebra (X.presheaf.stalk y) (X.presheaf.stalk x) :=
    (X.presheaf.stalkSpecializes h).hom.toAlgebra
  have hloc := NormalFamily.isLocalization_stalkSpecializes h
  set p := (maximalIdeal (X.presheaf.stalk x)).comap (X.presheaf.stalkSpecializes h).hom
  have : p.IsPrime := Ideal.comap_isPrime _ _
  have : IsRegularLocalRing (X.presheaf.stalk y) := hy
  have := RegularLocal.isRegularLocalRing_localization_atPrime (X.presheaf.stalk y) p
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p) (X.presheaf.stalk x)).toRingEquiv

namespace BertiniIncidence

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### Images under the second projection -/

section Projection

variable {k : Type u} [Field k] {n : ℕ} {X : Scheme.{u}} (q : X ⟶ Spec (CommRingCat.of k))

/-- If `X` is proper over `k`, the second projection `X ×_k (ℙⁿ_k)^∨ ⟶ (ℙⁿ_k)^∨` maps closed
sets to closed sets (images of proper schemes are closed). -/
theorem isClosed_image_snd [IsProper q] (C : Set (incidenceAmbient q n)) (hC : IsClosed C) :
    IsClosed (pullback.snd q (dualProjectiveSpaceStructure k n) '' C) := by
  let g := dualProjectiveSpaceStructure k n
  let I := Scheme.IdealSheafData.vanishingIdeal (X := incidenceAmbient q n) ⟨C, hC⟩
  have : IsProper (pullback.snd q g) := inferInstance
  have h := properImage (pullback.snd q g ≫ g) g I.subschemeι (pullback.snd q g)
    ⟨inferInstance, inferInstance⟩ ⟨inferInstance, inferInstance⟩ rfl
  have hrange : Set.range (I.subschemeι ≫ pullback.snd q g) = pullback.snd q g '' C := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  exact hrange ▸ h.1

/-- Closed points `x` of `X` and `H` of `(ℙⁿ_k)^∨` come from a closed point of
`X ×_k (ℙⁿ_k)^∨`. -/
theorem incidenceAmbient_exists_closedPoint_of_isClosed [IsAlgClosed k] [LocallyOfFiniteType q]
    (x : X) (hx : IsClosed {x}) (H : projectiveSpaceScheme k n) (hH : IsClosed {H}) :
    ∃ z : incidenceAmbient q n, IsClosed {z} ∧
      pullback.fst q (dualProjectiveSpaceStructure k n) z = x ∧
      pullback.snd q (dualProjectiveSpaceStructure k n) z = H := by
  let g := dualProjectiveSpaceStructure k n
  let s : Spec (CommRingCat.of k) ⟶ incidenceAmbient q n :=
    pullback.lift (pointOfClosedPoint q x hx) (pointOfClosedPoint g H hH)
      (by rw [pointOfClosedPoint_comp, pointOfClosedPoint_comp])
  have hs : s ≫ pullback.fst q g ≫ q = 𝟙 _ := by
    rw [pullback.lift_fst_assoc, pointOfClosedPoint_comp]
  let pt : Spec (CommRingCat.of k) := IsLocalRing.closedPoint k
  refine ⟨s pt,
    (pointEquivClosedPoint (pullback.fst q g ≫ q) ⟨s, hs⟩).2, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, pullback.lift_fst, pointOfClosedPoint_apply]
  · rw [← Scheme.Hom.comp_apply, pullback.lift_snd, pointOfClosedPoint_apply]

end Projection

/-! ### Good hyperplanes -/

section Good

variable {k : Type u} [Field k] {n : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ projectiveSpaceOverScheme n (Spec (CommRingCat.of k)))

/-- **A hyperplane is good iff it is bad at no closed point.** Let `X` be a nonempty regular
scheme with a closed immersion `φ : X ⟶ ℙⁿ_k`. The hyperplane `H_a` is bad at
no closed point of `X` exactly when it does not contain `X` and `H_a ∩ X` is regular. -/
theorem forall_not_isBadHyperplaneAt_iff [IsClosedImmersion φ] [Nonempty X] (hX : X.IsRegular)
    (a : Fin (n + 1) → k) :
    (∀ x : X, IsClosed {x} → ¬ IsBadHyperplaneAt φ a x) ↔
      (∃ x : X, x ∉ (hyperplaneSectionIdeal φ a).support) ∧
        (hyperplaneSectionIdeal φ a).subscheme.IsRegular := by
  have : IsProper (projectiveSpaceOverSchemeProjection n (Spec (CommRingCat.of k))) :=
    projectiveSpaceOverSchemeProjection_isProper n _
  set q := φ ≫ projectiveSpaceOverSchemeProjection n (Spec (CommRingCat.of k))
  set I := hyperplaneSectionIdeal φ a
  have : IsLocallyNoetherian X := hX.1
  constructor
  · intro h
    have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace q
    have : JacobsonSpace I.subscheme := LocallyOfFiniteType.jacobsonSpace (I.subschemeι ≫ q)
    obtain ⟨x₀, -, hx₀⟩ := nonempty_inter_closedPoints (X := X) (Z := Set.univ)
      Set.univ_nonempty isClosed_univ.isLocallyClosed
    refine ⟨?_, LocallyOfFiniteType.isLocallyNoetherian I.subschemeι, fun y => ?_⟩
    · by_contra hcon
      push Not at hcon
      exact h x₀ hx₀ (Or.inl hcon)
    obtain ⟨y', hy'y, hy'c⟩ := nonempty_inter_closedPoints (Set.singleton_nonempty y).closure
      isClosed_closure.isLocallyClosed
    refine isRegularAt_of_specializes (specializes_iff_mem_closure.mpr hy'y) ?_
    have hxc : IsClosed {I.subschemeι y'} := by
      rw [← Set.image_singleton]
      exact I.subschemeι.isClosedEmbedding.isClosedMap _ hy'c
    by_contra hreg
    exact h _ hxc (Or.inr ⟨y', rfl, hreg⟩)
  · rintro ⟨⟨y, hy⟩, hreg⟩ x - (h | ⟨z, -, hz⟩)
    · exact hy (h y)
    · exact hz (hreg.2 z)

/-- **Bertini's theorem** (Hartshorne II, Theorem 8.18). Let `k` be algebraically closed and let
`φ : X ⟶ ℙⁿ_k` be a closed immersion of a nonsingular integral scheme, so that `X` is a
nonsingular closed subvariety of `ℙⁿ_k`. The complete linear system of hyperplanes is the dual
projective space `(ℙⁿ_k)^∨`, a closed point `H` of which represents the coefficient vectors
`a ≠ 0` of the hyperplane `H_a = {∑ aᵢ xᵢ = 0}`. Then there is a dense open subset `U` of
`(ℙⁿ_k)^∨` whose closed points are exactly the hyperplanes `H_a` not containing `X` for which the
hyperplane section `H_a ∩ X` is regular at every point. -/
theorem bertini_regular_hyperplane_section [IsAlgClosed k] [IsClosedImmersion φ] [IsIntegral X]
    (hX : X.IsRegular) :
    ∃ U : Set (projectiveSpaceScheme k n), IsOpen U ∧ Dense U ∧
      ∀ H : projectiveSpaceScheme k n, IsClosed {H} → ∀ a : Fin (n + 1) → k, a ≠ 0 →
        Represents a H →
        (H ∈ U ↔ (∃ x : X, x ∉ (hyperplaneSectionIdeal φ a).support) ∧
          (hyperplaneSectionIdeal φ a).subscheme.IsRegular) := by
  classical
  have : IsProper (projectiveSpaceOverSchemeProjection n (Spec (CommRingCat.of k))) :=
    projectiveSpaceOverSchemeProjection_isProper n _
  set q := φ ≫ projectiveSpaceOverSchemeProjection n (Spec (CommRingCat.of k)) with hq_def
  set g := dualProjectiveSpaceStructure k n
  have : JacobsonSpace (incidenceAmbient q n) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.fst q g ≫ q)
  obtain ⟨r, hr, -⟩ := exists_topologicalKrullDim_eq_trdeg q ⟨inferInstance, inferInstance⟩
  suffices h : ∃ U : Set (projectiveSpaceScheme k n), IsOpen U ∧ Dense U ∧
      ∀ H : projectiveSpaceScheme k n, IsClosed {H} → ∀ a : Fin (n + 1) → k, a ≠ 0 →
        Represents a H → (H ∈ U ↔ ∀ x : X, IsClosed {x} → ¬ IsBadHyperplaneAt φ a x) by
    obtain ⟨U, hUo, hUd, hU⟩ := h
    exact ⟨U, hUo, hUd, fun H hH a ha hra =>
      (hU H hH a ha hra).trans (forall_not_isBadHyperplaneAt_iff φ hX a)⟩
  rcases lt_or_ge r n with hrn | hnr
  · obtain ⟨-, Z, hZc, -, hZdim, hZmem⟩ := bertini_bad_hyperplane_incidence φ hX hr hrn
    set S := pullback.snd q g '' Z
    have hSc : IsClosed S := isClosed_image_snd q Z hZc
    have hSdim : topologicalKrullDim S ≤ ((n - 1 : ℕ) : WithBot ℕ∞) :=
      (topologicalKrullDim_image_le (pullback.snd q g).continuous hZc
        fun C hC _ => isClosed_image_snd q C hC).trans hZdim.le
    have hSne : S ≠ Set.univ := by
      intro hS
      have hdim : topologicalKrullDim (Set.univ : Set (projectiveSpaceScheme k n)) = n := by
        rw [IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ _).isHomeomorph]
        exact topologicalKrullDim_projectiveSpace
      rw [hS, hdim] at hSdim
      have : n ≤ n - 1 := by exact_mod_cast hSdim
      omega
    have : IrreducibleSpace (projectiveSpaceScheme k n) :=
      projectiveSpace_irreducibleSpace (k := k) (n := n)
    refine ⟨Sᶜ, hSc.isOpen_compl, hSc.isOpen_compl.dense (Set.nonempty_compl.mpr hSne),
      fun H hH a ha hra => ?_⟩
    rw [Set.mem_compl_iff, ← not_iff_not, not_not]
    push Not
    constructor
    · rintro ⟨z₀, hz₀, hz₀H⟩
      obtain ⟨z, ⟨hzZ, hzH⟩, hzc⟩ := nonempty_inter_closedPoints (X := incidenceAmbient q n)
        (Z := Z ∩ pullback.snd q g ⁻¹' {H}) ⟨z₀, hz₀, hz₀H⟩
        (hZc.inter (hH.preimage (pullback.snd q g).continuous)).isLocallyClosed
      have hzH : pullback.snd q g z = H := hzH
      refine ⟨pullback.fst q g z, (incidenceAmbient_closedPoint q z hzc).1, ?_⟩
      exact (hZmem z hzc a ha (hzH ▸ hra)).mp hzZ
    · rintro ⟨x, hx, hbad⟩
      obtain ⟨z, hzc, hzx, hzH⟩ := incidenceAmbient_exists_closedPoint_of_isClosed q x hx H hH
      exact ⟨z, (hZmem z hzc a ha (hzH ▸ hra)).mpr (hzx ▸ hbad), hzH⟩
  · refine ⟨Set.univ, isOpen_univ, dense_univ, fun H hH a ha hra => ?_⟩
    simp only [Set.mem_univ, true_iff]
    intro x hx hbad
    have : IsRegularLocalRing (X.presheaf.stalk x) := hX.2 x
    have hmem := (mem_badHyperplaneSubspace_iff φ x a).mpr hbad
    have hfin := finrank_badHyperplaneSubspace φ hX hr x hx
    rw [Nat.sub_eq_zero_of_le hnr, Submodule.finrank_eq_zero] at hfin
    rw [hfin] at hmem
    exact ha ((Submodule.mem_bot k).mp hmem)

end Good

end BertiniIncidence

end Hartshorne

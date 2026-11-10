/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.WeilClassGroup
import Mathlib.Algebra.Exact.Basic

/-!
# Restriction of class groups to open complements

Hartshorne, *Algebraic Geometry*, II.6, Proposition 6.5 (p. 133).

Let `X` satisfy Hartshorne's condition `(*)`, let `Z` be a proper closed subset and let
`U = X - Z`. Restricting Weil divisors along the open immersion `U ⟶ X` sends a prime divisor
`Y` to `Y ∩ U` (or to zero when `Y` misses `U`), and preserves principal divisors because the
function field of `X` is identified with that of `U` compatibly with the codimension-one stalks.
This gives a surjection `Cl X → Cl U`, which is an isomorphism when `codim (Z, X) ≥ 2`; when `Z`
is irreducible of codimension one, the sequence `ℤ → Cl X → Cl U → 0` with `1 ↦ [Z]` is exact.

The proper closed subset `Z` is a `Closeds X` whose complement `Z.compl` is nonempty; the
surjectivity statement is stated for an arbitrary nonempty open subscheme `U`, which is the same
thing with `Z = Uᶜ`.
-/

noncomputable section

open CategoryTheory Limits TopologicalSpace Order

namespace AlgebraicGeometry

universe u

/-- A nonempty open subscheme of a scheme satisfying `(*)` satisfies `(*)`. -/
theorem Scheme.SatisfiesConditionStar.restrict {X : Scheme.{u}} (hX : X.SatisfiesConditionStar)
    (U : X.Opens) [Nonempty U] : (U : Scheme).SatisfiesConditionStar := by
  have := hX.isNoetherian
  have := hX.isIntegral
  have := hX.isSeparated
  refine ⟨?_, isIntegral_of_isOpenImmersion U.ι, ?_, ?_⟩
  · have : CompactSpace U :=
      isCompact_iff_compactSpace.mp (NoetherianSpace.isCompact (U : Set X))
    exact {}
  · exact ⟨by rw [← terminal.comp_from U.ι]; infer_instance⟩
  · intro y hy
    have hy' : coheight (U.ι y) = 1 := by
      rw [coheight_eq_of_isOpenImmersion]
      exact hy
    have := hX.isRegularInCodimensionOne _ hy'
    exact IsRegularLocalRing.of_ringEquiv (asIso (U.ι.stalkMap y)).commRingCatIsoToRingEquiv


section OpenSubscheme

variable {X : Scheme.{u}}

/-- A nonempty open subscheme of an integral scheme is integral. -/
instance Scheme.Opens.isIntegral_toScheme [IsIntegral X] (U : X.Opens) [Nonempty U] :
    IsIntegral (U : Scheme) :=
  isIntegral_of_isOpenImmersion U.ι

/-- The function field of an integral scheme is identified with that of a nonempty open
subscheme, via the stalk map of the open immersion at the generic point. -/
noncomputable def Scheme.Opens.functionFieldIso [IsIntegral X] (U : X.Opens) [Nonempty U] :
    X.functionField ≅ (U : Scheme).functionField :=
  have : IsIso (X.presheaf.stalkSpecializes
      (Inseparable.of_eq (genericPoint_eq_of_isOpenImmersion U.ι)).specializes) :=
    (X.presheaf.stalkCongr (Inseparable.of_eq (genericPoint_eq_of_isOpenImmersion U.ι))).isIso_inv
  asIso (X.presheaf.stalkSpecializes
      (Inseparable.of_eq (genericPoint_eq_of_isOpenImmersion U.ι)).specializes ≫
    U.ι.stalkMap (genericPoint U))

/-- The function field isomorphism is compatible with the stalk maps of the open immersion. -/
theorem Scheme.Opens.functionFieldIso_hom_algebraMap [IsIntegral X] (U : X.Opens) [Nonempty U]
    (y : (U : Scheme)) (r : X.presheaf.stalk (U.ι y)) :
    U.functionFieldIso.hom (algebraMap (X.presheaf.stalk (U.ι y)) X.functionField r) =
      algebraMap ((U : Scheme).presheaf.stalk y) (U : Scheme).functionField
        (U.ι.stalkMap y r) := by
  have key : X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes (Set.mem_univ _) :
        genericPoint X ⤳ U.ι y) ≫ U.functionFieldIso.hom =
      U.ι.stalkMap y ≫ (U : Scheme).presheaf.stalkSpecializes
        ((genericPoint_spec (U : Scheme)).specializes (Set.mem_univ _)) := by
    rw [functionFieldIso, asIso_hom,
      TopCat.Presheaf.stalkSpecializes_comp_assoc, Scheme.Hom.stalkSpecializes_stalkMap]
  exact ConcreteCategory.congr_hom key r

/-- The order of vanishing at a point of an open subscheme agrees with the order of
vanishing at its image, under the function field isomorphism. -/
theorem Scheme.Opens.ord_functionFieldIso_hom [IsIntegral X] [IsLocallyNoetherian X]
    (U : X.Opens) [Nonempty U] (f : X.functionField) (y : (U : Scheme)) :
    Scheme.ord (U.functionFieldIso.hom f) y = Scheme.ord f (U.ι y) := by
  by_cases hy : coheight y = 1
  · have hy' : coheight (U.ι y) = 1 := (coheight_eq_of_isOpenImmersion U.ι).trans hy
    rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hy, Scheme.ord_eq_ordHom_of_coheight_eq_one hy']
    congr 2
    unfold Scheme.ordHom
    have : Ring.KrullDimLE 1 (X.presheaf.stalk (U.ι y)) := krullDimLE_of_coheight_le hy'.le
    have : Ring.KrullDimLE 1 ((U : Scheme).presheaf.stalk y) := krullDimLE_of_coheight_le hy.le
    exact Hartshorne.ordFrac_ringEquiv (asIso (U.ι.stalkMap y)).commRingCatIsoToRingEquiv
      U.functionFieldIso.commRingCatIsoToRingEquiv (fun r ↦ U.functionFieldIso_hom_algebraMap y r) f
  · have hy' : coheight (U.ι y) ≠ 1 := by rwa [coheight_eq_of_isOpenImmersion]
    rw [Scheme.ord_eq_zero_of_coheight_neq_one hy, Scheme.ord_eq_zero_of_coheight_neq_one hy']

end OpenSubscheme

section Divisors

variable {X : Scheme.{u}}

/-- Weil divisors are determined by their coefficients. -/
theorem Scheme.WeilDivisor.ext_apply {D E : X.WeilDivisor} (h : ∀ x, D.1 x = E.1 x) : D = E :=
  Subtype.ext (Function.locallyFinsuppWithin.ext h)

/-- The Weil divisor `1 · P` of a prime divisor `P`. -/
noncomputable def Scheme.PrimeDivisor.toWeilDivisor (P : X.PrimeDivisor) : X.WeilDivisor := by
  classical
  refine ⟨Function.locallyFinsuppWithin.single P.1 1, fun x hx ↦ ?_⟩
  have hxP : x ≠ P.1 := fun h ↦ hx (h ▸ P.2)
  simp [hxP]

/-- The coefficient of `1 · P` at the generic point of `P`. -/
theorem Scheme.PrimeDivisor.toWeilDivisor_apply_self (P : X.PrimeDivisor) :
    P.toWeilDivisor.1 P.1 = 1 := by
  classical
  simp [toWeilDivisor]

/-- The coefficients of `1 · P` away from the generic point of `P` vanish. -/
theorem Scheme.PrimeDivisor.toWeilDivisor_apply_of_ne (P : X.PrimeDivisor) {x : X}
    (hx : x ≠ P.1) : P.toWeilDivisor.1 x = 0 := by
  classical
  simp [toWeilDivisor, hx]

/-- Restriction of Weil divisors to an open subscheme: a prime divisor of `X` meeting `U`
restricts to its intersection with `U`, and one missing `U` restricts to zero. -/
noncomputable def Scheme.weilDivisorRestrict (U : X.Opens) :
    X.WeilDivisor →+ (U : Scheme).WeilDivisor where
  toFun D :=
    ⟨{ toFun := fun y ↦ D.1 (U.ι y)
       supportWithinDomain' := Set.subset_univ _
       supportLocallyFiniteWithinDomain' := fun y _ ↦ by
         obtain ⟨t, ht, hfin⟩ :=
           D.1.supportLocallyFiniteWithinDomain (U.ι y) (Set.mem_univ _)
         refine ⟨U.ι ⁻¹' t, U.ι.continuous.continuousAt.preimage_mem_nhds ht, ?_⟩
         refine (hfin.preimage U.ι.isOpenEmbedding.injective.injOn).subset ?_
         rintro z ⟨hz, hz'⟩
         exact ⟨hz, hz'⟩ },
      fun y hy ↦ D.2 (U.ι y) (by rwa [coheight_eq_of_isOpenImmersion])⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Coefficients of a restricted Weil divisor. -/
@[simp]
theorem Scheme.weilDivisorRestrict_apply (U : X.Opens) (D : X.WeilDivisor) (y : (U : Scheme)) :
    (X.weilDivisorRestrict U D).1 y = D.1 (U.ι y) :=
  rfl

/-- The function field isomorphism of a nonempty open subscheme, as a ring equivalence. -/
noncomputable abbrev Scheme.Opens.functionFieldEquiv [IsIntegral X] (U : X.Opens) [Nonempty U] :
    X.functionField ≃+* (U : Scheme).functionField :=
  U.functionFieldIso.commRingCatIsoToRingEquiv

/-- Restriction sends the principal divisor of `f` to the principal divisor of the
corresponding rational function on the open subscheme. -/
theorem Scheme.weilDivisorRestrict_principalDivisor (hX : X.SatisfiesConditionStar)
    (U : X.Opens) [Nonempty U] :
    let _ : IsIntegral X := hX.isIntegral
    ∀ f : X.functionFieldˣ, X.weilDivisorRestrict U (X.principalDivisor hX f) =
      (U : Scheme).principalDivisor (hX.restrict U)
        (Units.map (U.functionFieldEquiv : X.functionField →* (U : Scheme).functionField) f) := by
  have := hX.isNoetherian
  have := hX.isIntegral
  intro _ f
  apply Scheme.WeilDivisor.ext_apply
  intro y
  rw [Scheme.weilDivisorRestrict_apply]
  have h1 := Scheme.principalDivisor_apply hX f (U.ι y)
  have h2 := Scheme.principalDivisor_apply (hX.restrict U)
    (Units.map (U.functionFieldEquiv : X.functionField →* (U : Scheme).functionField) f) y
  rw [h1, h2, Units.coe_map]
  exact (U.ord_functionFieldIso_hom _ y).symm

/-- Restriction of divisor classes to a nonempty open subscheme. -/
noncomputable def Scheme.weilClassGroupRestrict (hX : X.SatisfiesConditionStar)
    (U : X.Opens) [Nonempty U] :
    X.WeilClassGroup hX →+ (U : Scheme).WeilClassGroup (hX.restrict U) :=
  QuotientAddGroup.map _ _ (X.weilDivisorRestrict U) <| by
    have := hX.isNoetherian
    have := hX.isIntegral
    intro D hD
    change D ∈ (X.principalDivisorHom hX).range at hD
    obtain ⟨f, rfl⟩ := hD
    change X.weilDivisorRestrict U (X.principalDivisor hX f.toMul) ∈
      ((U : Scheme).principalDivisorHom (hX.restrict U)).range
    rw [Scheme.weilDivisorRestrict_principalDivisor]
    exact ⟨Additive.ofMul _, rfl⟩

/-- Restriction of divisor classes is computed on representatives. -/
theorem Scheme.weilClassGroupRestrict_weilDivisorClassHom (hX : X.SatisfiesConditionStar)
    (U : X.Opens) [Nonempty U] (D : X.WeilDivisor) :
    X.weilClassGroupRestrict hX U (X.weilDivisorClassHom hX D) =
      (U : Scheme).weilDivisorClassHom (hX.restrict U) (X.weilDivisorRestrict U D) :=
  rfl

/-- Extension by zero of a Weil divisor on a Noetherian open subscheme. -/
noncomputable def Scheme.weilDivisorExtend (U : X.Opens) [IsNoetherian (U : Scheme)]
    (E : (U : Scheme).WeilDivisor) : X.WeilDivisor := by
  classical
  let g : X → ℤ := fun x ↦ if h : x ∈ U then E.1 (show (U : Scheme) from ⟨x, h⟩) else 0
  have hfin : g.support.Finite := by
    refine ((Scheme.WeilDivisor.support_finite E).image U.ι).subset ?_
    intro x hx
    by_cases h : x ∈ U
    · refine ⟨(show (U : Scheme) from ⟨x, h⟩), ?_, rfl⟩
      simp only [g, h, dif_pos, Function.mem_support] at hx
      exact hx
    · simp [g, h] at hx
  refine ⟨{ toFun := g
            supportWithinDomain' := Set.subset_univ _
            supportLocallyFiniteWithinDomain' := fun _ _ ↦
              ⟨Set.univ, Filter.univ_mem, by simpa using hfin⟩ }, fun x hx ↦ ?_⟩
  change g x = 0
  by_cases h : x ∈ U
  · have hx' : coheight (show (U : Scheme) from ⟨x, h⟩) ≠ 1 := by
      rw [← coheight_eq_of_isOpenImmersion U.ι]
      exact hx
    simp only [g, dif_pos h]
    exact E.2 _ hx'
  · simp [g, h]

/-- Extension by zero is a section of restriction. -/
theorem Scheme.weilDivisorRestrict_weilDivisorExtend (U : X.Opens) [IsNoetherian (U : Scheme)]
    (E : (U : Scheme).WeilDivisor) :
    X.weilDivisorRestrict U (X.weilDivisorExtend U E) = E := by
  classical
  apply Scheme.WeilDivisor.ext_apply
  intro y
  have hy : U.ι y ∈ U := y.2
  change (if h : U.ι y ∈ U then E.1 (show (U : Scheme) from ⟨U.ι y, h⟩) else 0) = E.1 y
  rw [dif_pos hy]
  rfl

end Divisors

section Codimension

variable {X : Scheme.{u}}

/-- The codimension of a closed subset is at most the coheight of any of its points. -/
theorem Scheme.codim_le_coheight {Z : Set X} (hZ : IsClosed Z) {x : X} (hx : x ∈ Z) :
    Hartshorne.codim Z ≤ coheight x := by
  have hsub : ((irreducibleSetEquivPoints (α := X)).symm x : Set X) ⊆ Z := by
    rw [coe_irreducibleEquivPoints_symm_apply]
    exact closure_minimal (Set.singleton_subset_iff.2 hx) hZ
  calc Hartshorne.codim Z ≤ coheight ((irreducibleSetEquivPoints (α := X)).symm x) :=
        iInf₂_le (f := fun (W : IrreducibleCloseds X) (_ : (W : Set X) ⊆ Z) ↦ coheight W) _ hsub
    _ = coheight x := coheight_orderIso _ _

/-- The codimension of an irreducible closed subset is the coheight of its generic point. -/
theorem Scheme.coheight_genericPoint_eq_codim {Z : Set X} (hZ : IsIrreducible Z)
    (hZc : IsClosed Z) : coheight hZ.genericPoint = Hartshorne.codim Z := by
  refine le_antisymm ?_ (Scheme.codim_le_coheight hZc ?_)
  · rw [← coheight_orderIso (irreducibleSetEquivPoints (α := X)).symm]
    refine le_iInf₂ fun W hW ↦ coheight_anti ?_
    change (W : Set X) ⊆ ((irreducibleSetEquivPoints (α := X)).symm hZ.genericPoint : Set X)
    rw [coe_irreducibleEquivPoints_symm_apply, hZ.closure_genericPoint hZc]
    exact hW
  · have h := subset_closure (s := ({hZ.genericPoint} : Set X)) rfl
    rwa [hZ.closure_genericPoint hZc] at h

/-- The prime divisor of an irreducible closed subset of codimension one. -/
noncomputable def Scheme.primeDivisorOfIsIrreducible {Z : Set X} (hZ : IsIrreducible Z)
    (hZc : IsClosed Z) (h : Hartshorne.codim Z = 1) : X.PrimeDivisor :=
  ⟨hZ.genericPoint, (Scheme.coheight_genericPoint_eq_codim hZ hZc).trans h⟩

/-- A point of an irreducible closed subset `Z` of finite codimension whose coheight equals
`codim Z` is the generic point of `Z`. -/
theorem Scheme.eq_genericPoint_of_coheight_eq {Z : Set X} (hZ : IsIrreducible Z)
    (hZc : IsClosed Z) {x : X} (hx : x ∈ Z) (hx1 : coheight x = Hartshorne.codim Z)
    (hfin : Hartshorne.codim Z < ⊤) : x = hZ.genericPoint := by
  let e := (irreducibleSetEquivPoints (α := X)).symm
  have hle : e x ≤ e hZ.genericPoint := by
    change ((e x : Set X)) ⊆ (e hZ.genericPoint : Set X)
    rw [coe_irreducibleEquivPoints_symm_apply, coe_irreducibleEquivPoints_symm_apply,
      hZ.closure_genericPoint hZc]
    exact closure_minimal (Set.singleton_subset_iff.2 hx) hZc
  have hcoh : coheight (e hZ.genericPoint) = coheight (e x) := by
    rw [coheight_orderIso, coheight_orderIso, hx1,
      Scheme.coheight_genericPoint_eq_codim hZ hZc]
  apply e.injective
  by_contra hne
  have hlt : e x < e hZ.genericPoint := lt_of_le_of_ne hle hne
  have := coheight_strictAnti hlt (by rw [hcoh, coheight_orderIso, hx1]; exact hfin)
  exact this.ne hcoh

end Codimension

section Main

variable {X : Scheme.{u}}

/-- If the class of `D` restricts to zero on `U`, then `D` agrees with a principal divisor on
`U`. -/
theorem Scheme.exists_principalDivisor_eqOn_of_weilClassGroupRestrict_eq_zero
    (hX : X.SatisfiesConditionStar) (U : X.Opens) [Nonempty U] (D : X.WeilDivisor)
    (hD : X.weilClassGroupRestrict hX U (X.weilDivisorClassHom hX D) = 0) :
    let _ : IsIntegral X := hX.isIntegral
    ∃ f : X.functionFieldˣ, ∀ x ∈ U, (D - X.principalDivisor hX f).1 x = 0 := by
  have := hX.isNoetherian
  have := hX.isIntegral
  intro _
  rw [Scheme.weilClassGroupRestrict_weilDivisorClassHom] at hD
  have hmem : X.weilDivisorRestrict U D ∈
      (U : Scheme).principalDivisorSubgroup (hX.restrict U) :=
    (QuotientAddGroup.eq_zero_iff _).1 hD
  change _ ∈ ((U : Scheme).principalDivisorHom (hX.restrict U)).range at hmem
  obtain ⟨g, hg⟩ := hmem
  let f : X.functionFieldˣ :=
    Units.map (U.functionFieldEquiv.symm : (U : Scheme).functionField →* X.functionField) g.toMul
  refine ⟨f, fun x hx ↦ ?_⟩
  have hrestr := Scheme.weilDivisorRestrict_principalDivisor hX U f
  have hgg : Units.map (U.functionFieldEquiv : X.functionField →* (U : Scheme).functionField) f =
      g.toMul := by
    ext
    simp [f]
  rw [hgg] at hrestr
  have hy := congrArg (fun E : (U : Scheme).WeilDivisor ↦ E.1 (show (U : Scheme) from ⟨x, hx⟩))
    (hrestr.trans hg)
  change (X.principalDivisor hX f).1 x = D.1 x at hy
  change D.1 x - (X.principalDivisor hX f).1 x = 0
  rw [hy, sub_self]

/-- **Hartshorne II, Proposition 6.5, surjectivity.** Restriction of divisor classes to a
nonempty open subscheme is surjective. -/
theorem Scheme.weilClassGroupRestrict_surjective (hX : X.SatisfiesConditionStar)
    (U : X.Opens) [Nonempty U] : Function.Surjective (X.weilClassGroupRestrict hX U) := by
  have := (hX.restrict U).isNoetherian
  intro c
  obtain ⟨E, rfl⟩ := QuotientAddGroup.mk_surjective c
  refine ⟨X.weilDivisorClassHom hX (X.weilDivisorExtend U E), ?_⟩
  rw [Scheme.weilClassGroupRestrict_weilDivisorClassHom,
    Scheme.weilDivisorRestrict_weilDivisorExtend]
  rfl

/-- **Hartshorne II, Proposition 6.5, codimension at least two.** If the proper closed subset
`Z` has codimension at least two, restriction `Cl X → Cl (X - Z)` is an isomorphism. -/
theorem Scheme.weilClassGroupRestrict_bijective_of_two_le_codim (hX : X.SatisfiesConditionStar)
    (Z : Closeds X) [Nonempty Z.compl] (hZ : 2 ≤ Hartshorne.codim (Z : Set X)) :
    Function.Bijective (X.weilClassGroupRestrict hX Z.compl) := by
  have := hX.isNoetherian
  have := hX.isIntegral
  refine ⟨(injective_iff_map_eq_zero _).2 fun c hc ↦ ?_,
    Scheme.weilClassGroupRestrict_surjective hX _⟩
  obtain ⟨D, rfl⟩ := QuotientAddGroup.mk_surjective c
  obtain ⟨f, hf⟩ :=
    Scheme.exists_principalDivisor_eqOn_of_weilClassGroupRestrict_eq_zero hX Z.compl D hc
  have hE : D - X.principalDivisor hX f = 0 := by
    apply Scheme.WeilDivisor.ext_apply
    intro x
    by_cases hxU : x ∈ Z.compl
    · exact hf x hxU
    · by_cases hx1 : coheight x = 1
      · have hxZ : x ∈ (Z : Set X) := by simpa [Closeds.compl] using hxU
        have h := Scheme.codim_le_coheight Z.isClosed hxZ
        rw [hx1] at h
        exact absurd (hZ.trans h) (by decide)
      · exact (D - X.principalDivisor hX f).2 x hx1
  apply (QuotientAddGroup.eq_zero_iff D).2
  change D ∈ (X.principalDivisorHom hX).range
  exact ⟨Additive.ofMul f, (sub_eq_zero.1 hE).symm⟩

/-- **Hartshorne II, Proposition 6.5, codimension one.** If `Z` is an irreducible closed subset
of codimension one, the sequence `ℤ → Cl X → Cl (X - Z) → 0`, with `1 ↦ [Z]`, is exact. -/
theorem Scheme.weilClassGroupRestrict_exact_of_codim_eq_one (hX : X.SatisfiesConditionStar)
    (Z : Closeds X) [Nonempty Z.compl] (hZ : IsIrreducible (Z : Set X))
    (hcodim : Hartshorne.codim (Z : Set X) = 1) :
    Function.Exact
        (zmultiplesHom (X.WeilClassGroup hX) (X.weilDivisorClassHom hX
          (X.primeDivisorOfIsIrreducible hZ Z.isClosed hcodim).toWeilDivisor))
        (X.weilClassGroupRestrict hX Z.compl) ∧
      Function.Surjective (X.weilClassGroupRestrict hX Z.compl) := by
  have := hX.isNoetherian
  have := hX.isIntegral
  set P := X.primeDivisorOfIsIrreducible hZ Z.isClosed hcodim with hP
  have hPZ : P.1 ∈ (Z : Set X) := (hZ.isGenericPoint_genericPoint Z.isClosed).mem
  have hne : ∀ x ∈ Z.compl, x ≠ P.1 := fun x hx hxP ↦ hx (hxP ▸ hPZ)
  refine ⟨fun c ↦ ⟨fun hc ↦ ?_, ?_⟩, Scheme.weilClassGroupRestrict_surjective hX _⟩
  · obtain ⟨D, rfl⟩ := QuotientAddGroup.mk_surjective c
    obtain ⟨f, hf⟩ :=
      Scheme.exists_principalDivisor_eqOn_of_weilClassGroupRestrict_eq_zero hX Z.compl D hc
    let n : ℤ := (D - X.principalDivisor hX f).1 P.1
    have hE : D - X.principalDivisor hX f = n • P.toWeilDivisor := by
      apply Scheme.WeilDivisor.ext_apply
      intro x
      change _ = n • P.toWeilDivisor.1 x
      by_cases hxU : x ∈ Z.compl
      · rw [hf x hxU, P.toWeilDivisor_apply_of_ne (hne x hxU), smul_zero]
      · have hxZ : x ∈ (Z : Set X) := by simpa [Closeds.compl] using hxU
        by_cases hx1 : coheight x = 1
        · have hxP : x = P.1 :=
            Scheme.eq_genericPoint_of_coheight_eq hZ Z.isClosed hxZ (hx1.trans hcodim.symm)
              (by rw [hcodim]; exact ENat.one_lt_top)
          rw [hxP, P.toWeilDivisor_apply_self, smul_eq_mul, mul_one]
        · have hxP : x ≠ P.1 := fun h ↦ hx1 (h ▸ P.2)
          rw [(D - X.principalDivisor hX f).2 x hx1, P.toWeilDivisor_apply_of_ne hxP, smul_zero]
    refine ⟨n, ?_⟩
    rw [zmultiplesHom_apply, ← map_zsmul, ← hE]
    exact ((Scheme.weilDivisorClass_eq_iff hX _ _).2 ⟨f, by abel⟩).symm
  · rintro ⟨n, rfl⟩
    rw [zmultiplesHom_apply, map_zsmul, Scheme.weilClassGroupRestrict_weilDivisorClassHom]
    have h0 : X.weilDivisorRestrict Z.compl P.toWeilDivisor = 0 := by
      apply Scheme.WeilDivisor.ext_apply
      intro y
      exact P.toWeilDivisor_apply_of_ne (hne _ y.2)
    rw [h0, map_zero, smul_zero]

end Main


end AlgebraicGeometry

/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.SmoothMorphisms.SmoothTangentCriterion
import Hartshorne.Scheme.CoherentFibreRank
import Hartshorne.Scheme.DimensionAtClosedPoint
import Hartshorne.Scheme.Differentials.DenseNonsingularLocus
import Hartshorne.Scheme.Differentials.FieldDifferentialsDimension
import Mathlib.FieldTheory.SeparablyGenerated

/-!
# Dominant morphisms are generically smooth on the source in characteristic zero

Hartshorne, *Algebraic Geometry*, III, Lemma 10.5 (p. 271).

Let `f : X ⟶ Y` be a dominant morphism of integral schemes of finite type over an algebraically
closed field `k` of characteristic zero. Then there is a nonempty open `U` of `X` such that
`U ⟶ Y` is smooth of some relative dimension
(`Hartshorne.exists_nonempty_open_smooth_of_isDominant`). The relative dimension is
`n = dim X - dim Y` (`Hartshorne.exists_nonempty_open_smoothOfRelativeDimension_of_isDominant`).

## Proof

We follow Hartshorne's proof.

* By II.8.16 (`Hartshorne.exists_nonempty_dense_isRegularAt`) we may replace `X` and `Y` by
  nonempty open subsets that are nonsingular; since `f` is dominant, it sends the generic point
  of `X` to the generic point of `Y`, so the open sets can be chosen compatibly.
* Since `k` has characteristic zero, the extension of function fields `K(X)/K(Y)` is finitely
  generated and separably generated, so by II.8.6A (`Hartshorne.trdeg_le_rank_kaehlerDifferential`)
  `Ω_{K(X)/K(Y)}` has dimension `n = tr.deg K(X)/K(Y) = dim X - dim Y`.
* The stalk of `Ω_{X/Y}` at the generic point is `Ω_{K(X)/K(Y)}`, a free `K(X)`-module, so by
  II Ex. 5.7 (`Hartshorne.exists_isFree_restrict_of_free_stalk_of_isLocallyNoetherian`) the sheaf
  `Ω_{X/Y}` is free on a nonempty open set, of rank `n`. By the fibre criterion
  (`AlgebraicGeometry.Scheme.relativeDifferentials_isLocallyFreeOfRank_iff`) the relative
  differentials of the restricted morphism are locally free of rank `n`.
* By Proposition 10.4 (`Hartshorne.SmoothTangent.smoothOfRelativeDimension_tfae_of_isRegularAt`)
  the restricted morphism of nonsingular varieties is smooth of relative dimension `n`.
-/

universe u

open CategoryTheory AlgebraicGeometry Module IsLocalRing
open scoped TensorProduct

namespace Hartshorne

/-- The transcendence degree over `k` of the local ring at a point `y` equal to the generic point
of `Y` is that of the function field. -/
theorem trdeg_stalk_eq_of_eq_genericPoint {k : Type u} [Field k] {Y : Scheme.{u}} [IsIntegral Y]
    (p : Y ⟶ Spec (.of k)) (y : Y) (hy : genericPoint Y = y) :
    (letI : Algebra k (Y.presheaf.stalk y) :=
      ((Y.presheaf.germ (p ⁻¹ᵁ ⊤) y trivial).hom.comp
        ((p.app ⊤).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)).toAlgebra;
      Algebra.trdeg k (Y.presheaf.stalk y)) =
      (letI := functionFieldAlgebra p; Algebra.trdeg k Y.functionField) := by
  subst hy
  rfl

/-- **Hartshorne III, Lemma 10.5**, with the relative dimension. Let `f : X ⟶ Y` be a dominant
morphism of integral schemes of finite type over an algebraically closed field `k` of
characteristic zero. Then there are `n` with `dim X = dim Y + n` and a nonempty open subset `U` of
`X` such that the restriction `U ⟶ Y` of `f` is smooth of relative dimension `n`.

This makes explicit the value `n = dim X - dim Y` that appears in Hartshorne's proof. -/
theorem exists_nonempty_open_smoothOfRelativeDimension_of_isDominant {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {X Y : Scheme.{u}} (pX : X ⟶ Spec (.of k))
    (pY : Y ⟶ Spec (.of k)) (hX : LocallyOfFiniteType pX ∧ QuasiCompact pX)
    (hY : LocallyOfFiniteType pY ∧ QuasiCompact pY)
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) (hf : f ≫ pY = pX) [IsDominant f] :
    ∃ n : ℕ, topologicalKrullDim X = topologicalKrullDim Y + n ∧
      ∃ U : X.Opens, (U : Set X).Nonempty ∧ SmoothOfRelativeDimension n (U.ι ≫ f) := by
  subst hf
  have : LocallyOfFiniteType (f ≫ pY) := hX.1
  have : QuasiCompact (f ≫ pY) := hX.2
  have : LocallyOfFiniteType pY := hY.1
  have : QuasiCompact pY := hY.2
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (f ≫ pY)
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian pY
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f pY
  set η := genericPoint X
  -- `f` sends the generic point of `X` to the generic point of `Y`
  have hgen : f η = genericPoint Y := by
    apply ((genericPoint_spec Y).eq _).symm
    have h := (genericPoint_spec X).image f.continuous
    rwa [Set.image_univ, f.denseRange.closure_range] at h
  -- Step 1 (II.8.16): nonsingular nonempty open subsets of `X` and `Y`
  obtain ⟨UX, hUXne, -, hUXreg⟩ := exists_nonempty_dense_isRegularAt (f ≫ pY)
  obtain ⟨UY, hUYne, -, hUYreg⟩ := exists_nonempty_dense_isRegularAt pY
  have hηUX : η ∈ UX :=
    ((genericPoint_spec X).mem_open_set_iff UX.isOpen).mpr (by simpa using hUXne)
  have hηUY : f η ∈ UY := hgen ▸
    ((genericPoint_spec Y).mem_open_set_iff UY.isOpen).mpr (by simpa using hUYne)
  -- Step 2 (II.8.6A): `Ω_{K(X)/K(Y)}` has dimension `tr.deg K(X)/K(Y)`
  have hfield : IsField (Y.presheaf.stalk (f η)) := hgen ▸ Field.toIsField Y.functionField
  let : Field (Y.presheaf.stalk (f η)) := hfield.toField
  let : Algebra (Y.presheaf.stalk (f η)) (X.presheaf.stalk η) := (f.stalkMap η).hom.toAlgebra
  have : Algebra.EssFiniteType (Y.presheaf.stalk (f η)) (X.presheaf.stalk η) :=
    LocallyOfFiniteType.stalkMap f η
  let φ : Algebra k (Y.presheaf.stalk (f η)) :=
    ((Y.presheaf.germ (pY ⁻¹ᵁ ⊤) (f η) trivial).hom.comp
      ((pY.app ⊤).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)).toAlgebra
  have : CharZero (Y.presheaf.stalk (f η)) :=
    charZero_of_injective_ringHom (algebraMap k (Y.presheaf.stalk (f η))).injective
  -- separable generation in characteristic zero
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField
    (Y.presheaf.stalk (f η)) (X.presheaf.stalk η)
  have htrdeg : Algebra.trdeg (Y.presheaf.stalk (f η)) (X.presheaf.stalk η) =
      Module.rank (X.presheaf.stalk η) Ω[X.presheaf.stalk η⁄Y.presheaf.stalk (f η)] :=
    ((trdeg_le_rank_kaehlerDifferential (IntermediateField.fg_top_iff.mpr inferInstance)).2.1).mpr
      ⟨s, hs, hsep⟩
  set n := finrank (X.presheaf.stalk η) Ω[X.presheaf.stalk η⁄Y.presheaf.stalk (f η)] with hn
  have hntr : Algebra.trdeg (Y.presheaf.stalk (f η)) (X.presheaf.stalk η) = n := by
    rw [htrdeg, hn, Module.finrank_eq_rank]
  -- `dim X = dim Y + n`, from `dim = tr.deg` and the tower `k ⊆ K(Y) ⊆ K(X)`
  have hpX : FiniteType (f ≫ pY) := hX
  obtain ⟨rX, hXdim, hXtr⟩ := exists_topologicalKrullDim_eq_trdeg (f ≫ pY) hpX
  obtain ⟨rY, hYdim, hYtr⟩ := exists_topologicalKrullDim_eq_trdeg pY hY
  rw [← trdeg_stalk_eq_of_eq_genericPoint pY (f η) hgen.symm] at hYtr
  let := functionFieldAlgebra (f ≫ pY)
  have : IsScalarTower k (Y.presheaf.stalk (f η)) (X.presheaf.stalk η) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      change _ = f.stalkMap η (Y.presheaf.germ (pY ⁻¹ᵁ ⊤) (f η) trivial
        (pY.app ⊤ ((Scheme.ΓSpecIso (.of k)).inv a)))
      exact (Scheme.Hom.germ_stalkMap_apply f (pY ⁻¹ᵁ ⊤) η trivial _).symm
  have hdimXY : rX = rY + n := by
    have h := trdeg_add_eq k (Y.presheaf.stalk (f η)) (A := X.presheaf.stalk η)
    rw [hYtr, hntr, hXtr] at h
    exact_mod_cast h.symm
  refine ⟨n, by rw [hXdim, hYdim, hdimXY]; push_cast; rfl, ?_⟩
  -- Step 3 (II Ex. 5.7): `Ω_{X/Y}` is free near the generic point
  have hFc := Scheme.relativeDifferentials_isCoherent_of_locallyOfFiniteType f
  obtain ⟨W₀, hηW₀, I, ⟨α⟩⟩ := exists_isFree_restrict_of_free_stalk_of_isLocallyNoetherian
    (Scheme.relativeDifferentials f) hFc η inferInstance
  -- the fibre of `Ω_{X/Y}` at the generic point is `Ω_{K(X)/K(Y)}`, of dimension `n`
  have hfibη : (Cardinal.mk I).toNat = n := by
    have h := congrArg Cardinal.toNat
      (rank_fibre_of_restrict_iso_free (Scheme.relativeDifferentials f) α hηW₀)
    rw [← h]
    change finrank _ _ = _
    rw [SmoothTangent.finrank_fibre_relativeDifferentials_eq_stalk, Module.finrank_baseChange]
  -- the open set on which we restrict `f`
  set W : X.Opens := UX ⊓ f ⁻¹ᵁ UY ⊓ W₀
  have hηW : η ∈ W := ⟨⟨hηUX, hηUY⟩, hηW₀⟩
  have hWle : W ≤ f ⁻¹ᵁ UY := fun x hx ↦ hx.1.2
  have hWW₀ : W ≤ W₀ := fun x hx ↦ hx.2
  have : Nonempty W := ⟨⟨η, hηW⟩⟩
  have : Nonempty UY := ⟨⟨f η, hηUY⟩⟩
  refine ⟨W, ⟨η, hηW⟩, ?_⟩
  let g : W.toScheme ⟶ UY.toScheme := f.resLE UY W hWle
  have hg : g ≫ UY.ι = W.ι ≫ f := f.resLE_comp_ι hWle
  have : LocallyOfFiniteType (g ≫ UY.ι) := by rw [hg]; infer_instance
  have : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g UY.ι
  -- `Ω_{W/UY}` is free with basis indexed by `I`
  let j : W.toScheme ⟶ W₀.toScheme := X.homOfLE hWW₀
  let β : Scheme.relativeDifferentials g ≅ SheafOfModules.free I :=
    RelDiffLocal.restrictIso f W.ι g UY.ι hg.symm ≪≫
      (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι hWW₀).symm).app _ ≪≫
      (Scheme.Modules.restrictFunctorComp j W₀.ι).app _ ≪≫
      (Scheme.Modules.restrictFunctor j).mapIso α ≪≫ Scheme.Modules.restrictFreeIso j I
  let β' : (Scheme.relativeDifferentials g).restrict (⊤ : W.toScheme.Opens).ι ≅
      SheafOfModules.free I :=
    (Scheme.Modules.restrictFunctor (⊤ : W.toScheme.Opens).ι).mapIso β ≪≫
      Scheme.Modules.restrictFreeIso _ I
  -- hence `Ω_{W/UY}` is locally free of rank `n`
  have hloc : (Scheme.relativeDifferentials g).IsLocallyFreeOfRank n := by
    rw [Scheme.relativeDifferentials_isLocallyFreeOfRank_iff g n]
    intro w
    rw [← hfibη]
    exact congrArg Cardinal.toNat
      (rank_fibre_of_restrict_iso_free (Scheme.relativeDifferentials g) β' (Set.mem_univ w))
  -- Step 4 (Proposition 10.4): the restriction is smooth of relative dimension `n`
  let X' : Over (Spec (.of k)) := Over.mk (W.ι ≫ f ≫ pY)
  let Y' : Over (Spec (.of k)) := Over.mk (UY.ι ≫ pY)
  let f' : X' ⟶ Y' := Over.homMk g (by simp [X', Y', reassoc_of% hg])
  have : IsIntegral X'.left := inferInstanceAs (IsIntegral W.toScheme)
  have : IsIntegral Y'.left := inferInstanceAs (IsIntegral UY.toScheme)
  have hX' : LocallyOfFiniteType X'.hom ∧ QuasiCompact X'.hom :=
    ⟨inferInstanceAs (LocallyOfFiniteType (W.ι ≫ f ≫ pY)),
      inferInstanceAs (QuasiCompact (W.ι ≫ f ≫ pY))⟩
  have hY' : LocallyOfFiniteType Y'.hom ∧ QuasiCompact Y'.hom :=
    ⟨inferInstanceAs (LocallyOfFiniteType (UY.ι ≫ pY)),
      inferInstanceAs (QuasiCompact (UY.ι ≫ pY))⟩
  have hXr : ∀ x : X'.left, X'.left.IsRegularAt x := fun x ↦ by
    have : IsRegularLocalRing (X.presheaf.stalk x.1) := hUXreg x.1 x.2.1.1
    exact IsRegularLocalRing.of_ringEquiv (W.stalkIso x).commRingCatIsoToRingEquiv.symm
  have hYr : ∀ y : Y'.left, Y'.left.IsRegularAt y := fun y ↦ by
    have : IsRegularLocalRing (Y.presheaf.stalk y.1) := hUYreg y.1 y.2
    exact IsRegularLocalRing.of_ringEquiv (UY.stalkIso y).commRingCatIsoToRingEquiv.symm
  have hdim : topologicalKrullDim X'.left = topologicalKrullDim Y'.left + n := by
    change topologicalKrullDim W = topologicalKrullDim UY + n
    rw [topologicalKrullDim_opens_eq (f ≫ pY) hpX hXdim W,
      topologicalKrullDim_opens_eq pY hY hYdim UY, hdimXY]
    push_cast
    rfl
  have htfae := SmoothTangent.smoothOfRelativeDimension_tfae_of_isRegularAt hX' hY' hXr hYr f' n
    hdim
  have : SmoothOfRelativeDimension n g := (htfae.out 0 1).mpr hloc
  rw [← hg]
  exact smoothOfRelativeDimension_comp n 0 g UY.ι

/-- **Hartshorne III, Lemma 10.5.** Let `f : X ⟶ Y` be a dominant morphism of integral schemes
of finite type over an algebraically closed field `k` of characteristic zero. Then there is a
nonempty open subset `U` of `X` such that the restriction `U ⟶ Y` of `f` is smooth, of some
relative dimension `n`.

The schemes over `k` are given by structure morphisms `pX` and `pY`, and `f` is a morphism over
`k`. The proof follows Hartshorne's: it restricts to nonsingular open subsets, computes the
generic rank of `Ω_{X/Y}` from the separably generated extension `K(X)/K(Y)`, and applies
Proposition 10.4 (see `exists_nonempty_open_smoothOfRelativeDimension_of_isDominant`). -/
theorem exists_nonempty_open_smooth_of_isDominant {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {X Y : Scheme.{u}} (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    (hX : LocallyOfFiniteType pX ∧ QuasiCompact pX)
    (hY : LocallyOfFiniteType pY ∧ QuasiCompact pY)
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) (hf : f ≫ pY = pX) [IsDominant f] :
    ∃ U : X.Opens, (U : Set X).Nonempty ∧ ∃ n : ℕ, SmoothOfRelativeDimension n (U.ι ≫ f) := by
  obtain ⟨n, -, U, hU, h⟩ :=
    exists_nonempty_open_smoothOfRelativeDimension_of_isDominant pX pY hX hY f hf
  exact ⟨U, hU, n, h⟩

end Hartshorne

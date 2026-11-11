/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Dominant morphisms are generically smooth on the source in characteristic zero

Hartshorne, *Algebraic Geometry*, III, Lemma 10.5 (p. 271).

Let `f : X ⟶ Y` be a dominant morphism of integral schemes of finite type over an algebraically
closed field `k` of characteristic zero. Then there is a nonempty open `U` of `X` such that
`U ⟶ Y` is smooth of some relative dimension
(`Hartshorne.exists_nonempty_open_smooth_of_isDominant`).

## Proof

Since `f` is dominant and `X` is irreducible, `f` sends the generic point of `X` to the generic
point of `Y`, so the stalk map of `f` at the generic point of `X` is the extension of function
fields `K(Y) → K(X)`. It is essentially of finite type because `f` is locally of finite type,
and `K(Y)` has characteristic zero because it is a `k`-algebra, so it is perfect. Hence the
extension is formally smooth (separable generation, Mathlib's
`Algebra.FormallySmooth.of_perfectField`), i.e. the generic point of `X` lies in the smooth locus
of `f`. The smooth locus is open, and the restriction of `f` to it is smooth. A standard smooth
chart of this restriction has a relative dimension `n`, and the open of `X` it covers is smooth of
relative dimension `n` over `Y`. The proof does not use that `k` is algebraically closed.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Hartshorne

/-- **Hartshorne III, Lemma 10.5.** Let `f : X ⟶ Y` be a dominant morphism of integral schemes
of finite type over an algebraically closed field `k` of characteristic zero. Then there is a
nonempty open subset `U` of `X` such that the restriction `U ⟶ Y` of `f` is smooth, of some
relative dimension `n`.

The schemes over `k` are given by structure morphisms `pX` and `pY`, and `f` is a morphism over
`k`. Algebraic closedness of `k` is part of Hartshorne's setting but is not used. -/
theorem exists_nonempty_open_smooth_of_isDominant {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {X Y : Scheme.{u}} (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    (hX : LocallyOfFiniteType pX ∧ QuasiCompact pX)
    (hY : LocallyOfFiniteType pY ∧ QuasiCompact pY)
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) (hf : f ≫ pY = pX) [IsDominant f] :
    ∃ U : X.Opens, (U : Set X).Nonempty ∧ ∃ n : ℕ, SmoothOfRelativeDimension n (U.ι ≫ f) := by
  have : LocallyOfFiniteType pX := hX.1
  have : LocallyOfFiniteType pY := hY.1
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian pY
  have : LocallyOfFiniteType (f ≫ pY) := by rw [hf]; infer_instance
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f pY
  have : LocallyOfFinitePresentation f := inferInstance
  -- `f` sends the generic point of `X` to the generic point of `Y`
  have hgen : f (genericPoint X) = genericPoint Y := by
    apply ((genericPoint_spec Y).eq _).symm
    have h := (genericPoint_spec X).image f.continuous
    rwa [Set.image_univ, f.denseRange.closure_range] at h
  -- the generic point of `X` lies in the smooth locus of `f`
  have hmem : genericPoint X ∈ f.smoothLocus := by
    have := LocallyOfFiniteType.stalkMap f (genericPoint X)
    rw [Scheme.Hom.mem_smoothLocus]
    algebraize [(f.stalkMap (genericPoint X)).hom]
    have hfield : IsField (Y.presheaf.stalk (f (genericPoint X))) :=
      hgen ▸ Field.toIsField Y.functionField
    let : Field (Y.presheaf.stalk (f (genericPoint X))) := hfield.toField
    let φ : k →+* Y.presheaf.stalk (f (genericPoint X)) :=
      (Y.presheaf.germ ⊤ _ trivial).hom.comp
        (pY.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
    have : CharZero (Y.presheaf.stalk (f (genericPoint X))) :=
      charZero_of_injective_ringHom φ.injective
    exact Algebra.FormallySmooth.of_perfectField
  -- the restriction of `f` to its smooth locus is smooth
  have hg : Smooth (f.smoothLocus.ι ≫ f) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    ext x
    simp
  -- a standard smooth chart around the generic point has some relative dimension `n`
  obtain ⟨U', hU', V', hV', hxV', e, hst⟩ :=
    Smooth.exists_isStandardSmooth (f.smoothLocus.ι ≫ f) ⟨genericPoint X, hmem⟩
  have hrel : ∃ n : ℕ, ((f.smoothLocus.ι ≫ f).appLE U' V' e).hom.IsStandardSmoothOfRelativeDimension
      n := by
    algebraize [((f.smoothLocus.ι ≫ f).appLE U' V' e).hom]
    obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := hst.toAlgebra.out
    exact ⟨P.dimension, P.isStandardSmoothOfRelativeDimension rfl⟩
  obtain ⟨n, hn⟩ := hrel
  have h₁ : SmoothOfRelativeDimension n ((f.smoothLocus.ι ≫ f).resLE U' V' e) := by
    have : IsAffine U' := hU'
    have : IsAffine V' := hV'
    rw [HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension n)]
    exact ((RingHom.locally_respectsIso
      (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := n))).arrow_mk_iso_iff
        (arrowResLEAppIso _ U' V' e)).mpr
      (RingHom.locally_of (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := n)) _ hn)
  have h₂ : SmoothOfRelativeDimension n (V'.ι ≫ f.smoothLocus.ι ≫ f) := by
    rw [← Scheme.Hom.resLE_comp_ι _ e]
    exact smoothOfRelativeDimension_comp n 0 ((f.smoothLocus.ι ≫ f).resLE U' V' e) U'.ι
  -- transport to the corresponding open of `X`
  let W : X.Opens := (V'.ι ≫ f.smoothLocus.ι).opensRange
  refine ⟨W, ⟨_, Scheme.Hom.mem_opensRange.mpr ⟨⟨_, hxV'⟩, rfl⟩⟩, n, ?_⟩
  have hW : W.ι ≫ f = (V'.ι ≫ f.smoothLocus.ι).isoOpensRange.inv ≫
      (V'.ι ≫ f.smoothLocus.ι ≫ f) := by
    rw [Iso.eq_inv_comp, ← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, Category.assoc]
  rw [hW, ← zero_add n]
  infer_instance

end Hartshorne

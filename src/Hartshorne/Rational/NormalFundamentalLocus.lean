/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Rational.SchemeMaximalDomain
import Hartshorne.Scheme.Normal
import Hartshorne.Scheme.Codimension
import Hartshorne.Scheme.ProjectiveSpaceProper
import Hartshorne.Curve.DVR
import Mathlib.AlgebraicGeometry.Birational.Birational
import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-!
# The fundamental locus on a normal source

Hartshorne, *Algebraic Geometry*, V.5, Lemma 5.1, p. 410.

Let `T : X ⤏ Y` be a birational transformation of projective varieties over a
field `k`, with `X` normal. Then the fundamental locus `X \ Dom(T)` is closed
and has codimension at least two; for a normal surface it is a finite set of
closed points.

Varieties are encoded as integral schemes over `Spec k`, projectivity as
`Hartshorne.Projective` of the structure morphism, and a birational
transformation as a rational map `T : X ⤏ Y` represented by a partial
isomorphism over `Spec k`. `Dom(T)` and the fundamental locus are those of
`Hartshorne.SchemeRationalMap`. The field is arbitrary.

## Proof

Let `x` be a point of codimension one, i.e. of coheight one. Since `X` is
normal and Noetherian, `𝒪_{X,x}` is a one-dimensional Noetherian integrally
closed local domain, hence a discrete valuation ring with fraction field
`K(X)`. The rational map gives a `k`-morphism `Spec K(X) ⟶ Y`; properness of
`Y` (valuative criterion, existence part) extends it to `Spec 𝒪_{X,x} ⟶ Y`,
and Mathlib's spreading out (`Y` is of finite type) turns this into a partial
map defined at `x`. It has the same restriction to `Spec K(X)` as `T`, so it
represents `T`, and `x ∈ Dom(T)`. The generic point lies in `Dom(T)` because
`Dom(T)` is a nonempty open set. Hence every point of the fundamental locus has
coheight at least two, which is the codimension statement. If `X` has dimension
two, a point of coheight two admits no proper specialization, so it is closed;
a closed subset of a Noetherian space all of whose points are closed is a
finite union of irreducible closed sets, each a single point, hence finite.

The mathematical content holds for any rational map `T : X ⤏ Y` over a base
`S`, with `X` integral, (locally) Noetherian and normal and `Y` proper over
`S`; this general form is stated first.

## Main results

* `Hartshorne.SchemeRationalMap.mem_dom_of_coheight_eq_one`: codimension-one
  points lie in `Dom(T)`.
* `Hartshorne.SchemeRationalMap.two_le_codim_fundamentalLocus`,
  `Hartshorne.SchemeRationalMap.fundamentalLocus_finite_of_topologicalKrullDim_eq_two`:
  the general form.
* `Hartshorne.SchemeRationalMap.normal_projective_fundamentalLocus_codim_two`,
  `Hartshorne.SchemeRationalMap.normal_projective_surface_fundamentalLocus_finite`:
  Lemma V.5.1 for birational transformations of projective varieties.
-/

namespace Hartshorne

namespace SchemeRationalMap

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

/-- The canonical maps `Spec 𝒪_{X,x} ⟶ U` are compatible with specialization. -/
theorem specMap_stalkSpecializes_fromSpecStalkOfMem {X : Scheme.{u}} (U : X.Opens) {x y : X}
    (h : x ⤳ y) (hx : x ∈ U) (hy : y ∈ U) :
    Spec.map (X.presheaf.stalkSpecializes h) ≫ U.fromSpecStalkOfMem y hy =
      U.fromSpecStalkOfMem x hx := by
  rw [← cancel_mono U.ι]
  simp

/-- The restrictions of a partial map to the local schemes of its domain are
compatible with specialization. -/
theorem specMap_stalkSpecializes_partialMap_fromSpecStalkOfMem {X Y : Scheme.{u}}
    (f : X.PartialMap Y) {x y : X} (h : x ⤳ y) (hx : x ∈ f.domain) (hy : y ∈ f.domain) :
    Spec.map (X.presheaf.stalkSpecializes h) ≫ f.fromSpecStalkOfMem hy =
      f.fromSpecStalkOfMem hx := by
  simp only [Scheme.PartialMap.fromSpecStalkOfMem]
  rw [← Category.assoc, specMap_stalkSpecializes_fromSpecStalkOfMem]

variable {S X Y : Scheme.{u}} [X.Over S] [Y.Over S]

/-- **Hartshorne V.5, Lemma 5.1, key step.** For `X` integral, locally
Noetherian and normal, `Y` proper over `S`, and `T : X ⤏ Y` a rational map over
`S`, every point of codimension one of `X` lies in `Dom(T)`. -/
theorem mem_dom_of_coheight_eq_one [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsProper (Y ↘ S)] (T : X ⤏ Y) [T.IsOver S] {x : X} (hx : Order.coheight x = 1) :
    x ∈ dom T := by
  have hdim : ringKrullDim (X.presheaf.stalk x) = 1 := by
    rw [ringKrullDim_stalk_eq_coheight, hx]; rfl
  have : IsDiscreteValuationRing (X.presheaf.stalk x) :=
    ((Hartshorne.dvr_characterizations (X.presheaf.stalk x) hdim).out 0 1).mpr
      (IsNormal.isIntegrallyClosed_stalk x)
  have hex : ValuativeCriterion.Existence (Y ↘ S) := by
    have h := (IsProper.eq_valuativeCriterion ▸ (inferInstance : IsProper (Y ↘ S)) :)
    exact h.1.1.1.existence
  have hT : T.compHom (Y ↘ S) = (X ↘ S).toRationalMap := Scheme.RationalMap.isOver_iff.mp ‹_›
  have hφ : T.fromFunctionField ≫ (Y ↘ S) = X.fromSpecStalk _ ≫ (X ↘ S) :=
    ((Scheme.RationalMap.equivFunctionField (X ↘ S) (Y ↘ S)).symm ⟨T, hT⟩).2
  have hsq : T.fromFunctionField ≫ (Y ↘ S) =
      Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)) ≫
        X.fromSpecStalk x ≫ (X ↘ S) := by
    rw [hφ, ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc
      ((genericPoint_spec X).specializes trivial)]
    rfl
  have hval : ValuationRing (X.presheaf.stalk x) := inferInstance
  let sq : ValuativeCommSq (Y ↘ S) :=
    { R := X.presheaf.stalk x
      domain := inferInstanceAs (IsDomain (X.presheaf.stalk x))
      valuationRing := hval
      K := X.functionField
      i₁ := T.fromFunctionField
      i₂ := X.fromSpecStalk x ≫ (X ↘ S)
      commSq := ⟨hsq⟩ }
  obtain ⟨⟨l, hl₁, hl₂⟩⟩ := hex sq
  have hl₂' : (l : Spec (X.presheaf.stalk x) ⟶ Y) ≫ (Y ↘ S) = X.fromSpecStalk x ≫ (X ↘ S) := hl₂
  let g := Scheme.PartialMap.ofFromSpecStalk (X ↘ S) (Y ↘ S) l hl₂'
  have hxg : x ∈ g.domain := Scheme.PartialMap.mem_domain_ofFromSpecStalk _ _ _ _
  have hg : g.toRationalMap = T := by
    apply Scheme.RationalMap.eq_of_fromFunctionField_eq
    rw [Scheme.RationalMap.fromFunctionField_toRationalMap, Scheme.PartialMap.fromFunctionField,
      ← specMap_stalkSpecializes_partialMap_fromSpecStalkOfMem g
        ((genericPoint_spec X).specializes trivial) _ hxg,
      Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk]
    exact hl₁
  exact le_dom g hg hxg

/-- Every point of the fundamental locus has coheight (codimension) at least two. -/
theorem two_le_coheight_of_mem_fundamentalLocus [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsProper (Y ↘ S)] (T : X ⤏ Y) [T.IsOver S] {z : X}
    (hz : z ∈ fundamentalLocus T) : 2 ≤ Order.coheight z := by
  have hz' : z ∉ dom T := hz
  have h1 : Order.coheight z ≠ 1 := fun h => hz' (mem_dom_of_coheight_eq_one (S := S) T h)
  have h0 : Order.coheight z ≠ 0 := by
    intro h
    have hmax : IsMax z := Order.coheight_eq_zero.mp h
    have hηz : z ≤ genericPoint X := genericPoint_specializes z
    have hzη : z ⤳ genericPoint X := hmax hηz
    have hη : genericPoint X ∈ dom T :=
      ((genericPoint_spec X).mem_open_set_iff (dom T).isOpen).mpr
        (by simpa using (dense_dom T).nonempty)
    exact hz' (hzη.mem_open (dom T).isOpen hη)
  generalize Order.coheight z = c at h0 h1 ⊢
  induction c using ENat.recTopCoe with
  | top => exact le_top
  | coe n =>
    norm_cast at h0 h1 ⊢
    omega

/-- **Hartshorne V.5, Lemma 5.1, general form.** For `X` integral, locally
Noetherian and normal, `Y` proper over `S`, and `T : X ⤏ Y` a rational map over
`S`, the fundamental locus has codimension at least two. -/
theorem two_le_codim_fundamentalLocus [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsProper (Y ↘ S)] (T : X ⤏ Y) [T.IsOver S] :
    2 ≤ codim (fundamentalLocus T : Set X) := by
  refine le_iInf₂ fun Z hZ => ?_
  let e : IrreducibleCloseds X ≃o X := irreducibleSetEquivPoints
  rw [← Order.coheight_orderIso e]
  refine two_le_coheight_of_mem_fundamentalLocus (S := S) T (hZ ?_)
  exact (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).mem

/-- **Hartshorne V.5, Lemma 5.1, surface clause, general form.** If moreover `X`
is Noetherian of dimension two, the fundamental locus is a finite set of closed
points. -/
theorem fundamentalLocus_finite_of_topologicalKrullDim_eq_two [IsIntegral X] [IsNoetherian X]
    [IsNormal X] [IsProper (Y ↘ S)] (T : X ⤏ Y) [T.IsOver S]
    (hdim : topologicalKrullDim X = 2) :
    (fundamentalLocus T : Set X).Finite ∧
      ∀ x ∈ fundamentalLocus T, IsClosed ({x} : Set X) := by
  have hclosed : ∀ x ∈ fundamentalLocus T, IsClosed ({x} : Set X) := by
    intro x hx
    have h2 := two_le_coheight_of_mem_fundamentalLocus (S := S) T hx
    refine closure_subset_iff_isClosed.mp fun y hy => ?_
    have hxy : x ⤳ y := specializes_iff_mem_closure.mpr hy
    by_contra hne
    have hlt : y < x := lt_of_le_not_ge hxy fun h => hne (hxy.antisymm h).eq.symm
    have h3 := Order.coheight_add_one_le hlt
    have hkd : (Order.coheight y : WithBot ℕ∞) ≤ 2 := by
      let e : IrreducibleCloseds X ≃o X := irreducibleSetEquivPoints
      rw [← hdim, topologicalKrullDim, Order.krullDim_eq_of_orderIso e]
      exact Order.coheight_le_krullDim y
    have hy2 : Order.coheight y ≤ 2 :=
      WithBot.coe_le_coe.mp (hkd.trans_eq rfl : _ ≤ ((2 : ℕ∞) : WithBot ℕ∞))
    have : (2 : ℕ∞) + 1 ≤ 2 := le_trans (by gcongr) (h3.trans hy2)
    exact absurd this (by decide)
  refine ⟨?_, hclosed⟩
  obtain ⟨Ss, hSf, hSc, hSi, hSU⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible (fundamentalLocus T).isClosed
  rw [hSU]
  refine hSf.sUnion fun t ht => ?_
  have hg := (hSi t ht).isGenericPoint_genericPoint (hSc t ht)
  have hgF : (hSi t ht).genericPoint ∈ fundamentalLocus T := by
    have : t ⊆ (fundamentalLocus T : Set X) := hSU ▸ Set.subset_sUnion_of_mem ht
    exact this hg.mem
  rw [← hg.def, (hclosed _ hgF).closure_eq]
  exact Set.finite_singleton _

variable {k : Type u} [Field k] {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]

/-- A partial isomorphism over `S` gives a rational map over `S`. -/
theorem isOver_of_partialIso_isOver {S : Scheme.{u}} [X.Over S] [Y.Over S] {T : X ⤏ Y}
    (hT : ∃ f : X.PartialIso Y, f.IsOver (X ↘ S) (Y ↘ S) ∧ f.toRationalMap = T) :
    T.IsOver S := by
  obtain ⟨f, hf, rfl⟩ := hT
  have : f.toPartialMap.IsOver S := ⟨hf⟩
  infer_instance

/-- **Hartshorne V.5, Lemma 5.1.** Let `T : X ⤏ Y` be a birational transformation
of projective varieties over `k`, with `X` normal. Then the fundamental locus of
`T` is closed and has codimension at least two. -/
theorem normal_projective_fundamentalLocus_codim_two [IsIntegral X] [IsIntegral Y] [IsNormal X]
    (hX : Projective (X ↘ Spec (.of k))) (hY : Projective (Y ↘ Spec (.of k))) (T : X ⤏ Y)
    (hT : ∃ f : X.PartialIso Y,
      f.IsOver (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) ∧ f.toRationalMap = T) :
    IsClosed (fundamentalLocus T : Set X) ∧ 2 ≤ codim (fundamentalLocus T : Set X) := by
  have := isOver_of_partialIso_isOver hT
  have := hX.isProper
  have := hY.isProper
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  exact ⟨(fundamentalLocus T).isClosed, two_le_codim_fundamentalLocus (S := Spec (.of k)) T⟩

/-- **Hartshorne V.5, Lemma 5.1, surface clause.** For a birational transformation
`T : X ⤏ Y` of projective varieties over `k` with `X` a normal surface, the
fundamental locus is a finite set of closed points. -/
theorem normal_projective_surface_fundamentalLocus_finite [IsIntegral X] [IsIntegral Y]
    [IsNormal X] (hX : Projective (X ↘ Spec (.of k))) (hY : Projective (Y ↘ Spec (.of k)))
    (hdim : topologicalKrullDim X = 2) (T : X ⤏ Y)
    (hT : ∃ f : X.PartialIso Y,
      f.IsOver (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) ∧ f.toRationalMap = T) :
    (fundamentalLocus T : Set X).Finite ∧
      ∀ x ∈ fundamentalLocus T, IsClosed ({x} : Set X) := by
  have := isOver_of_partialIso_isOver hT
  have := hX.isProper
  have := hY.isProper
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := {}
  exact fundamentalLocus_finite_of_topologicalKrullDim_eq_two (S := Spec (.of k)) T hdim

end SchemeRationalMap

end Hartshorne

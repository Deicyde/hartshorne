/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.GenericCompletionSheaf
import Hartshorne.Morphism.AffineVariety
import Hartshorne.Morphism.CoordinateRingIso
import Hartshorne.Topology.Subspace
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.RingTheory.Jacobson.Ring

/-!
# An affine variety completes to its spectrum

Hartshorne, *Algebraic Geometry*, II.2, the affine case of Proposition 2.6
(p. 78).

For an affine variety `Y ⊆ 𝔸ⁿ` over an algebraically closed field `k`, with
coordinate ring `A(Y)`, the ringed space `(t(Y), α_* 𝒪_Y)` built from the
generic completion is canonically isomorphic to `Spec A(Y)` as a locally ringed
space.

## Construction

* **Points.** An irreducible closed subset `Z ⊆ Y` goes to its ideal
  `I(Z) ⊆ A(Y)`; the inverse sends a prime to its zero set. That these are
  inverse uses the Nullstellensatz in the form "`A(Y)` is a Jacobson ring whose
  maximal ideals are the `𝔪_P`". Closed sets `{Z | Z ⊆ C}` of `t(Y)` correspond
  to the closed sets `V(I(C))` of `Spec A(Y)`, so the bijection is a
  homeomorphism, and a classical point `P` goes to `𝔪_P`.
* **Sections.** Over an open `W ⊆ Spec A(Y)`, a section of the structure sheaf
  is sent to the function on the corresponding open of `Y` whose value at `P`
  is its germ in `A(Y)_{𝔪_P}` evaluated at `P`. Locally the section is `a / f`,
  so the function is locally `a(P) / f(P)` and is regular. Injectivity and
  surjectivity both come from the identity principle in `A(Y)`: an element
  vanishing on a nonempty open subset of the irreducible `Y` is zero. For
  surjectivity, a regular function is written as `a / f` near a classical point
  of the zero set of each prime, and these local quotients agree in every
  localization.

The isomorphism of sheafed spaces then makes the stalks of `(t(Y), α_* 𝒪_Y)`
local, so it is a locally ringed space, and the isomorphism lifts.

## Main definitions and results

* `Hartshorne.genericCompletionHomeomorphSpec`: the homeomorphism
  `t(Y) ≃ₜ Spec A(Y)`, `Z ↦ I(Z)`.
* `Hartshorne.specToRegular`: evaluation of structure-sheaf sections at
  classical points, a ring isomorphism onto regular functions.
* `Hartshorne.affineVarietyGenericCompletionSheafedSpaceIsoSpec`: the
  isomorphism of sheafed spaces `(t(Y), α_* 𝒪_Y) ≅ Spec A(Y)`.
* `Hartshorne.affineVarietyGenericCompletionLocallyRingedSpace`: the locally
  ringed space `(t(Y), α_* 𝒪_Y)`.
* `Hartshorne.affineVarietyGenericCompletionIsoSpec`: the canonical isomorphism
  of locally ringed spaces, with its description on points
  (`Hartshorne.affineVarietyGenericCompletionIsoSpec_hom_base_asIdeal`,
  `Hartshorne.affineVarietyGenericCompletionIsoSpec_hom_base_alpha`) and on
  sections (`Hartshorne.affineVarietyGenericCompletionIsoSpec_hom_c_app`).
-/

noncomputable section

open CategoryTheory Opposite TopologicalSpace MvPolynomial
open scoped AlgebraicGeometry

namespace Hartshorne

universe u

variable {k : Type u} [Field k] {σ : Type u} {Y : Set (σ → k)}

/-! ### Ideals of subsets and zero sets of ideals inside `Y` -/

/-- The ideal of `A(Y)` of functions vanishing on a subset `C` of `Y`. -/
def coordIdealOf (C : Set Y) : Ideal (coordinateRing Y) :=
  ⨅ x ∈ C, maximalIdealAt Y x

theorem mem_coordIdealOf {C : Set Y} {a : coordinateRing Y} :
    a ∈ coordIdealOf C ↔ ∀ x ∈ C, evalAt Y x a = 0 := by
  simp [coordIdealOf, Submodule.mem_iInf, mem_maximalIdealAt]

/-- The points of `Y` at which every element of `S ⊆ A(Y)` vanishes. -/
def coordZeroSet (S : Set (coordinateRing Y)) : Set Y :=
  {x | ∀ a ∈ S, evalAt Y x a = 0}

theorem mem_coordZeroSet {S : Set (coordinateRing Y)} {x : Y} :
    x ∈ coordZeroSet S ↔ ∀ a ∈ S, evalAt Y x a = 0 :=
  Iff.rfl

theorem coordZeroSet_eq_preimage (S : Set (coordinateRing Y)) :
    coordZeroSet S =
      Subtype.val ⁻¹' zeroSet (Ideal.Quotient.mk (vanishingIdeal k Y) ⁻¹' S) := by
  ext x
  simp only [mem_coordZeroSet, Set.mem_preimage, mem_zeroSet_iff]
  constructor
  · intro h p hp
    simpa using h _ hp
  · intro h a ha
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    simpa using h p ha

theorem isClosed_coordZeroSet (S : Set (coordinateRing Y)) : IsClosed (coordZeroSet S) := by
  rw [coordZeroSet_eq_preimage]
  exact (isClosed_zeroSet _).preimage continuous_subtype_val

theorem coordZeroSet_anti {S T : Set (coordinateRing Y)} (h : S ⊆ T) :
    coordZeroSet T ⊆ coordZeroSet S :=
  fun _ hx a ha => hx a (h ha)

theorem coordIdealOf_anti {C D : Set Y} (h : C ⊆ D) : coordIdealOf D ≤ coordIdealOf C :=
  fun _ ha => mem_coordIdealOf.2 fun x hx => mem_coordIdealOf.1 ha x (h hx)

theorem subset_coordZeroSet_iff {C : Set Y} {S : Set (coordinateRing Y)} :
    C ⊆ coordZeroSet S ↔ S ⊆ coordIdealOf C := by
  constructor
  · intro h a ha
    exact mem_coordIdealOf.2 fun x hx => h hx a ha
  · intro h x hx a ha
    exact mem_coordIdealOf.1 (h ha) x hx

theorem coordIdealOf_closure (C : Set Y) : coordIdealOf (closure C) = coordIdealOf C := by
  refine le_antisymm (coordIdealOf_anti subset_closure) fun a ha => ?_
  have hC : C ⊆ coordZeroSet {a} := subset_coordZeroSet_iff.2 (by simpa using ha)
  have := (isClosed_coordZeroSet {a}).closure_subset_iff.2 hC
  exact (subset_coordZeroSet_iff.1 this) rfl

theorem coordIdealOf_singleton (x : Y) : coordIdealOf {x} = maximalIdealAt Y x := by
  ext a
  simp [mem_coordIdealOf, mem_maximalIdealAt]

/-- For a closed `C` in an algebraic set `Y`, the zero set of the ideal of `C`
is `C` again. -/
theorem coordZeroSet_coordIdealOf (hY : IsClosed Y) {C : Set Y} (hC : IsClosed C) :
    coordZeroSet (coordIdealOf C : Set (coordinateRing Y)) = C := by
  refine Set.Subset.antisymm (fun x hx => ?_) (subset_coordZeroSet_iff.2 le_rfl)
  have halg : IsAlgebraicSet (Subtype.val '' C) :=
    isClosed_iff_isAlgebraicSet.1 (isClosed_image_val hY hC)
  have hx' : (x : σ → k) ∈ zeroLocus k (vanishingIdeal k (Subtype.val '' C)) := by
    intro p hp
    have hmem : Ideal.Quotient.mk (vanishingIdeal k Y) p ∈ coordIdealOf C := by
      refine mem_coordIdealOf.2 fun c hc => ?_
      simpa using hp c ⟨c, hc, rfl⟩
    simpa using hx _ hmem
  rw [halg.zeroLocus_vanishingIdeal] at hx'
  obtain ⟨c, hc, hcx⟩ := hx'
  rwa [Subtype.val_injective hcx] at hc

/-- Zero sets in `Y` of primes, read in the ambient space. -/
theorem coordZeroSet_eq_preimage_zeroLocus (I : Ideal (coordinateRing Y)) :
    coordZeroSet (I : Set (coordinateRing Y)) =
      Subtype.val ⁻¹' zeroLocus k (Ideal.comap (Ideal.Quotient.mk (vanishingIdeal k Y)) I) := by
  rw [coordZeroSet_eq_preimage, zeroLocus_eq_zeroSet]
  rfl

theorem isPrime_coordIdealOf {Z : Set Y} (hZ : IsIrreducible Z) :
    (coordIdealOf Z).IsPrime := by
  rw [Ideal.isPrime_iff]
  refine ⟨fun h => ?_, fun {a b} hab => ?_⟩
  · obtain ⟨x, hx⟩ := hZ.nonempty
    have := mem_coordIdealOf.1 (h ▸ Submodule.mem_top : (1 : coordinateRing Y) ∈ coordIdealOf Z)
      x hx
    simp at this
  · have hcov : Z ⊆ coordZeroSet {a} ∪ coordZeroSet {b} := by
      intro x hx
      have := mem_coordIdealOf.1 hab x hx
      rw [map_mul, mul_eq_zero] at this
      rcases this with h | h
      · exact Or.inl (by simpa [mem_coordZeroSet] using h)
      · exact Or.inr (by simpa [mem_coordZeroSet] using h)
    rcases isPreirreducible_iff_isClosed_union_isClosed.1 hZ.2 _ _ (isClosed_coordZeroSet _)
      (isClosed_coordZeroSet _) hcov with h | h
    · exact Or.inl ((subset_coordZeroSet_iff.1 h) rfl)
    · exact Or.inr ((subset_coordZeroSet_iff.1 h) rfl)

/-- The zero set of `𝔪_P` is the single point `P`. -/
theorem coordZeroSet_maximalIdealAt (x : Y) :
    coordZeroSet (maximalIdealAt Y x : Set (coordinateRing Y)) = {x} := by
  refine Set.Subset.antisymm (fun y hy => ?_) ?_
  · have hle : maximalIdealAt Y x ≤ maximalIdealAt Y y := fun a ha => hy a ha
    exact maximalIdealAt_injective
      (((maximalIdealAt_isMaximal x).eq_of_le (maximalIdealAt_isMaximal y).ne_top hle).symm)
  · rw [Set.singleton_subset_iff]
    exact fun a ha => ha

/-! ### Evaluating germs of the structure sheaf at classical points -/

/-- Evaluation at a classical point `P` of an element of the localization of
`A(Y)` at a prime `q` contained in `𝔪_P` (so `q = 𝔪_P`): `a / s ↦ a(P) / s(P)`. -/
def localizationEval (x : Y) (q : PrimeSpectrum (coordinateRing Y))
    (hq : maximalIdealAt Y x ≤ q.asIdeal) :
    LocalizedModule q.asIdeal.primeCompl (coordinateRing Y) →+* k :=
  IsLocalization.lift (M := q.asIdeal.primeCompl) (g := (evalAt Y x).toRingHom) fun s =>
    isUnit_iff_ne_zero.2 fun h => s.2 (hq h)

theorem localizationEval_mk (x : Y) (q : PrimeSpectrum (coordinateRing Y))
    (hq : maximalIdealAt Y x ≤ q.asIdeal) (a : coordinateRing Y) (s : q.asIdeal.primeCompl) :
    localizationEval x q hq (LocalizedModule.mk a s) = evalAt Y x a / evalAt Y x s := by
  have hs : evalAt Y x s ≠ 0 := fun h => s.2 (hq h)
  change localizationEval x q hq (Localization.mk a s) = _
  rw [Localization.mk_eq_mk', localizationEval, IsLocalization.lift_mk'_spec]
  change evalAt Y x a = evalAt Y x s * (evalAt Y x a / evalAt Y x s)
  field_simp

/-- **Identity principle in `A(Y)`.** An element of `A(Y)` vanishing on a
nonempty open subset of an irreducible `Y` is zero. -/
theorem eq_zero_of_evalAt_eq_zero_of_isOpen (hY : IsIrreducible Y) {a : coordinateRing Y}
    {U : Set Y} (hU : IsOpen U) (hne : U.Nonempty) (h : ∀ x ∈ U, evalAt Y x a = 0) :
    a = 0 := by
  have : PreirreducibleSpace Y := isPreirreducible_iff_preirreducibleSpace.1 hY.2
  have hsub : U ⊆ coordZeroSet {a} := fun x hx b hb => by
    rw [Set.mem_singleton_iff.1 hb]
    exact h x hx
  have hcl := (isClosed_coordZeroSet {a}).closure_subset_iff.2 hsub
  rw [(hU.dense hne).closure_eq] at hcl
  apply coordinateToRegular_injective
  funext x
  rw [coordinateToRegular_apply, map_zero]
  exact hcl (Set.mem_univ x) a rfl

section AlgClosed

variable [IsAlgClosed k] [Finite σ]

/-- The zero set in `Y` of a prime of `A(Y)` is irreducible. -/
theorem isIrreducible_coordZeroSet (hY : IsAlgebraicSet Y) {p : Ideal (coordinateRing Y)}
    (hp : p.IsPrime) : IsIrreducible (coordZeroSet (p : Set (coordinateRing Y))) := by
  rw [coordZeroSet_eq_preimage_zeroLocus]
  have hP : (Ideal.comap (Ideal.Quotient.mk (vanishingIdeal k Y)) p).IsPrime :=
    Ideal.comap_isPrime _ _
  have halg : IsAlgebraicSet
      (zeroLocus k (Ideal.comap (Ideal.Quotient.mk (vanishingIdeal k Y)) p)) :=
    isAlgebraicSet_iff_exists_ideal.2 ⟨_, rfl⟩
  refine isIrreducible_preimage_val (isClosed_iff_isAlgebraicSet.2 hY)
    ((isIrreducible_iff_isPrime halg).2
      (by rwa [vanishingIdeal_zeroLocus_of_isRadical hP.isRadical])) ?_
  refine (zeroLocus_anti_mono ?_).trans_eq hY.zeroLocus_vanishingIdeal
  intro x hx
  rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hx]
  exact Ideal.zero_mem _

/-- **Nullstellensatz in `A(Y)`.** A prime of `A(Y)` is the ideal of its zero
set: `A(Y)` is a Jacobson ring and its maximal ideals are the `𝔪_P`. -/
theorem coordIdealOf_coordZeroSet (hY : IsAlgebraicSet Y) {p : Ideal (coordinateRing Y)}
    (hp : p.IsPrime) : coordIdealOf (coordZeroSet (p : Set (coordinateRing Y))) = p := by
  refine le_antisymm (fun a ha => ?_) (subset_coordZeroSet_iff.1 le_rfl)
  rw [← IsJacobsonRing.out' p hp.isRadical, Ideal.jacobson, Submodule.mem_sInf]
  rintro m ⟨hpm, hm⟩
  obtain ⟨x, rfl⟩ := maximalIdealAt_surjective hY hm
  exact mem_coordIdealOf.1 ha x fun b hb => hpm hb

/-- **Points.** The irreducible closed subsets of an algebraic set `Y`
correspond to the primes of `A(Y)`: send `Z` to its ideal `I(Z)`, with inverse
the zero set. -/
def irreducibleClosedsEquivPrimeSpectrum (hY : IsAlgebraicSet Y) :
    IrreducibleCloseds Y ≃ PrimeSpectrum (coordinateRing Y) where
  toFun Z := ⟨coordIdealOf (Z : Set Y), isPrime_coordIdealOf Z.isIrreducible⟩
  invFun p := ⟨coordZeroSet (p.asIdeal : Set (coordinateRing Y)),
    isIrreducible_coordZeroSet hY p.isPrime, isClosed_coordZeroSet _⟩
  left_inv Z := IrreducibleCloseds.ext
    (coordZeroSet_coordIdealOf (isClosed_iff_isAlgebraicSet.2 hY) Z.isClosed)
  right_inv p := PrimeSpectrum.ext (coordIdealOf_coordZeroSet hY p.isPrime)

@[simp]
theorem irreducibleClosedsEquivPrimeSpectrum_apply_asIdeal (hY : IsAlgebraicSet Y)
    (Z : IrreducibleCloseds Y) :
    (irreducibleClosedsEquivPrimeSpectrum hY Z).asIdeal = coordIdealOf (Z : Set Y) :=
  rfl

@[simp]
theorem coe_irreducibleClosedsEquivPrimeSpectrum_symm (hY : IsAlgebraicSet Y)
    (p : PrimeSpectrum (coordinateRing Y)) :
    (((irreducibleClosedsEquivPrimeSpectrum hY).symm p : IrreducibleCloseds Y) : Set Y) =
      coordZeroSet (p.asIdeal : Set (coordinateRing Y)) :=
  rfl

/-- **Points, with topology.** The generic completion `t(Y)` is homeomorphic to
`Spec A(Y)`, an irreducible closed subset going to its ideal. -/
def genericCompletionHomeomorphSpec (hY : IsAlgebraicSet Y) :
    genericCompletionObj (TopCat.of Y) ≃ₜ PrimeSpectrum (coordinateRing Y) where
  toEquiv := irreducibleClosedsEquivPrimeSpectrum hY
  continuous_toFun := by
    rw [continuous_iff_isClosed]
    intro C hC
    obtain ⟨S, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus C).1 hC
    refine (genericCompletion_isClosed_iff (TopCat.of Y) _).2
      ⟨coordZeroSet S, isClosed_coordZeroSet S, ?_⟩
    ext (Z : IrreducibleCloseds Y)
    change S ⊆ coordIdealOf (Z : Set Y) ↔ (Z : Set Y) ⊆ coordZeroSet S
    exact subset_coordZeroSet_iff.symm
  continuous_invFun := by
    rw [continuous_iff_isClosed]
    intro C hC
    obtain ⟨D, hD, rfl⟩ := (genericCompletion_isClosed_iff _ C).1 hC
    rw [PrimeSpectrum.isClosed_iff_zeroLocus]
    refine ⟨coordIdealOf D, ?_⟩
    ext p
    change coordZeroSet (p.asIdeal : Set (coordinateRing Y)) ⊆ D ↔
      (coordIdealOf D : Set (coordinateRing Y)) ⊆ p.asIdeal
    constructor
    · intro h
      have := coordIdealOf_anti h
      rwa [coordIdealOf_coordZeroSet hY p.isPrime] at this
    · intro h
      have := coordZeroSet_anti h
      rwa [coordZeroSet_coordIdealOf (isClosed_iff_isAlgebraicSet.2 hY) hD] at this

/-- On the classical points the homeomorphism is `P ↦ 𝔪_P`. -/
theorem genericCompletionHomeomorphSpec_alpha (hY : IsAlgebraicSet Y) (x : Y) :
    (genericCompletionHomeomorphSpec hY (genericCompletionAlpha (TopCat.of Y) x)).asIdeal =
      maximalIdealAt Y x := by
  change coordIdealOf (closure {x}) = _
  rw [coordIdealOf_closure, coordIdealOf_singleton]

/-! ### The affine variety, its generic completion, and `Spec A(Y)` -/

variable (hY : IsAffineVariety Y)

/-- The homeomorphism `t(Y) ≅ Spec A(Y)` as an isomorphism in `TopCat`. -/
def genericCompletionIsoSpecTop :
    genericCompletionObj (TopCat.of (Variety.ofQuasiAffine hY.isQuasiAffineVariety).carrier) ≅
      AlgebraicGeometry.PrimeSpectrum.Top (coordinateRing Y) :=
  TopCat.isoOfHomeo (genericCompletionHomeomorphSpec hY.isAlgebraicSet)

/-- The point of `Spec A(Y)` attached to a classical point. -/
abbrev specPoint (x : Y) : PrimeSpectrum (coordinateRing Y) :=
  genericCompletionHomeomorphSpec hY.isAlgebraicSet (genericCompletionAlpha (TopCat.of Y) x)

theorem specPoint_asIdeal (x : Y) : (specPoint hY x).asIdeal = maximalIdealAt Y x :=
  genericCompletionHomeomorphSpec_alpha hY.isAlgebraicSet x

theorem continuous_specPoint : Continuous (specPoint hY) :=
  (genericCompletionHomeomorphSpec hY.isAlgebraicSet).continuous.comp
    (genericCompletionAlpha (TopCat.of Y)).hom.continuous

/-- The open subset of `Y` corresponding to an open subset `W` of `Spec A(Y)`:
the classical points whose maximal ideal lies in `W`. -/
def specOpenToVariety (W : Opens (AlgebraicGeometry.PrimeSpectrum.Top (coordinateRing Y))) :
    Opens (Variety.ofQuasiAffine hY.isQuasiAffineVariety).carrier :=
  (genericCompletionOpensOrderIso (TopCat.of _)).symm
    ((Opens.map (genericCompletionIsoSpecTop hY).hom).obj W)

theorem mem_specOpenToVariety
    {W : Opens (AlgebraicGeometry.PrimeSpectrum.Top (coordinateRing Y))} {x : Y} :
    x ∈ specOpenToVariety hY W ↔ specPoint hY x ∈ W :=
  Iff.rfl

theorem specOpenToVariety_mono
    {W W' : Opens (AlgebraicGeometry.PrimeSpectrum.Top (coordinateRing Y))} (h : W' ≤ W) :
    specOpenToVariety hY W' ≤ specOpenToVariety hY W :=
  fun _ hx => h hx

/-- Every point `q` of an open `W ⊆ Spec A(Y)` has a classical point of its
zero set inside the corresponding open of `Y`. -/
theorem exists_mem_coordZeroSet_specOpenToVariety
    {W : Opens (AlgebraicGeometry.PrimeSpectrum.Top (coordinateRing Y))}
    {q : PrimeSpectrum (coordinateRing Y)} (hq : q ∈ W) :
    ∃ x : Y, x ∈ coordZeroSet (q.asIdeal : Set (coordinateRing Y)) ∧
      x ∈ specOpenToVariety hY W := by
  have h := (genericCompletionOpensOrderIso (TopCat.of Y)).apply_symm_apply
    ((Opens.map (genericCompletionIsoSpecTop hY).hom).obj W)
  have hmem : (genericCompletionHomeomorphSpec hY.isAlgebraicSet).symm q ∈
      (Opens.map (genericCompletionIsoSpecTop hY).hom).obj W := by
    change genericCompletionHomeomorphSpec hY.isAlgebraicSet
      ((genericCompletionHomeomorphSpec hY.isAlgebraicSet).symm q) ∈ W
    rwa [Homeomorph.apply_symm_apply]
  rw [← h] at hmem
  obtain ⟨x, hxZ, hxU⟩ := hmem
  exact ⟨x, hxZ, hxU⟩

/-- The value at a classical point `x` of a section of the structure sheaf of
`Spec A(Y)`: evaluate its germ in `A(Y)_{𝔪_x}` at `x`. -/
def specSectionEval {W : Opens (AlgebraicGeometry.PrimeSpectrum.Top (coordinateRing Y))}
    (s : (AlgebraicGeometry.Spec.structureSheaf (coordinateRing Y)).obj.obj (op W))
    (x : specOpenToVariety hY W) : k :=
  localizationEval x.1 (specPoint hY x.1) (specPoint_asIdeal hY x.1).ge
    (s.1 ⟨specPoint hY x.1, x.2⟩)

theorem specSectionEval_eq_div
    {W : Opens (AlgebraicGeometry.PrimeSpectrum.Top (coordinateRing Y))}
    (s : (AlgebraicGeometry.Spec.structureSheaf (coordinateRing Y)).obj.obj (op W))
    (x : specOpenToVariety hY W) (a f : coordinateRing Y)
    (hf : f ∈ (specPoint hY x.1).asIdeal.primeCompl)
    (he : s.1 ⟨specPoint hY x.1, x.2⟩ = LocalizedModule.mk a ⟨f, hf⟩) :
    specSectionEval hY s x = evalAt Y x.1 a / evalAt Y x.1 f := by
  rw [specSectionEval, he]
  exact localizationEval_mk _ _ _ _ _

theorem evalAt_ne_zero_of_mem_primeCompl (x : Y) {f : coordinateRing Y}
    (hf : f ∈ (specPoint hY x).asIdeal.primeCompl) : evalAt Y x f ≠ 0 := by
  intro h
  apply hf
  rw [specPoint_asIdeal]
  exact h

/-- Evaluating a structure-sheaf section at the classical points gives a
regular function. -/
theorem specSectionEval_mem
    {W : Opens (AlgebraicGeometry.PrimeSpectrum.Top (coordinateRing Y))}
    (s : (AlgebraicGeometry.Spec.structureSheaf (coordinateRing Y)).obj.obj (op W)) :
    specSectionEval hY s ∈
      (Variety.ofQuasiAffine hY.isQuasiAffineVariety).regular (specOpenToVariety hY W) := by
  intro P
  obtain ⟨V', hV', i, a, f, hfr⟩ := s.2 ⟨specPoint hY P.1, P.2⟩
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective f
  refine ⟨{x | specPoint hY x.1 ∈ V'},
    V'.isOpen.preimage ((continuous_specPoint hY).comp continuous_subtype_val), hV', g, h,
    fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨hf, -⟩ := hfr ⟨specPoint hY x.1, hx⟩
    have := evalAt_ne_zero_of_mem_primeCompl hY x.1 hf
    simpa using this
  · obtain ⟨hf, he⟩ := hfr ⟨specPoint hY x.1, hx⟩
    rw [specSectionEval_eq_div hY s x _ _ hf he]
    simp

/-- **Sections.** Evaluation at classical points, as a ring map from sections
of the structure sheaf of `Spec A(Y)` over `W` to regular functions on the
corresponding open of `Y`. -/
def specToRegular (W : Opens (AlgebraicGeometry.PrimeSpectrum.Top (coordinateRing Y))) :
    (AlgebraicGeometry.Spec.structureSheaf (coordinateRing Y)).obj.obj (op W) →+*
      (Variety.ofQuasiAffine hY.isQuasiAffineVariety).regular (specOpenToVariety hY W) where
  toFun s := ⟨specSectionEval hY s, specSectionEval_mem hY s⟩
  map_one' := Subtype.ext <| funext fun _ => map_one (localizationEval _ _ _)
  map_mul' _ _ := Subtype.ext <| funext fun _ => map_mul (localizationEval _ _ _) _ _
  map_zero' := Subtype.ext <| funext fun _ => map_zero (localizationEval _ _ _)
  map_add' _ _ := Subtype.ext <| funext fun _ => map_add (localizationEval _ _ _) _ _

@[simp]
theorem specToRegular_apply
    (W : Opens (AlgebraicGeometry.PrimeSpectrum.Top (coordinateRing Y)))
    (s : (AlgebraicGeometry.Spec.structureSheaf (coordinateRing Y)).obj.obj (op W))
    (x : specOpenToVariety hY W) :
    (specToRegular hY W s).1 x = specSectionEval hY s x :=
  rfl

/-- Evaluation at classical points is injective on structure-sheaf sections:
a section that is locally `a / f` and vanishes at the classical points has
`a` vanishing on a nonempty open subset of `Y`, so `a = 0`. -/
theorem specToRegular_injective
    (W : Opens (AlgebraicGeometry.PrimeSpectrum.Top (coordinateRing Y))) :
    Function.Injective (specToRegular hY W) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  apply Subtype.ext
  funext q
  obtain ⟨V', hqV', i, a, f, hfr⟩ := s.2 q
  have ha : a = 0 := by
    obtain ⟨x0, -, hx0⟩ := exists_mem_coordZeroSet_specOpenToVariety hY hqV'
    refine eq_zero_of_evalAt_eq_zero_of_isOpen hY.1 (specOpenToVariety hY V').isOpen
      ⟨x0, hx0⟩ fun x hx => ?_
    obtain ⟨hf, he⟩ := hfr ⟨specPoint hY x, hx⟩
    have hxW : x ∈ specOpenToVariety hY W := specOpenToVariety_mono hY i.le hx
    have h0 : specSectionEval hY s ⟨x, hxW⟩ = 0 := congrArg (fun g => g.1 ⟨x, hxW⟩) hs
    rw [specSectionEval_eq_div hY s ⟨x, hxW⟩ a f hf he] at h0
    exact (div_eq_zero_iff.1 h0).resolve_right (evalAt_ne_zero_of_mem_primeCompl hY x hf)
  obtain ⟨hf, he⟩ := hfr ⟨q.1, hqV'⟩
  exact he.trans (by rw [ha, LocalizedModule.zero_mk]; rfl)

/-- Evaluation at classical points is surjective onto regular functions: a
regular function is locally `a / f` near a classical point of the zero set of
each prime `q`; these local quotients agree in every localization by the
identity principle, and glue to a structure-sheaf section. -/
theorem specToRegular_surjective
    (W : Opens (AlgebraicGeometry.PrimeSpectrum.Top (coordinateRing Y))) :
    Function.Surjective (specToRegular hY W) := by
  intro g
  have key : ∀ q : W, ∃ (O : Set Y) (a f : coordinateRing Y), IsOpen O ∧
      O ⊆ {y : Y | specPoint hY y ∈ W} ∧
      (∃ x ∈ O, x ∈ coordZeroSet
        ((q.1 : PrimeSpectrum (coordinateRing Y)).asIdeal : Set (coordinateRing Y))) ∧
      ∀ y (hy : y ∈ specOpenToVariety hY W), y ∈ O →
        evalAt Y y f ≠ 0 ∧ g.1 ⟨y, hy⟩ = evalAt Y y a / evalAt Y y f := by
    intro q
    obtain ⟨x, hxZ, hxU⟩ := exists_mem_coordZeroSet_specOpenToVariety hY q.2
    obtain ⟨O, hO, hxO, G, Hh, hne, heq⟩ := g.2 ⟨x, hxU⟩
    obtain ⟨O₁, hO₁, rfl⟩ := isOpen_induced_iff.1 hO
    refine ⟨O₁ ∩ {y : Y | specPoint hY y ∈ W}, Ideal.Quotient.mk _ G, Ideal.Quotient.mk _ Hh,
      hO₁.inter (specOpenToVariety hY W).isOpen, Set.inter_subset_right,
      ⟨x, ⟨hxO, hxU⟩, hxZ⟩, fun y hy hyO => ⟨?_, ?_⟩⟩
    · intro h0
      exact hne ⟨y, hy⟩ hyO.1 h0
    · exact heq ⟨y, hy⟩ hyO.1
  choose O a f hO hOU hx hrep using key
  have hfq : ∀ q : W, f q ∉ (q.1 : PrimeSpectrum (coordinateRing Y)).asIdeal := by
    intro q hmem
    obtain ⟨x, hxO, hxZ⟩ := hx q
    exact (hrep q x (hOU q hxO) hxO).1 (hxZ _ hmem)
  let N : W → Opens (AlgebraicGeometry.PrimeSpectrum.Top (coordinateRing Y)) := fun q =>
    (Opens.map (genericCompletionIsoSpecTop hY).inv).obj
      (genericCompletionOpensOrderIso (TopCat.of Y) ⟨O q, hO q⟩)
  have hN : ∀ q (z : PrimeSpectrum (coordinateRing Y)),
      z ∈ N q ↔ (coordZeroSet (z.asIdeal : Set (coordinateRing Y)) ∩ O q).Nonempty :=
    fun _ _ => Iff.rfl
  have hagree : ∀ q z : W, z.1 ∈ N q → a z * f q = a q * f z := by
    intro q z hz
    have hirr := isIrreducible_coordZeroSet hY.isAlgebraicSet
      (z.1 : PrimeSpectrum (coordinateRing Y)).isPrime
    obtain ⟨x, hxO, hxZ⟩ := hx z
    have hne : (coordZeroSet ((z.1 : PrimeSpectrum (coordinateRing Y)).asIdeal :
        Set (coordinateRing Y)) ∩ (O z ∩ O q)).Nonempty :=
      hirr.2 _ _ (hO z) (hO q) ⟨x, hxZ, hxO⟩ ((hN q z.1).1 hz)
    rw [← sub_eq_zero]
    refine eq_zero_of_evalAt_eq_zero_of_isOpen hY.1 ((hO z).inter (hO q))
      (hne.mono Set.inter_subset_right) fun y hy => ?_
    have hyW := hOU z hy.1
    obtain ⟨hfz, hgz⟩ := hrep z y hyW hy.1
    obtain ⟨hfq', hgq⟩ := hrep q y hyW hy.2
    rw [hgz] at hgq
    rw [map_sub, map_mul, map_mul]
    rw [div_eq_div_iff hfz hfq'] at hgq
    linear_combination hgq
  refine ⟨⟨fun q => LocalizedModule.mk (a q) ⟨f q, hfq q⟩, fun q => ?_⟩, ?_⟩
  · have hqN : q.1 ∈ N q := by
      obtain ⟨x, hxO, hxZ⟩ := hx q
      exact (hN q q.1).2 ⟨x, hxZ, hxO⟩
    refine ⟨N q ⊓ W, ⟨hqN, q.2⟩, homOfLE inf_le_right, a q, f q, fun z => ⟨?_, ?_⟩⟩
    · intro hmem
      obtain ⟨y, hyZ, hyO⟩ := (hN q z.1).1 z.2.1
      exact (hrep q y (hOU q hyO) hyO).1 (hyZ _ hmem)
    · change LocalizedModule.mk (a ⟨z.1, z.2.2⟩) ⟨f ⟨z.1, z.2.2⟩, _⟩ = LocalizedModule.mk (a q) _
      rw [LocalizedModule.mk_eq]
      refine ⟨1, ?_⟩
      simp only [one_smul, Submonoid.smul_def, smul_eq_mul]
      have := hagree q ⟨z.1, z.2.2⟩ z.2.1
      linear_combination this
  · apply Subtype.ext
    funext x
    let q : W := ⟨specPoint hY x.1, x.2⟩
    refine (localizationEval_mk (x.1 : Y) (specPoint hY x.1) (specPoint_asIdeal hY x.1).ge
      (a q) ⟨f q, hfq q⟩).trans ?_
    obtain ⟨x', hx'O, hx'Z⟩ := hx q
    have hx'x : x' = x.1 := by
      have : x' ∈ coordZeroSet (maximalIdealAt Y x.1 : Set (coordinateRing Y)) := by
        rw [← specPoint_asIdeal hY x.1]
        exact hx'Z
      exact (coordZeroSet_maximalIdealAt (Y := Y) x.1).subset this
    exact (hrep q x.1 x.2 (hx'x ▸ hx'O)).2.symm

/-- Evaluation at classical points, as a morphism from the structure sheaf of
`Spec A(Y)` to the pushforward of `α_* 𝒪_Y` along `t(Y) ≅ Spec A(Y)`. -/
def specToGenericCompletionPushforward :
    (AlgebraicGeometry.Spec.structureSheaf (coordinateRing Y)).obj ⟶
      (TopCat.Presheaf.pushforward CommRingCat (genericCompletionIsoSpecTop hY).hom).obj
        (genericCompletionRegularSheaf (Variety.ofQuasiAffine hY.isQuasiAffineVariety)).obj where
  app W := CommRingCat.ofHom (specToRegular hY W.unop)
  naturality _ _ _ := by
    ext
    rfl

instance isIso_specToGenericCompletionPushforward :
    IsIso (specToGenericCompletionPushforward hY) := by
  have (W : (Opens (AlgebraicGeometry.PrimeSpectrum.Top (coordinateRing Y)))ᵒᵖ) :
      IsIso ((specToGenericCompletionPushforward hY).app W) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      ⟨specToRegular_injective hY W.unop, specToRegular_surjective hY W.unop⟩
  exact NatIso.isIso_of_isIso_app _

/-- The ringed space `(t(Y), α_* 𝒪_Y)` attached to an affine variety `Y`, as a
sheafed space. -/
def affineVarietyGenericCompletionSheafedSpace :
    AlgebraicGeometry.SheafedSpace CommRingCat.{u} where
  carrier :=
    genericCompletionObj (TopCat.of (Variety.ofQuasiAffine hY.isQuasiAffineVariety).carrier)
  presheaf := (genericCompletionRegularSheaf (Variety.ofQuasiAffine hY.isQuasiAffineVariety)).obj
  IsSheaf :=
    (genericCompletionRegularSheaf (Variety.ofQuasiAffine hY.isQuasiAffineVariety)).property

/-- **Hartshorne II.2, affine case of Proposition 2.6.** The canonical
isomorphism of sheafed spaces `(t(Y), α_* 𝒪_Y) ≅ Spec A(Y)`: on points an
irreducible closed subset goes to its ideal, and on sections a section of the
structure sheaf is sent to the regular function obtained by evaluating its
germs at the classical points. -/
def affineVarietyGenericCompletionSheafedSpaceIsoSpec :
    affineVarietyGenericCompletionSheafedSpace hY ≅
      AlgebraicGeometry.Spec.sheafedSpaceObj (CommRingCat.of (coordinateRing Y)) :=
  AlgebraicGeometry.SheafedSpace.isoMk
    (AlgebraicGeometry.PresheafedSpace.isoOfComponents (genericCompletionIsoSpecTop hY)
      (asIso (specToGenericCompletionPushforward hY)).symm)

/-- The stalks of `(t(Y), α_* 𝒪_Y)` are local rings, being isomorphic to the
stalks of `Spec A(Y)`; so it is a locally ringed space. -/
def affineVarietyGenericCompletionLocallyRingedSpace :
    AlgebraicGeometry.LocallyRingedSpace.{u} where
  toSheafedSpace := affineVarietyGenericCompletionSheafedSpace hY
  isLocalRing x :=
    @RingEquiv.isLocalRing _ _ _
      ((AlgebraicGeometry.Spec.locallyRingedSpaceObj
        (CommRingCat.of (coordinateRing Y))).isLocalRing
          ((affineVarietyGenericCompletionSheafedSpaceIsoSpec hY).hom.hom.base x)) _
      (AlgebraicGeometry.PresheafedSpace.stalkMap.stalkIso
        ((AlgebraicGeometry.SheafedSpace.forgetToPresheafedSpace).mapIso
          (affineVarietyGenericCompletionSheafedSpaceIsoSpec hY)) x).commRingCatIsoToRingEquiv

/-- The underlying sheafed space is the project's `(t(Y), α_* 𝒪_Y)`: its
presheaf is the transported regular-function sheaf. -/
theorem affineVarietyGenericCompletionLocallyRingedSpace_presheaf :
    (affineVarietyGenericCompletionLocallyRingedSpace hY).presheaf =
      (genericCompletionRegularSheaf (Variety.ofQuasiAffine hY.isQuasiAffineVariety)).obj :=
  rfl

/-- **Hartshorne II.2, affine case of Proposition 2.6.** For an affine variety
`Y` over an algebraically closed field, the canonical isomorphism of locally
ringed spaces `(t(Y), α_* 𝒪_Y) ≅ Spec A(Y)`. -/
def affineVarietyGenericCompletionIsoSpec :
    affineVarietyGenericCompletionLocallyRingedSpace hY ≅
      AlgebraicGeometry.Spec.locallyRingedSpaceObj (CommRingCat.of (coordinateRing Y)) :=
  AlgebraicGeometry.LocallyRingedSpace.isoOfSheafedSpaceIso
    (affineVarietyGenericCompletionSheafedSpaceIsoSpec hY)

/-- On points, the isomorphism sends an irreducible closed subset `Z` of `Y` to
its ideal `I(Z) ⊆ A(Y)`. -/
theorem affineVarietyGenericCompletionIsoSpec_hom_base_asIdeal
    (Z : IrreducibleCloseds Y) :
    ((affineVarietyGenericCompletionIsoSpec hY).hom.base Z).asIdeal = coordIdealOf (Z : Set Y) :=
  rfl

/-- On points, a classical point `P` goes to its maximal ideal `𝔪_P`. -/
theorem affineVarietyGenericCompletionIsoSpec_hom_base_alpha (x : Y) :
    ((affineVarietyGenericCompletionIsoSpec hY).hom.base
      (genericCompletionAlpha (TopCat.of Y) x)).asIdeal = maximalIdealAt Y x :=
  genericCompletionHomeomorphSpec_alpha hY.isAlgebraicSet x

/-- On sections over an open `W ⊆ Spec A(Y)`, the isomorphism is evaluation of
germs at the classical points. -/
theorem affineVarietyGenericCompletionIsoSpec_hom_c_app
    (W : Opens (AlgebraicGeometry.PrimeSpectrum.Top (coordinateRing Y))) :
    (affineVarietyGenericCompletionIsoSpec hY).hom.c.app (op W) =
      CommRingCat.ofHom (specToRegular hY W) :=
  rfl

end AlgClosed

end Hartshorne

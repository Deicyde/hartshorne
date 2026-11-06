/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.FlatFamilies.FlatOverRegularCurve
import Hartshorne.Cohomology.FlatFamilies.HironakaNormality
import Hartshorne.Scheme.Normal
import Hartshorne.Scheme.ReducedInducedSubscheme
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Normal algebraic families over a nonsingular curve are flat

Hartshorne, *Algebraic Geometry*, III.9, the definition after Corollary 9.10 and Theorem 9.11
(pp. 263–264).

## Encoding

Varieties are encoded as in the other III.9 files: `k`-schemes `X : Over (Spec k)` with `X.left`
integral and `X.hom` separated, locally of finite type and quasi-compact, over an algebraically
closed field `k`. For `f : X ⟶ T` and `t ∈ T`, the scheme-theoretic fibre `X_t` is Mathlib's
`f.fiber t`, and the reduced fibre `X^t = (X_t)_red` is `Hartshorne.reducedFiber f t`, the
reduced induced closed subscheme on all of `X_t`. A nonsingular curve is an integral scheme of
dimension one all of whose local rings are regular; "`X^t` is normal" is `Hartshorne.IsNormal`.
The dimension condition `dim X^t = dim X - dim T` is stated additively.

## Proof

Flatness: `X` is integral and `f` is surjective, so the only irreducible component of `X`
dominates `T`, and flatness over a regular one-dimensional base follows from Hartshorne
III Proposition 9.7.

Reducedness of `X_t` (`Hartshorne.NormalFamily.isReduced_fiber`): let `w ∈ X_t` with image `x`
in `X`, let `A = 𝒪_{X,x}`, and let `τ ∈ A` be the image of a generator of the maximal ideal of
the discrete valuation ring `𝒪_{T,t}`.

* `𝒪_{X_t,w} = A / τA` (`ker_stalkMap_fiberι`): the kernel of the stalk map of the fibre
  inclusion is `𝔪_t A`; the reverse inclusion uses the point `Spec (A / 𝔪_t A) ⟶ X_t` given by
  the universal property of the fibre product.
* `τA` has a unique minimal prime `p`, the prime of the generic point `η` of the irreducible
  fibre: every prime containing `τ` corresponds to a point of `X_t`, which specializes from `η`.
* `A_p = 𝒪_{X,η}` (`isLocalization_stalkSpecializes`), and `𝒪_{X,η} / τ = 𝒪_{X_t,η}` is
  reduced and zero-dimensional, hence a field; so `τ` generates the maximal ideal of `A_p`.
* `A / p` is the local ring of the reduced fibre `X^t` at `w`: the stalk map of the preimmersion
  `X^t ⟶ X` is surjective with prime kernel (the local rings of `X^t` are domains), and this
  kernel has the same zero locus as `τA`. So `A / p` is integrally closed.
* Hironaka's lemma (Hartshorne III Lemma 9.12) gives `p = τA`, so `𝒪_{X_t,w} = A / p` is a
  domain.

The irreducibility of `X^t` and the reducedness of `X_t` at its generic point enter the second
and third steps; the dimension condition, separatedness and algebraic closedness are part of the
definition and are not needed by the argument.

## Main definitions and results

* `Hartshorne.reducedFiber`: the reduced fibre `X^t`.
* `Hartshorne.IsAlgebraicFamily`: an algebraic family of varieties.
* `Hartshorne.IsAlgebraicFamily.isReduced_fiber_and_flat`: Hartshorne III Theorem 9.11.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing Topology
  TopologicalSpace

namespace Hartshorne

universe u

namespace NormalFamily

variable {X Y : Scheme.{u}}

/-- A prime of `𝒪_{X,x}` contains `𝔪_{f x} 𝒪_{X,x}` exactly when the corresponding
generalization of `x` lies in the fibre of `f` through `x`. -/
theorem map_maximalIdeal_le_iff (f : X ⟶ Y) (x : X) (Q : Spec (X.presheaf.stalk x)) :
    (maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom ≤ Q.asIdeal ↔
      f (X.fromSpecStalk x Q) = f x := by
  have h : f (X.fromSpecStalk x Q) = Y.fromSpecStalk (f x) (Spec.map (f.stalkMap x) Q) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Scheme.SpecMap_stalkMap_fromSpecStalk]
  have h1 : f (X.fromSpecStalk x Q) = f x ↔
      Spec.map (f.stalkMap x) Q = closedPoint (Y.presheaf.stalk (f x)) := by
    rw [h]
    conv_lhs => rhs; rw [← Scheme.fromSpecStalk_closedPoint (x := f x) (X := Y)]
    exact (Y.fromSpecStalk (f x)).isEmbedding.injective.eq_iff
  refine Iff.trans ?_ h1.symm
  rw [Ideal.map_le_iff_le_comap]
  constructor
  · intro h
    exact PrimeSpectrum.ext (le_antisymm (le_maximalIdeal (PrimeSpectrum.isPrime _).ne_top) h)
  · intro h
    exact (congrArg PrimeSpectrum.asIdeal h).ge

/-- For a preimmersion `g : F ⟶ X` and `z ∈ F`, a prime of `𝒪_{X,g z}` contains the kernel of the
stalk map exactly when the corresponding generalization of `g z` lies in the image of `g`. -/
theorem ker_stalkMap_le_iff {F : Scheme.{u}} (g : F ⟶ X) [IsPreimmersion g] (z : F)
    (Q : Spec (X.presheaf.stalk (g z))) :
    RingHom.ker (g.stalkMap z).hom ≤ Q.asIdeal ↔ X.fromSpecStalk (g z) Q ∈ Set.range g := by
  have hψ : Function.Surjective (g.stalkMap z).hom := g.stalkMap_surjective z
  have hc : ∀ q' : Spec (F.presheaf.stalk z),
      g (F.fromSpecStalk z q') = X.fromSpecStalk (g z) (Spec.map (g.stalkMap z) q') := by
    intro q'
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Scheme.SpecMap_stalkMap_fromSpecStalk]
  have hz : RingHom.ker (g.stalkMap z).hom ≤ Q.asIdeal ↔
      Q ∈ Set.range (PrimeSpectrum.comap (g.stalkMap z).hom) := by
    rw [range_comap_of_surjective (hf := hψ)]
    exact Iff.rfl
  refine hz.trans ⟨?_, ?_⟩
  · rintro ⟨q', rfl⟩
    exact ⟨F.fromSpecStalk z q', hc q'⟩
  · rintro ⟨z', hz'⟩
    have hsp : g z' ⤳ g z := by
      rw [hz']
      exact (Scheme.range_fromSpecStalk (x := g z)).subset ⟨Q, rfl⟩
    rw [g.isEmbedding.toIsInducing.specializes_iff] at hsp
    obtain ⟨q', rfl⟩ : z' ∈ Set.range (F.fromSpecStalk z) := by
      rw [Scheme.range_fromSpecStalk]; exact hsp
    refine ⟨q', (X.fromSpecStalk (g z)).isEmbedding.injective ?_⟩
    rw [← hz', hc q']
    rfl

/-- The stalk of `Spec` of a field at any point is a field. -/
theorem isField_stalk_spec_field (K : Type u) [Field K] (q : Spec (CommRingCat.of K)) :
    IsField ((Spec (CommRingCat.of K)).presheaf.stalk q) := by
  obtain rfl : q = closedPoint K := Subsingleton.elim (α := PrimeSpectrum K) _ _
  exact (stalkClosedPointIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
    (Field.toIsField K)

set_option backward.isDefEq.respectTransparency false in
/-- Going along two stalk identifications between inseparable points and back is the
identity. -/
theorem stalkCongr_hom_stalkCongr_hom {a b : X} (e1 : Inseparable a b) (e2 : Inseparable b a)
    (s : X.presheaf.stalk a) :
    (X.presheaf.stalkCongr e2).hom ((X.presheaf.stalkCongr e1).hom s) = s := by
  rw [← CategoryTheory.comp_apply]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The local ring of the scheme-theoretic fibre `X_y` at a point `w` is
`𝒪_{X,x} / 𝔪_y 𝒪_{X,x}`, where `x` is the image of `w` in `X`: the kernel of the stalk map of the
fibre inclusion is `𝔪_y 𝒪_{X,x}`. -/
theorem ker_stalkMap_fiberι (f : X ⟶ Y) (y : Y) (w : f.fiber y) :
    RingHom.ker ((f.fiberι y).stalkMap w).hom =
      (maximalIdeal (Y.presheaf.stalk (f (f.fiberι y w)))).map
        (f.stalkMap (f.fiberι y w)).hom := by
  set x := f.fiberι y w with hx
  have hfx : f x = y := by
    have : x ∈ Set.range (f.fiberι y) := ⟨w, rfl⟩
    rwa [Scheme.Hom.range_fiberι] at this
  apply le_antisymm
  · intro a ha
    rw [RingHom.mem_ker] at ha
    let A := X.presheaf.stalk x
    let I := (maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom
    have hI : I ≤ maximalIdeal A :=
      Ideal.map_le_iff_le_comap.mpr fun r hr => map_nonunit (f.stalkMap x).hom r hr
    have : Nontrivial (A ⧸ I) :=
      Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (maximalIdeal.isMaximal A).ne_top hI)
    have : IsLocalRing (A ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
    let mk : X.presheaf.stalk x ⟶ CommRingCat.of (A ⧸ I) :=
      CommRingCat.ofHom (Ideal.Quotient.mk I)
    have : IsLocalHom mk.hom := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    let ρ' : Y.residueField (f x) ⟶ CommRingCat.of (A ⧸ I) :=
      CommRingCat.ofHom (Ideal.quotientMap I (f.stalkMap x).hom Ideal.le_comap_map)
    let Φ : Spec (CommRingCat.of (A ⧸ I)) ⟶ X := Spec.map mk ≫ X.fromSpecStalk x
    let ρ : Spec (CommRingCat.of (A ⧸ I)) ⟶ Spec (Y.residueField y) :=
      Spec.map ((Y.residueFieldCongr hfx.symm).hom ≫ ρ')
    have hcond : Φ ≫ f = ρ ≫ Y.fromSpecResidueField y := by
      simp only [Φ, ρ, Spec.map_comp, Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField]
      rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, Scheme.fromSpecResidueField,
        ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
      congr 2
    let L : Spec (CommRingCat.of (A ⧸ I)) ⟶ f.fiber y := pullback.lift Φ ρ hcond
    have hL : L ≫ f.fiberι y = Φ := pullback.lift_fst _ _ _
    have e1 := congrArg (SpecToEquivOfLocalRing X (CommRingCat.of (A ⧸ I))) hL
    have e2 : SpecToEquivOfLocalRing X (CommRingCat.of (A ⧸ I)) Φ = ⟨x, mk, inferInstance⟩ :=
      (SpecToEquivOfLocalRing X _).apply_symm_apply ⟨x, mk, inferInstance⟩
    obtain ⟨h1, h2⟩ := SpecToEquivOfLocalRing_eq_iff.mp (e1.trans e2)
    simp only [SpecToEquivOfLocalRing_apply_fst, SpecToEquivOfLocalRing_apply_snd_coe] at h1 h2
    rw [Scheme.stalkClosedPointTo_comp] at h2
    have hLc : w = L (closedPoint _) :=
      ((f.fiberι y).isEmbedding.injective h1).symm
    have hcp := Scheme.Hom.stalkMap_congr_point (f.fiberι y) w _ hLc
    have hb := ConcreteCategory.congr_hom hcp a
    rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply, ha, map_zero] at hb
    have h3 : Scheme.stalkClosedPointTo L ((f.fiberι y).stalkMap (L (closedPoint _))
        ((X.presheaf.stalkCongr (.of_eq (congrArg _ hLc))).hom a)) =
        mk ((X.presheaf.stalkCongr (.of_eq h1)).hom
          ((X.presheaf.stalkCongr (.of_eq (congrArg _ hLc))).hom a)) :=
      ConcreteCategory.congr_hom h2 _
    have h5 := stalkCongr_hom_stalkCongr_hom (.of_eq (congrArg (f.fiberι y) hLc)) (.of_eq h1) a
    have h6 : mk a = 0 :=
      (congrArg mk h5).symm.trans (h3.symm.trans ((congrArg _ hb.symm).trans (map_zero _)))
    exact Ideal.Quotient.eq_zero_iff_mem.mp h6
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, RingHom.mem_ker, ← CommRingCat.comp_apply,
      ← Scheme.Hom.stalkMap_comp,
      Scheme.Hom.stalkMap_congr_hom _ _ (f.fiber_fac y), Scheme.Hom.stalkMap_comp]
    have hfield := isField_stalk_spec_field (Y.residueField y) (f.fiberToSpecResidueField y w)
    have e : Inseparable (f (f.fiberι y w))
        (Y.fromSpecResidueField y (f.fiberToSpecResidueField y w)) := .of_eq (by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, f.fiber_fac])
    have hnu := map_nonunit ((Y.presheaf.stalkCongr e).hom ≫
      (Y.fromSpecResidueField y).stalkMap (f.fiberToSpecResidueField y w)).hom r hr
    have h0 : ((Y.presheaf.stalkCongr e).hom ≫
        (Y.fromSpecResidueField y).stalkMap (f.fiberToSpecResidueField y w)).hom r = 0 := by
      by_contra hne
      obtain ⟨b, hb⟩ := hfield.mul_inv_cancel hne
      exact hnu (isUnit_iff_exists_inv.mpr ⟨b, hb⟩)
    simp only [CommRingCat.comp_apply] at h0 ⊢
    exact (congrArg (fun s => (f.fiberToSpecResidueField y).stalkMap w s) h0).trans (map_zero _)

set_option backward.isDefEq.respectTransparency false in
/-- If `x ⤳ y`, then `𝒪_{X,x}` is the localization of `𝒪_{X,y}` at the prime ideal
corresponding to `x`, the preimage of the maximal ideal of `𝒪_{X,x}`. -/
theorem isLocalization_stalkSpecializes {x y : X} (h : x ⤳ y) :
    let := (X.presheaf.stalkSpecializes h).hom.toAlgebra
    IsLocalization.AtPrime (X.presheaf.stalk x)
      ((maximalIdeal (X.presheaf.stalk x)).comap (X.presheaf.stalkSpecializes h).hom) := by
  let : Algebra (X.presheaf.stalk y) (X.presheaf.stalk x) :=
    (X.presheaf.stalkSpecializes h).hom.toAlgebra
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hxV : x ∈ V := h.mem_open V.isOpen hyV
  let : Algebra Γ(X, V) (X.presheaf.stalk y) := X.presheaf.algebra_section_stalk ⟨y, hyV⟩
  let : Algebra Γ(X, V) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hxV⟩
  have := hV.isLocalization_stalk ⟨y, hyV⟩
  have := hV.isLocalization_stalk ⟨x, hxV⟩
  have : IsScalarTower Γ(X, V) (X.presheaf.stalk y) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq'
      (congrArg CommRingCat.Hom.hom (X.presheaf.germ_stalkSpecializes hyV h)).symm
  set p := (maximalIdeal (X.presheaf.stalk x)).comap (X.presheaf.stalkSpecializes h).hom
  have : p.IsPrime := Ideal.comap_isPrime _ _
  have hloc := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    (hV.primeIdealOf ⟨y, hyV⟩).asIdeal.primeCompl (Localization.AtPrime p) p
  have hcomap : p.comap (algebraMap Γ(X, V) (X.presheaf.stalk y)) =
      (hV.primeIdealOf ⟨x, hxV⟩).asIdeal := by
    rw [Ideal.comap_comap]
    change Ideal.comap ((algebraMap (X.presheaf.stalk y) (X.presheaf.stalk x)).comp
      (algebraMap Γ(X, V) (X.presheaf.stalk y))) _ = _
    rw [← IsScalarTower.algebraMap_eq]
    exact IsLocalization.AtPrime.under_maximalIdeal (X.presheaf.stalk x)
      (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have key : ∀ (P Q : Ideal Γ(X, V)) [P.IsPrime] [Q.IsPrime], P = Q →
      IsLocalization.AtPrime (Localization.AtPrime p) P →
        IsLocalization.AtPrime (Localization.AtPrime p) Q := by
    intro P Q _ _ hPQ hP
    subst hPQ
    exact hP
  have hloc' := key _ _ hcomap hloc
  let e : Localization.AtPrime p ≃ₐ[Γ(X, V)] X.presheaf.stalk x :=
    IsLocalization.algEquiv (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl _ _
  have he : e.toRingHom.comp (algebraMap (X.presheaf.stalk y) (Localization.AtPrime p)) =
      algebraMap (X.presheaf.stalk y) (X.presheaf.stalk x) := by
    refine IsLocalization.ringHom_ext (hV.primeIdealOf ⟨y, hyV⟩).asIdeal.primeCompl ?_
    ext r
    simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
    exact e.commutes r
  let e' : Localization.AtPrime p ≃ₐ[X.presheaf.stalk y] X.presheaf.stalk x :=
    AlgEquiv.ofRingEquiv (f := e.toRingEquiv) (fun s => DFunLike.congr_fun he s)
  exact IsLocalization.isLocalization_of_algEquiv p.primeCompl e'

/-- Along a specialization between equal points, the maximal ideal maps onto the maximal
ideal. -/
theorem map_maximalIdeal_stalkSpecializes_of_eq {a b : X} (hab : a = b) (h : a ⤳ b) :
    (maximalIdeal (X.presheaf.stalk b)).map (X.presheaf.stalkSpecializes h).hom =
      maximalIdeal (X.presheaf.stalk a) := by
  subst hab
  rw [TopCat.Presheaf.stalkSpecializes_refl, CommRingCat.hom_id, Ideal.map_id]

/-- A local ring of a scheme locally of finite type over a field `k` is a `k`-algebra
essentially of finite type. -/
theorem exists_algebra_essFiniteType_stalk {k : Type u} [Field k]
    (φ : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType φ] (x : X) :
    ∃ _ : Algebra k (X.presheaf.stalk x), Algebra.EssFiniteType k (X.presheaf.stalk x) := by
  have h1 : ∀ q : PrimeSpectrum k,
      (algebraMap k ((Spec.structureSheaf k).presheaf.stalk q)).EssFiniteType := fun q =>
    RingHom.EssFiniteType.holdsForLocalization _ q.asIdeal.primeCompl
  exact ⟨_, (h1 (φ x)).comp (LocallyOfFiniteType.stalkMap φ x)⟩

end NormalFamily

/-- The reduced fibre `X^t = (X_t)_red` of `f : X ⟶ T` over `t`: the scheme-theoretic fibre
`X_t` with its reduced induced structure. -/
noncomputable abbrev reducedFiber {X T : Scheme.{u}} (f : X ⟶ T) (t : T) : Scheme.{u} :=
  reducedInducedSubscheme (⊤ : Closeds (f.fiber t))

namespace NormalFamily

variable {X Y : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- The local form of Hartshorne III Theorem 9.11. Let `X` be an integral scheme locally of finite
type over a field, `f : X ⟶ T` a morphism and `t ∈ T` such that the maximal ideals of the local
rings of `T` are principal. If the reduced fibre `X^t` is irreducible and normal and the fibre `X_t`
is reduced at its generic point, then `X_t` is reduced. -/
theorem isReduced_fiber {k : Type u} [Field k] (φ : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType φ] [IsIntegral X] [IsLocallyNoetherian X] (f : X ⟶ Y) (t : Y)
    (hπ : ∀ y : Y, (maximalIdeal (Y.presheaf.stalk y)).IsPrincipal)
    (hirr : IrreducibleSpace (reducedFiber f t))
    (hgen : ∀ ξ : f.fiber t, closure {ξ} ∈ irreducibleComponents (f.fiber t) →
      _root_.IsReduced ((f.fiber t).presheaf.stalk ξ))
    (hnorm : IsNormal (reducedFiber f t)) :
    IsReduced (f.fiber t) := by
  let ρ := reducedInducedSubschemeι (⊤ : Closeds (f.fiber t))
  have hρsurj : Function.Surjective ρ := by
    rw [← Set.range_eq_univ]
    exact range_reducedInducedSubschemeι _
  have hFirr : IrreducibleSpace (f.fiber t) := by
    have h := (IrreducibleSpace.isIrreducible_univ (reducedFiber f t)).image ρ
      ρ.continuous.continuousOn
    rw [Set.image_univ, Set.range_eq_univ.mpr hρsurj] at h
    exact (irreducibleSpace_def _).mpr h
  let ξ := genericPoint (f.fiber t)
  have hξ : ∀ z : f.fiber t, ξ ⤳ z := fun z => genericPoint_specializes z
  have hfib : ∀ z : f.fiber t, f (f.fiberι t z) = t := fun z => by
    have : f.fiberι t z ∈ Set.range (f.fiberι t) := ⟨z, rfl⟩
    rwa [Scheme.Hom.range_fiberι] at this
  -- The generic point of the fibre.
  have hredξ : _root_.IsReduced ((f.fiber t).presheaf.stalk ξ) := by
    apply hgen
    rw [irreducibleComponents_eq_singleton, (genericPoint_spec (f.fiber t)).def]
    rfl
  have hmaxB : maximalIdeal (X.presheaf.stalk (f.fiberι t ξ)) =
      (maximalIdeal (Y.presheaf.stalk (f (f.fiberι t ξ)))).map
        (f.stalkMap (f.fiberι t ξ)).hom := by
    rw [← ker_stalkMap_fiberι f t ξ]
    have hdim : Ring.KrullDimLE 0 ((f.fiber t).presheaf.stalk ξ) := by
      have hc : Order.coheight ξ = 0 := Order.coheight_eq_zero.mpr fun b _ => hξ b
      rw [Ring.krullDimLE_iff, ringKrullDim_stalk_eq_coheight, hc]
      rfl
    have hfield : IsField ((f.fiber t).presheaf.stalk ξ) := Ring.KrullDimLE.isField_of_isReduced
    have hsurj := (f.fiberι t).stalkMap_surjective ξ
    have hmax : (RingHom.ker ((f.fiberι t).stalkMap ξ).hom).IsMaximal :=
      Ideal.Quotient.maximal_of_isField _
        ((RingHom.quotientKerEquivOfSurjective hsurj).toMulEquiv.isField hfield)
    exact (IsLocalRing.eq_maximalIdeal hmax).symm
  have hred : ∀ w : f.fiber t, _root_.IsReduced ((f.fiber t).presheaf.stalk w) := by
    intro w
    obtain ⟨u, rfl⟩ := hρsurj w
    have hfx : f (f.fiberι t (ρ u)) = t := hfib (ρ u)
    obtain ⟨π, hπeq⟩ := (hπ (f (f.fiberι t (ρ u)))).principal
    have hI : (maximalIdeal (Y.presheaf.stalk (f (f.fiberι t (ρ u))))).map
        (f.stalkMap (f.fiberι t (ρ u))).hom =
          Ideal.span {(f.stalkMap (f.fiberι t (ρ u))).hom π} := by
      rw [hπeq, Ideal.submodule_span_eq, Ideal.map_span, Set.image_singleton]
    -- The prime `p` of `𝒪_{X,x}` corresponding to the generic point of the fibre.
    have hηx : f.fiberι t ξ ⤳ f.fiberι t (ρ u) := (hξ (ρ u)).map (f.fiberι t).continuous
    let σ := X.presheaf.stalkSpecializes hηx
    let p := (maximalIdeal (X.presheaf.stalk (f.fiberι t ξ))).comap σ.hom
    have : p.IsPrime := Ideal.comap_isPrime _ _
    let Pp : Spec (X.presheaf.stalk (f.fiberι t (ρ u))) := Spec.map σ (closedPoint _)
    have hPpη : X.fromSpecStalk (f.fiberι t (ρ u)) Pp = f.fiberι t ξ := by
      rw [← Scheme.Hom.comp_apply, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
        Scheme.fromSpecStalk_closedPoint]
    have hle : ∀ Q : Spec (X.presheaf.stalk (f.fiberι t (ρ u))),
        Ideal.span {(f.stalkMap (f.fiberι t (ρ u))).hom π} ≤ Q.asIdeal ↔
          f (X.fromSpecStalk (f.fiberι t (ρ u)) Q) = t := by
      intro Q
      rw [← hI, map_maximalIdeal_le_iff, hfx]
    have hIp : Ideal.span {(f.stalkMap (f.fiberι t (ρ u))).hom π} ≤ p :=
      (hle Pp).mpr (by rw [hPpη, hfib])
    have hpQ : ∀ Q : Spec (X.presheaf.stalk (f.fiberι t (ρ u))),
        Ideal.span {(f.stalkMap (f.fiberι t (ρ u))).hom π} ≤ Q.asIdeal → p ≤ Q.asIdeal := by
      intro Q hQ
      obtain ⟨z, hz⟩ : X.fromSpecStalk (f.fiberι t (ρ u)) Q ∈ Set.range (f.fiberι t) := by
        rw [Scheme.Hom.range_fiberι]; exact (hle Q).mp hQ
      have h2 : X.fromSpecStalk (f.fiberι t (ρ u)) Pp ⤳ X.fromSpecStalk (f.fiberι t (ρ u)) Q := by
        rw [hPpη, ← hz]; exact (hξ z).map (f.fiberι t).continuous
      rw [(X.fromSpecStalk (f.fiberι t (ρ u))).isEmbedding.isInducing.specializes_iff] at h2
      exact (PrimeSpectrum.le_iff_specializes _ _).mpr h2
    have hmin : (Ideal.span {(f.stalkMap (f.fiberι t (ρ u))).hom π}).minimalPrimes = {p} := by
      ext q
      simp only [Set.mem_singleton_iff]
      constructor
      · intro hq
        have hpq := hpQ ⟨q, hq.1.1⟩ hq.1.2
        exact le_antisymm (hq.2 ⟨inferInstance, hIp⟩ hpq) hpq
      · rintro rfl
        exact ⟨⟨inferInstance, hIp⟩, fun q hq _ => hpQ ⟨q, hq.1⟩ hq.2⟩
    -- `t` generates the maximal ideal of the localization at `p`.
    let := σ.hom.toAlgebra
    have := isLocalization_stalkSpecializes hηx
    let e : Localization.AtPrime p ≃ₐ[X.presheaf.stalk (f.fiberι t (ρ u))]
        X.presheaf.stalk (f.fiberι t ξ) := IsLocalization.algEquiv p.primeCompl _ _
    have hmaxB' : maximalIdeal (X.presheaf.stalk (f.fiberι t ξ)) =
        Ideal.span {σ.hom ((f.stalkMap (f.fiberι t (ρ u))).hom π)} := by
      rw [hmaxB, ← map_maximalIdeal_stalkSpecializes_of_eq ((hfib ξ).trans hfx.symm)
        (hηx.map f.continuous), Ideal.map_map, ← CommRingCat.hom_comp,
        Scheme.Hom.stalkSpecializes_stalkMap, CommRingCat.hom_comp, ← Ideal.map_map, hI,
        Ideal.map_span, Set.image_singleton]
    have hmax : maximalIdeal (Localization.AtPrime p) =
        Ideal.span {algebraMap _ (Localization.AtPrime p)
          ((f.stalkMap (f.fiberι t (ρ u))).hom π)} := by
      have h1 : (maximalIdeal (X.presheaf.stalk (f.fiberι t ξ))).map
          (e.symm : X.presheaf.stalk (f.fiberι t ξ) ≃+* Localization.AtPrime p) =
            maximalIdeal (Localization.AtPrime p) :=
        IsLocalRing.eq_maximalIdeal (Ideal.map_isMaximal_of_equiv _)
      rw [← h1, hmaxB', Ideal.map_span, Set.image_singleton]
      congr 2
      exact e.symm.commutes _
    -- The quotient by `p` is the local ring of the reduced fibre, hence normal.
    let g := ρ ≫ f.fiberι t
    have hgsurj := g.stalkMap_surjective u
    have hrange : Set.range g = f ⁻¹' {t} := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Set.range_eq_univ.mpr hρsurj,
        Set.image_univ, Scheme.Hom.range_fiberι]
    have hiff : ∀ Q : Spec (X.presheaf.stalk (f.fiberι t (ρ u))),
        RingHom.ker (g.stalkMap u).hom ≤ Q.asIdeal ↔
          Ideal.span {(f.stalkMap (f.fiberι t (ρ u))).hom π} ≤ Q.asIdeal := by
      intro Q
      rw [ker_stalkMap_le_iff g u Q, hrange, hle]
      rfl
    have hKp : RingHom.ker (g.stalkMap u).hom = p := by
      have : (RingHom.ker (g.stalkMap u).hom).IsPrime := RingHom.ker_isPrime _
      apply le_antisymm
      · exact (hiff Pp).mpr hIp
      · exact hpQ ⟨_, this⟩ ((hiff ⟨_, this⟩).mp le_rfl)
    have hnormp : IsIntegrallyClosed (X.presheaf.stalk (f.fiberι t (ρ u)) ⧸ p) :=
      IsIntegrallyClosed.of_equiv
        ((Ideal.quotEquivOfEq hKp.symm).trans (RingHom.quotientKerEquivOfSurjective hgsurj)).symm
    -- Hironaka's lemma.
    obtain ⟨_, _⟩ := exists_algebra_essFiniteType_stalk φ (f.fiberι t (ρ u))
    have hp' : {q | Minimal (· ∈ associatedPrimes (X.presheaf.stalk (f.fiberι t (ρ u)))
        (X.presheaf.stalk (f.fiberι t (ρ u)) ⧸
          Ideal.span {(f.stalkMap (f.fiberι t (ρ u))).hom π})) q} = {p} := by
      rw [Hironaka.minimal_associatedPrimes_eq_minimalPrimes]
      exact hmin
    obtain ⟨hpτ, -⟩ := hironaka_normality_lemma (k := k) _ p hp' hmax hnormp
    -- Hence the local ring of the fibre is a domain.
    have hker : RingHom.ker ((f.fiberι t).stalkMap (ρ u)).hom = p := by
      rw [ker_stalkMap_fiberι, hI, ← hpτ]
    have hψsurj := (f.fiberι t).stalkMap_surjective (ρ u)
    have : (RingHom.ker ((f.fiberι t).stalkMap (ρ u)).hom).IsPrime := hker ▸ inferInstance
    exact isReduced_of_injective (RingHom.quotientKerEquivOfSurjective hψsurj).symm
      (RingHom.quotientKerEquivOfSurjective hψsurj).symm.injective
  exact isReduced_of_isReduced_stalk _

end NormalFamily

/-- **Hartshorne III.9, p. 263 (algebraic family of varieties).** Let `k` be an algebraically
closed field. A morphism `f : X ⟶ T` of `k`-schemes is an *algebraic family* of the varieties
`X^t` parametrized by `T` when `X` and `T` are varieties over `k` (integral, separated, of finite
type), `f` is surjective, and for every closed point `t ∈ T` the reduced fibre
`X^t = (X_t)_red` is irreducible of dimension `dim X - dim T` (stated additively as
`dim X^t + dim T = dim X`) and the scheme-theoretic fibre `X_t` is reduced at its generic
points. -/
structure IsAlgebraicFamily {k : Type u} [Field k] [IsAlgClosed k]
    {X T : Over (Spec (CommRingCat.of k))} (f : X ⟶ T) : Prop where
  isIntegral_source : IsIntegral X.left
  isSeparated_source : IsSeparated X.hom
  locallyOfFiniteType_source : LocallyOfFiniteType X.hom
  quasiCompact_source : QuasiCompact X.hom
  isIntegral_base : IsIntegral T.left
  isSeparated_base : IsSeparated T.hom
  locallyOfFiniteType_base : LocallyOfFiniteType T.hom
  quasiCompact_base : QuasiCompact T.hom
  surjective : Surjective f.left
  irreducibleSpace_reducedFiber :
    ∀ t : T.left, IsClosed {t} → IrreducibleSpace (reducedFiber f.left t)
  topologicalKrullDim_reducedFiber : ∀ t : T.left, IsClosed {t} →
    topologicalKrullDim (reducedFiber f.left t) + topologicalKrullDim T.left =
      topologicalKrullDim X.left
  isReduced_stalk_fiber : ∀ t : T.left, IsClosed {t} → ∀ ξ : f.left.fiber t,
    closure {ξ} ∈ irreducibleComponents (f.left.fiber t) →
      _root_.IsReduced ((f.left.fiber t).presheaf.stalk ξ)

/-- **Hartshorne III, Theorem 9.11.** Let `f : X ⟶ T` be an algebraic family of normal varieties
`X^t` parametrized by a nonsingular curve `T` (an integral scheme of dimension one whose local
rings are regular). Then every closed scheme-theoretic fibre `X_t` is reduced, so that it equals
the reduced fibre `X^t`, and `f` is flat. -/
theorem IsAlgebraicFamily.isReduced_fiber_and_flat {k : Type u} [Field k] [IsAlgClosed k]
    {X T : Over (Spec (CommRingCat.of k))} {f : X ⟶ T} (hf : IsAlgebraicFamily f)
    (hnorm : ∀ t : T.left, IsClosed {t} → IsNormal (reducedFiber f.left t))
    (hreg : ∀ t : T.left, IsRegularLocalRing (T.left.presheaf.stalk t))
    (hdim : topologicalKrullDim T.left = 1) :
    (∀ t : T.left, IsClosed {t} → IsReduced (f.left.fiber t)) ∧ Flat f.left := by
  have := hf.isIntegral_source
  have := hf.isIntegral_base
  have := hf.locallyOfFiniteType_source
  have := hf.locallyOfFiniteType_base
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : IsLocallyNoetherian T.left := LocallyOfFiniteType.isLocallyNoetherian T.hom
  refine ⟨fun t ht => ?_, ?_⟩
  · have hπ : ∀ y : T.left, (maximalIdeal (T.left.presheaf.stalk y)).IsPrincipal := fun y => by
      have := isBezout_stalk_of_isRegularLocalRing hreg hdim.le y
      exact IsPrincipalIdealRing.principal _
    exact NormalFamily.isReduced_fiber X.hom f.left t hπ
      (hf.irreducibleSpace_reducedFiber t ht) (hf.isReduced_stalk_fiber t ht) (hnorm t ht)
  · rw [flat_iff_forall_mem_irreducibleComponents_dense_image f.left hreg hdim]
    intro Z hZ
    rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hZ
    subst hZ
    rw [Set.image_univ, Set.range_eq_univ.mpr hf.surjective.surj]
    exact dense_univ

end Hartshorne

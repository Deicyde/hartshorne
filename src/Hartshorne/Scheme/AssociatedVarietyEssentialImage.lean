/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ProjectiveVarietyProj
import Hartshorne.Scheme.VarietyFunctorFullyFaithful
import Hartshorne.Scheme.GeneratedProjProjective
import Hartshorne.Morphism.OpenSubvariety

/-!
# Classical varieties and quasi-projective integral schemes

Hartshorne, *Algebraic Geometry*, II.4, Proposition 4.10 (pp. 104–105): for `k`
algebraically closed, the essential image of the functor `t` from varieties to
schemes over `k` is the class of quasi-projective integral schemes over `k`, and
projective varieties correspond to projective integral schemes.

## Reading of the statement

Hartshorne's `t` is defined on the category of classical varieties: affine,
quasi-affine, projective and quasi-projective varieties, i.e. (up to isomorphism)
the locally closed irreducible subsets of some `ℙⁿ`. The project's
`Hartshorne.varietyToSchemeFunctor` is defined on the larger category
`Hartshorne.SchemeVarietyCat` of abstract varieties with an affine-open basis,
which also contains e.g. the affine line with a doubled origin, whose associated
scheme is not separated. The faithful reading therefore restricts the functor to
the full subcategory of varieties isomorphic to a quasi-projective variety
(`Hartshorne.SchemeVarietyCat.isQuasiProjective`), respectively to a projective
variety (`Hartshorne.SchemeVarietyCat.isProjective`), and asks for the essential
image of the restricted functor.

## Status

This module proves the first inclusion of both clauses: an object of
`Over (Spec k)` in the essential image is integral, and its structure morphism
is quasi-projective (respectively projective).

* `t(V)` is integral for every variety `V`: its underlying space is irreducible
  (the generic point `V` lies in every nonempty open), and its sections are rings
  of `k`-valued functions, hence reduced.
* For a projective variety `Y`, `t(Y) ≅ Proj S(Y)` over `k`; `S(Y)` is generated
  in degree one over `S(Y)₀ = k`, so `Proj S(Y) → Spec k` is projective.
* For a quasi-projective variety `Y`, the inclusion of `Y` into its closure `Ȳ`
  (a projective variety in which `Y` is open) induces an open immersion
  `t(Y) → t(Ȳ)` over `k`, so `t(Y) → Spec k` is quasi-projective.

The converse inclusions (a projective, resp. quasi-projective, integral scheme
over `k` is isomorphic over `k` to `t(Y)` for a projective, resp.
quasi-projective, variety `Y`) are not proved here.

## Main definitions and results

* `Hartshorne.Variety.IsQuasiProjective`, `Hartshorne.Variety.IsProjective`
* `Hartshorne.SchemeVarietyCat.isQuasiProjective`, `Hartshorne.SchemeVarietyCat.isProjective`
* `Hartshorne.isIntegral_varietyAssociatedScheme`
* `Hartshorne.projective_structureMorphism_ofProjective`
* `Hartshorne.quasiProjective_structureMorphism_ofQuasiProjective`
* `Hartshorne.isIntegral_and_quasiProjective_of_mem_essImage`
* `Hartshorne.isIntegral_and_projective_of_mem_essImage`
-/

noncomputable section

open CategoryTheory TopologicalSpace Topology AlgebraicGeometry

namespace Hartshorne

universe u

variable {k : Type u} [Field k]

/-! ### Classical varieties -/

namespace Variety

/-- A variety is *quasi-projective* (a classical variety in Hartshorne's sense)
when it is isomorphic to a quasi-projective variety in some projective space. -/
def IsQuasiProjective (X : Variety.{u, u} k) : Prop :=
  ∃ (σ : Type u), Finite σ ∧ ∃ (Y : Set (ProjectiveSpace k σ)) (hY : IsQuasiProjVariety Y)
    (φ : VarietyHom X (Variety.ofQuasiProjective hY)), φ.IsIso

/-- A variety is *projective* when it is isomorphic to a projective variety in
some projective space. -/
def IsProjective (X : Variety.{u, u} k) : Prop :=
  ∃ (σ : Type u), Finite σ ∧ ∃ (Y : Set (ProjectiveSpace k σ)) (hY : IsProjVariety Y)
    (φ : VarietyHom X (Variety.ofProjective hY)), φ.IsIso

end Variety

/-! ### The associated scheme is integral -/

section Integral

variable (V : Variety.{u, u} k)

/-- The generic point `V` of the generic completion lies in every nonempty open. -/
theorem genericCompletion_top_mem_of_nonempty
    {s : Set (genericCompletionObj (TopCat.of V.carrier))} (hs : IsOpen s) (hne : s.Nonempty) :
    (⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩ :
      IrreducibleCloseds V.carrier) ∈ s := by
  obtain ⟨U, rfl⟩ := hs
  obtain ⟨Z, x, -, hxU⟩ := hne
  exact ⟨x, Set.mem_univ x, hxU⟩

instance irreducibleSpace_genericCompletionObj :
    IrreducibleSpace (genericCompletionObj (TopCat.of V.carrier)) := by
  let η : genericCompletionObj (TopCat.of V.carrier) :=
    (⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩ :
      IrreducibleCloseds V.carrier)
  have hdense : closure {η} = Set.univ :=
    ((dense_iff_inter_open (s := {η})).2 fun s hs hne =>
      ⟨η, genericCompletion_top_mem_of_nonempty V hs hne, rfl⟩).closure_eq
  rw [irreducibleSpace_def, Set.top_eq_univ, ← hdense]
  exact isIrreducible_singleton.closure

variable [IsAlgClosed k] (hV : V.HasAffineOpenBasis)

instance isReduced_varietyAssociatedScheme : IsReduced (varietyAssociatedScheme V hV) where
  component_reduced U := by
    change _root_.IsReduced (V.regular _)
    exact isReduced_of_injective (Subalgebra.val _) Subtype.val_injective

instance irreducibleSpace_varietyAssociatedScheme :
    IrreducibleSpace (varietyAssociatedScheme V hV) :=
  irreducibleSpace_genericCompletionObj V

/-- The scheme associated to a variety is integral. -/
instance isIntegral_varietyAssociatedScheme : IsIntegral (varietyAssociatedScheme V hV) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

end Integral

/-! ### Projective varieties give projective schemes -/

section Projective

variable {σ : Type u} {Y : Set (ProjectiveSpace k σ)}

/-- For nonempty `Y`, the degree-zero part of `S(Y)` is the field of constants. -/
theorem bijective_algebraMap_projCoordGrading_zero (hY : Y.Nonempty) :
    Function.Bijective (algebraMap k (projCoordGrading Y 0)) := by
  obtain ⟨y, hy⟩ := hY
  refine ⟨fun a b hab => ?_, fun x => ?_⟩
  · have h := congrArg (fun z : projCoordGrading Y 0 =>
      projCoordEval ⟨y, hy⟩ (z : homogeneousCoordinateRing Y)) hab
    simpa only [SetLike.GradeZero.coe_algebraMap, projCoordEval_algebraMap] using h
  · obtain ⟨x, p, hp, hpx⟩ := x
    have hp0 : p = MvPolynomial.C (MvPolynomial.coeff 0 p) :=
      MvPolynomial.totalDegree_eq_zero_iff_eq_C.1
        (Nat.le_zero.1 ((MvPolynomial.mem_homogeneousSubmodule 0 p).1 hp).totalDegree_le)
    refine ⟨MvPolynomial.coeff 0 p, Subtype.ext ?_⟩
    rw [SetLike.GradeZero.coe_algebraMap]
    change _ = x
    subst hpx
    conv_rhs => rw [hp0]
    rfl

/-- `S(Y)` is generated over its degree-zero part by the classes of the
coordinates, which have degree one. -/
theorem exists_degreeOne_generators_projCoordGrading [Finite σ]
    (Y : Set (ProjectiveSpace k σ)) :
    ∃ s : Finset (homogeneousCoordinateRing Y), (∀ x ∈ s, x ∈ projCoordGrading Y 1) ∧
      Algebra.adjoin (projCoordGrading Y 0) (s : Set (homogeneousCoordinateRing Y)) = ⊤ := by
  classical
  have := Fintype.ofFinite σ
  let s : Finset (homogeneousCoordinateRing Y) :=
    Finset.univ.image fun i => Ideal.Quotient.mk (projVanishingIdeal Y).toIdeal (MvPolynomial.X i)
  refine ⟨s, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
    exact mk_X_mem_projCoordGrading i Y
  · rw [eq_top_iff]
    rintro x -
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    induction p using MvPolynomial.induction_on with
    | C a =>
      have h : Ideal.Quotient.mk (projVanishingIdeal Y).toIdeal (MvPolynomial.C a) =
          algebraMap (projCoordGrading Y 0) (homogeneousCoordinateRing Y)
            (algebraMap k (projCoordGrading Y 0) a) := by
        change _ = ((algebraMap k (projCoordGrading Y 0) a : projCoordGrading Y 0) :
          homogeneousCoordinateRing Y)
        rw [SetLike.GradeZero.coe_algebraMap]
        rfl
      rw [h]
      exact Subalgebra.algebraMap_mem _ _
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul]
      exact mul_mem hp (Algebra.subset_adjoin (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩))

variable [IsAlgClosed k] [Finite σ] [DecidableEq σ] [Nonempty σ]

/-- **Hartshorne II, Proposition 4.10, projective case, first half.** The scheme
associated to a projective variety is projective over `k`. -/
theorem projective_structureMorphism_ofProjective (hY : IsProjVariety Y) :
    Projective (varietyAssociatedSchemeStructureMorphism (Variety.ofProjective hY)
      (Variety.hasAffineOpenBasis_ofProjective hY)) := by
  rw [← projectiveVarietyAssociatedSchemeIsoProj_hom_comp_structureMorphism hY]
  refine (MorphismProperty.cancel_left_of_respectsIso Projective _ _).2 ?_
  have : IsIso (CommRingCat.ofHom (algebraMap k (projCoordGrading Y 0))) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      (bijective_algebraMap_projCoordGrading_zero hY.1.nonempty)
  exact (MorphismProperty.cancel_right_of_respectsIso Projective _ _).2
    (projective_projToSpecZero_of_degreeOne_generators _
      (exists_degreeOne_generators_projCoordGrading Y))

end Projective

/-! ### Quasi-projective varieties give quasi-projective schemes -/

section QuasiProjective

variable {σ : Type u} {Y : Set (ProjectiveSpace k σ)}

/-- The closure of a quasi-projective variety is a projective variety. -/
theorem IsQuasiProjVariety.isProjVariety_closure (hY : IsQuasiProjVariety Y) :
    IsProjVariety (closure Y) :=
  ⟨hY.isIrreducible.closure, isClosed_closure⟩

/-- A quasi-projective variety is open in its closure. -/
theorem IsQuasiProjVariety.isOpen_in_closure (hY : IsQuasiProjVariety Y) :
    IsOpen {y : closure Y | y.1 ∈ Y} := by
  obtain ⟨-, V, U, hV, hU, rfl⟩ := hY
  have hcl : closure (V ∩ U) ⊆ V := closure_minimal Set.inter_subset_left hV.2
  have hset : {y : closure (V ∩ U) | y.1 ∈ V ∩ U} = Subtype.val ⁻¹' U := by
    ext y
    exact ⟨fun hy => hy.2, fun hy => ⟨hcl y.2, hy⟩⟩
  rw [hset]
  exact hU.preimage continuous_subtype_val

/-- The inclusion of a quasi-projective variety into its closure. -/
abbrev closureInclHom (hY : IsQuasiProjVariety Y) :
    VarietyHom (Variety.ofQuasiProjective hY)
      (Variety.ofProjective hY.isProjVariety_closure) :=
  inclHom hY.isProjVariety_closure.isQuasiProjVariety hY subset_closure

theorem isOpenEmbedding_closureInclHom (hY : IsQuasiProjVariety Y) :
    IsOpenEmbedding (closureInclHom hY) := by
  refine ⟨?_, ?_⟩
  · refine (Topology.IsEmbedding.subtypeVal.of_comp_iff).1 ?_
    exact Topology.IsEmbedding.subtypeVal (p := fun x : ProjectiveSpace k σ => x ∈ Y)
  · have hrange : Set.range (closureInclHom hY) = {y : closure Y | y.1 ∈ Y} := by
      ext y
      exact ⟨fun ⟨x, hx⟩ => hx ▸ x.2, fun hy => ⟨⟨y.1, hy⟩, rfl⟩⟩
    rw [hrange]
    exact hY.isOpen_in_closure

/-- Regular functions on open subsets of `Y` are regular on the same subsets of
the closure. -/
theorem closureInclHom_descends (hY : IsQuasiProjVariety Y)
    (O : Opens (Variety.ofProjective hY.isProjVariety_closure).carrier)
    (hO : (O : Set (Variety.ofProjective hY.isProjVariety_closure).carrier) ⊆
      Set.range (closureInclHom hY))
    (h : (Variety.ofQuasiProjective hY).regular
      (Opens.comap ⟨closureInclHom hY, (closureInclHom hY).continuous_toFun⟩ O)) :
    ∃ f : (Variety.ofProjective hY.isProjVariety_closure).regular O,
      ∀ w : Opens.comap ⟨closureInclHom hY, (closureInclHom hY).continuous_toFun⟩ O,
        f.1 ⟨closureInclHom hY w.1, w.2⟩ = h.1 w := by
  have hV : ∀ y : (Variety.ofProjective hY.isProjVariety_closure).carrier,
      y ∈ O ↔ ∃ hy : y.1 ∈ Y, (⟨y.1, hy⟩ : Y) ∈
        Opens.comap ⟨closureInclHom hY, (closureInclHom hY).continuous_toFun⟩ O := by
    intro y
    refine ⟨fun hyO => ?_, fun ⟨hy, hyO⟩ => hyO⟩
    obtain ⟨x, hx⟩ := hO hyO
    have hy : y.1 ∈ Y := hx ▸ x.2
    refine ⟨hy, ?_⟩
    have hgy : (closureInclHom hY).toFun ⟨y.1, hy⟩ = y := Subtype.ext rfl
    change (closureInclHom hY).toFun ⟨y.1, hy⟩ ∈ O
    rw [hgy]
    exact hyO
  refine ⟨⟨_, regular_pullPoint hY.isProjVariety_closure.isQuasiProjVariety hY hV h.1 h.2⟩,
    fun w => ?_⟩
  exact congrArg h.1 (Subtype.ext rfl)

variable [IsAlgClosed k] [Finite σ] [DecidableEq σ] [Nonempty σ]

/-- The inclusion of a quasi-projective variety into its closure induces an open
immersion of associated schemes. -/
instance isOpenImmersion_closureInclHom (hY : IsQuasiProjVariety Y) :
    IsOpenImmersion ((closureInclHom hY).associatedSchemeHom
      (Variety.hasAffineOpenBasis_ofQuasiProjective hY)
      (Variety.hasAffineOpenBasis_ofProjective hY.isProjVariety_closure)) :=
  (closureInclHom hY).isOpenImmersion_genericCompletionHom (isOpenEmbedding_closureInclHom hY)
    (closureInclHom_descends hY)

/-- **Hartshorne II, Proposition 4.10, first half.** The scheme associated to a
quasi-projective variety is quasi-projective over `k`. -/
theorem quasiProjective_structureMorphism_ofQuasiProjective (hY : IsQuasiProjVariety Y) :
    QuasiProjective (varietyAssociatedSchemeStructureMorphism (Variety.ofQuasiProjective hY)
      (Variety.hasAffineOpenBasis_ofQuasiProjective hY)) := by
  exact QuasiProjective.mk _ _
    (projective_structureMorphism_ofProjective hY.isProjVariety_closure)
    ((closureInclHom hY).associatedSchemeHom_comp_structureMorphism _ _)

end QuasiProjective

/-! ### The essential images -/

section EssImage

/-- The quasi-projective (classical) varieties among varieties with an
affine-open basis. -/
def SchemeVarietyCat.isQuasiProjective : ObjectProperty (SchemeVarietyCat k) :=
  fun X => X.toVariety.IsQuasiProjective

/-- The projective varieties among varieties with an affine-open basis. -/
def SchemeVarietyCat.isProjective : ObjectProperty (SchemeVarietyCat k) :=
  fun X => X.toVariety.IsProjective

/-- A nonempty subset of projective space forces the coordinate index type to be
nonempty. -/
theorem nonempty_of_projectiveSpace_nonempty {σ : Type u} {Y : Set (ProjectiveSpace k σ)}
    (hY : Y.Nonempty) : Nonempty σ := by
  obtain ⟨y, -⟩ := hY
  by_contra hσ
  rw [not_nonempty_iff] at hσ
  exact y.rep_nonzero (Subsingleton.elim _ _)

/-- An isomorphism of varieties is an isomorphism in the source category. -/
def SchemeVarietyCat.isoOfIsIso {X W : SchemeVarietyCat k}
    (φ : VarietyHom X.toVariety W.toVariety) (hφ : φ.IsIso) : X ≅ W where
  hom := φ
  inv := hφ.choose
  hom_inv_id := hφ.choose_spec.1
  inv_hom_id := hφ.choose_spec.2

variable [IsAlgClosed k]

/-- Transport of integrality and of a property of the structure morphism along an
isomorphism in `Over (Spec k)`. -/
theorem isIntegral_and_of_iso_varietyToSchemeFunctor_obj (P : MorphismProperty Scheme.{u})
    [P.RespectsIso]
    {V : SchemeVarietyCat k} {X : Over (Spec (CommRingCat.of k))}
    (e : (varietyToSchemeFunctor k).obj V ≅ X)
    (hP : P (varietyAssociatedSchemeStructureMorphism V.toVariety V.hasAffineOpenBasis)) :
    IsIntegral X.left ∧ P X.hom := by
  have : IsIso e.inv.left := (Over.forget _).map_isIso e.inv
  have : IsIntegral ((varietyToSchemeFunctor k).obj V).left :=
    isIntegral_varietyAssociatedScheme V.toVariety V.hasAffineOpenBasis
  have : Nonempty X.left := ⟨e.hom.left (IsIntegral.nonempty (X := _)).some⟩
  refine ⟨isIntegral_of_isOpenImmersion e.inv.left, ?_⟩
  rw [← Over.w e.inv]
  exact (MorphismProperty.cancel_left_of_respectsIso P _ _).2 hP

/-- **Hartshorne II, Proposition 4.10, first half.** Every scheme isomorphic over
`k` to the scheme of a quasi-projective variety is integral and quasi-projective
over `k`. -/
theorem isIntegral_and_quasiProjective_of_mem_essImage {X : Over (Spec (CommRingCat.of k))}
    (hX : (SchemeVarietyCat.isQuasiProjective.ι ⋙ varietyToSchemeFunctor k).essImage X) :
    IsIntegral X.left ∧ QuasiProjective X.hom := by
  classical
  obtain ⟨⟨V, σ, hσ, Y, hY, φ, hφ⟩, ⟨e⟩⟩ := hX
  have := nonempty_of_projectiveSpace_nonempty hY.1
  let W : SchemeVarietyCat k :=
    ⟨Variety.ofQuasiProjective hY, Variety.hasAffineOpenBasis_ofQuasiProjective hY⟩
  let E :=
    ((varietyToSchemeFunctor k).mapIso (SchemeVarietyCat.isoOfIsIso (W := W) φ hφ)).symm ≪≫ e
  exact isIntegral_and_of_iso_varietyToSchemeFunctor_obj QuasiProjective E
    (quasiProjective_structureMorphism_ofQuasiProjective hY)

/-- **Hartshorne II, Proposition 4.10, projective case, first half.** Every
scheme isomorphic over `k` to the scheme of a projective variety is integral and
projective over `k`. -/
theorem isIntegral_and_projective_of_mem_essImage {X : Over (Spec (CommRingCat.of k))}
    (hX : (SchemeVarietyCat.isProjective.ι ⋙ varietyToSchemeFunctor k).essImage X) :
    IsIntegral X.left ∧ Projective X.hom := by
  classical
  obtain ⟨⟨V, σ, hσ, Y, hY, φ, hφ⟩, ⟨e⟩⟩ := hX
  have := nonempty_of_projectiveSpace_nonempty hY.1.nonempty
  let W : SchemeVarietyCat k :=
    ⟨Variety.ofProjective hY, Variety.hasAffineOpenBasis_ofProjective hY⟩
  let E :=
    ((varietyToSchemeFunctor k).mapIso (SchemeVarietyCat.isoOfIsIso (W := W) φ hφ)).symm ≪≫ e
  exact isIntegral_and_of_iso_varietyToSchemeFunctor_obj Projective E
    (projective_structureMorphism_ofProjective hY)

end EssImage

end Hartshorne

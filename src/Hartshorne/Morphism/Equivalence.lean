/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.AffineIso
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Corollary 3.8: affine varieties and finitely generated domains

Hartshorne, *Algebraic Geometry*, I.3, Corollary 3.8 (p. 20).

`X ↦ A(X)` is an arrow-reversing equivalence between the affine varieties over
`k` and the finitely generated integral domains over `k`.

All the mathematics is already in place. Fully faithful is Proposition 3.5 with
`X` affine, composed with `A(X) ≅ 𝒪(X)`; essentially surjective is the
realization theorem of §1. What this file adds is the categories, the functor,
and the bookkeeping that turns those two facts into an equivalence.

## The two categories

Affine varieties get a bespoke structure: an object is an affine variety in
some `𝔸ⁿ`, which is Hartshorne's category verbatim, and morphisms are
`VarietyHom`s. Restricting the ambient space to `Fin n` rather than an arbitrary
finite index type is not a loss — it is what the realization theorem produces,
and it keeps every carrier in one universe.

Finitely generated domains are a full subcategory of Mathlib's `CommAlgCat k`,
so the algebra maps, identities and composition come from upstream.

## Main definitions

* `Hartshorne.AffineVarietyCat`, `Hartshorne.FgDomainCat`
-/

namespace Hartshorne

open CategoryTheory MvPolynomial TopologicalSpace

universe u

variable (k : Type u) [Field k]

/-- An object of the category of affine varieties over `k`: an affine variety
sitting in some `𝔸ⁿ`. -/
structure AffineVarietyCat where
  /-- The dimension of the ambient affine space, not of the variety. -/
  ambient : ℕ
  /-- The variety itself. -/
  carrier : Set (Fin ambient → k)
  /-- Which is affine: irreducible and closed. -/
  isAffine : IsAffineVariety carrier

/-- Being a finitely generated integral domain, as a property of a
`k`-algebra. -/
def IsFgDomain : ObjectProperty (CommAlgCat.{u} k) :=
  fun A => IsDomain A ∧ Algebra.FiniteType k A

/-- The category of finitely generated integral domains over `k`, as a full
subcategory of the `k`-algebras. -/
abbrev FgDomainCat := (IsFgDomain k).FullSubcategory

namespace AffineVarietyCat

variable {k}

/-- The bundled variety attached to an object. -/
noncomputable def toVariety (X : AffineVarietyCat k) : Variety.{u, u} k :=
  Variety.ofQuasiAffine X.isAffine.isQuasiAffineVariety

/-- Morphisms of affine varieties are morphisms of the underlying varieties.
Associativity and the unit laws are the ones already proved for `VarietyHom`. -/
noncomputable instance : Category (AffineVarietyCat k) where
  Hom X Y := VarietyHom X.toVariety Y.toVariety
  id _ := VarietyHom.id _
  comp f g := g.comp f
  id_comp f := VarietyHom.comp_id f
  comp_id f := VarietyHom.id_comp f
  assoc f g h := (VarietyHom.comp_assoc h g f).symm

@[simp]
theorem id_def (X : AffineVarietyCat k) : (𝟙 X : X ⟶ X) = VarietyHom.id X.toVariety := rfl

@[simp]
theorem comp_def {X Y Z : AffineVarietyCat k} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ≫ g = VarietyHom.comp g f := rfl

variable [IsAlgClosed k]

/-- **Theorem 3.2(a)** for an object of the category: `A(X) ≅ 𝒪(X)`.

Phrased through `toVariety` rather than through `Variety.ofQuasiAffine`
directly, so that it composes with `VarietyHom.pullback` without unfolding. -/
noncomputable def coordEquiv (X : AffineVarietyCat k) :
    coordinateRing X.carrier ≃ₐ[k] X.toVariety.regular ⊤ :=
  coordinateRingEquivRegularTop X.isAffine

/-- `A(X)`, as an object of the category of finitely generated domains. -/
noncomputable def coordObj (X : AffineVarietyCat k) : FgDomainCat k where
  obj := CommAlgCat.of k (coordinateRing X.carrier)
  property := ⟨isDomain_coordinateRing X.isAffine, inferInstance⟩

/-- The algebra map `A(Y) → A(X)` induced by a morphism `X → Y`: pull regular
functions back, and read both ends through `A ≅ 𝒪`. -/
noncomputable def coordMap {X Y : AffineVarietyCat k} (f : X ⟶ Y) :
    coordinateRing Y.carrier →ₐ[k] coordinateRing X.carrier :=
  X.coordEquiv.symm.toAlgHom.comp ((VarietyHom.pullback f).comp Y.coordEquiv.toAlgHom)

theorem coordMap_apply {X Y : AffineVarietyCat k} (f : X ⟶ Y)
    (a : coordinateRing Y.carrier) :
    coordMap f a = X.coordEquiv.symm (VarietyHom.pullback f (Y.coordEquiv a)) :=
  rfl

theorem coordMap_id (X : AffineVarietyCat k) :
    coordMap (𝟙 X) = AlgHom.id k (coordinateRing X.carrier) := by
  ext a
  have hp : VarietyHom.pullback (𝟙 X : X ⟶ X) (X.coordEquiv a) = X.coordEquiv a := rfl
  rw [coordMap_apply, hp]
  simp

theorem coordMap_comp {X Y Z : AffineVarietyCat k} (f : X ⟶ Y) (g : Y ⟶ Z) :
    coordMap (f ≫ g) = (coordMap f).comp (coordMap g) := by
  ext a
  rw [AlgHom.comp_apply, coordMap_apply, coordMap_apply, coordMap_apply,
    AlgEquiv.apply_symm_apply]
  rfl

/-- **Proposition 3.5** for objects of the category. -/
noncomputable def homEquivCoord (X Y : AffineVarietyCat k) :
    (X ⟶ Y) ≃ (coordinateRing Y.carrier →ₐ[k] X.toVariety.regular ⊤) :=
  homEquivAlgHom Y.isAffine

theorem homEquivCoord_apply {X Y : AffineVarietyCat k} (f : X ⟶ Y) :
    homEquivCoord X Y f = (VarietyHom.pullback f).comp Y.coordEquiv.toAlgHom :=
  homToAlgHom_eq_pullback_comp Y.isAffine f

theorem coordMap_injective {X Y : AffineVarietyCat k} :
    Function.Injective (coordMap (X := X) (Y := Y)) := by
  intro f g h
  refine (homEquivCoord X Y).injective ?_
  rw [homEquivCoord_apply, homEquivCoord_apply]
  exact AlgHom.ext fun a => X.coordEquiv.symm.injective (congrArg (fun φ => φ a) h)

/-- Every algebra map between coordinate rings comes from a morphism, produced
by Proposition 3.5. -/
theorem exists_coordMap_eq {X Y : AffineVarietyCat k}
    (ψ : coordinateRing Y.carrier →ₐ[k] coordinateRing X.carrier) :
    ∃ f : X ⟶ Y, coordMap f = ψ := by
  refine ⟨(homEquivCoord X Y).symm (X.coordEquiv.toAlgHom.comp ψ), ?_⟩
  have hh := (homEquivCoord X Y).apply_symm_apply (X.coordEquiv.toAlgHom.comp ψ)
  rw [homEquivCoord_apply] at hh
  ext a
  have hpt : VarietyHom.pullback ((homEquivCoord X Y).symm (X.coordEquiv.toAlgHom.comp ψ))
      (Y.coordEquiv a) = X.coordEquiv (ψ a) := congrArg (fun φ => φ a) hh
  rw [coordMap_apply, hpt]
  simp

end AffineVarietyCat

open AffineVarietyCat

variable {k}

variable (k) in
/-- **The coordinate ring functor** `X ↦ A(X)`, arrow-reversing.

Functoriality is functoriality of pullback of regular functions, which is
`rfl`; the two `A ≅ 𝒪` conversions at the ends cancel. -/
noncomputable def coordFunctor [IsAlgClosed k] :
    (AffineVarietyCat k)ᵒᵖ ⥤ FgDomainCat k where
  obj X := coordObj X.unop
  map f := ObjectProperty.homMk (CommAlgCat.ofHom (coordMap f.unop))
  map_id X := by
    apply ObjectProperty.hom_ext
    show CommAlgCat.ofHom (coordMap (𝟙 X.unop)) = _
    rw [coordMap_id]
    rfl
  map_comp f g := by
    apply ObjectProperty.hom_ext
    show CommAlgCat.ofHom (coordMap (g.unop ≫ f.unop)) = _
    rw [coordMap_comp]
    rfl

instance faithful_coordFunctor [IsAlgClosed k] : (coordFunctor k).Faithful where
  map_injective {X Y} {f g} h := by
    refine Quiver.Hom.unop_inj (coordMap_injective ?_)
    exact congrArg (fun m => CommAlgCat.Hom.hom (InducedCategory.Hom.hom m)) h

instance full_coordFunctor [IsAlgClosed k] : (coordFunctor k).Full where
  map_surjective {X Y} ψ := by
    obtain ⟨f, hf⟩ := exists_coordMap_eq (CommAlgCat.Hom.hom (InducedCategory.Hom.hom ψ))
    refine ⟨f.op, ?_⟩
    apply ObjectProperty.hom_ext
    show CommAlgCat.ofHom (coordMap f) = _
    rw [hf]
    rfl

instance essSurj_coordFunctor [IsAlgClosed k] : (coordFunctor k).EssSurj where
  mem_essImage B := by
    obtain ⟨hdom, hft⟩ := B.property
    obtain ⟨n, Y, hY, ⟨e⟩⟩ :=
      exists_isAffineVariety_coordinateRing_equiv (k := k) (B := B.obj.carrier)
    exact ⟨Opposite.op ⟨n, Y, hY⟩, ⟨ObjectProperty.isoMk _ (CommAlgCat.isoMk e)⟩⟩

instance isEquivalence_coordFunctor [IsAlgClosed k] : (coordFunctor k).IsEquivalence where

/-- **Corollary 3.8**: `X ↦ A(X)` is an arrow-reversing equivalence between
affine varieties over `k` and finitely generated integral domains over `k`. -/
noncomputable def coordEquivalence [IsAlgClosed k] :
    (AffineVarietyCat k)ᵒᵖ ≌ FgDomainCat k :=
  (coordFunctor k).asEquivalence

end Hartshorne

/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ProjectiveBundle
import Hartshorne.Scheme.SegreProductGradedAlgebra

/-!
# Twisting a quasi-coherent graded algebra by an invertible sheaf

Hartshorne, *Algebraic Geometry*, II.7, Lemma 7.9 (p. 161): for a quasi-coherent sheaf of graded
`𝒪_X`-algebras `S` and an invertible sheaf `L` on `X`, put `(S · L)_d = S_d ⊗ L^d`.

## The diagonal product of two quasi-coherent graded algebras

For quasi-coherent graded `𝒪_X`-algebras `S` and `T` (recorded on the affine opens of `X`, see
`Hartshorne.QuasiCoherentGradedAlgebra`), the *diagonal product* `S ×_X T` has sections
`(S ×_X T)(U) = ⊕_d S(U)_d ⊗_{Γ(U, 𝒪_X)} T(U)_d` over an affine open `U`
(`Hartshorne.SegreProduct.diagonal`), with restriction maps `s ⊗ t ↦ s|_{D(r)} ⊗ t|_{D(r)}`.
Restriction to a basic open `D(r)` is the localization at `r`
(`Hartshorne.SegreProduct.isLocalizationAway_diagonalMap`), so `S ×_X T` is again a
quasi-coherent graded `𝒪_X`-algebra (`Hartshorne.QuasiCoherentGradedAlgebra.diagonalProduct`).

## The twist `S · L`

The graded algebra `S · L` is the diagonal product of `S` with the symmetric algebra
`Sym(L) = ⊕_d Sym^d(L)` of `L` (`AlgebraicGeometry.Scheme.Modules.symmetricGradedAlgebra`), whose
degree-`d` part `Sym^d(L)` is the `d`-th power of the invertible sheaf `L`
(`Hartshorne.QuasiCoherentGradedAlgebra.lineBundleTwist`).
-/

universe u

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry TensorProduct

namespace Hartshorne

namespace QuasiCoherentGradedAlgebra

open Scheme.AffineZariskiSite

variable {X : Scheme.{u}} (S T : QuasiCoherentGradedAlgebra X)

/-- The `Γ(U, 𝒪_X)`-algebra structure of `S(U)` given by the structure map. -/
@[instance_reducible]
def sectionsAlgebra (U : X.AffineZariskiSite) : Algebra Γ(X, U.1) (S.obj.obj (.op U)) :=
  (S.structureMap.app (.op U)).hom.toAlgebra

attribute [local instance] sectionsAlgebra

theorem algebraMap_sections_mem (U : X.AffineZariskiSite) (a : Γ(X, U.1)) :
    algebraMap Γ(X, U.1) (S.obj.obj (.op U)) a ∈ S.grading U 0 :=
  S.structureMap_mem U a

variable {S} in
/-- The restriction `Γ(V, 𝒪_X) → Γ(U, 𝒪_X)` along an arrow `U ⟶ V` of affine opens. -/
abbrev baseRestrict {U V : X.AffineZariskiSite} (f : U ⟶ V) : Γ(X, V.1) →+* Γ(X, U.1) :=
  (X.presheaf.map ((toOpensFunctor X).map f).op).hom

theorem restrict_algebraMap {U V : X.AffineZariskiSite} (f : U ⟶ V) (a : Γ(X, V.1)) :
    S.restrict f (algebraMap Γ(X, V.1) (S.obj.obj (.op V)) a) =
      algebraMap Γ(X, U.1) (S.obj.obj (.op U)) (baseRestrict f a) :=
  congr($(S.structureMap.naturality f.op) a).symm

/-- The sections `(S ×_X T)(U) = ⊕_d S(U)_d ⊗_{Γ(U, 𝒪_X)} T(U)_d` of the diagonal product over an
affine open `U`. -/
abbrev diagonalSections (U : X.AffineZariskiSite) :
    Subalgebra Γ(X, U.1) (S.obj.obj (.op U) ⊗[Γ(X, U.1)] T.obj.obj (.op U)) :=
  SegreProduct.diagonal Γ(X, U.1) (S.grading U) (T.grading U)

/-- The restriction maps of the diagonal product. -/
def diagonalRestrict {U V : X.AffineZariskiSite} (f : U ⟶ V) :
    S.diagonalSections T V →+* S.diagonalSections T U :=
  SegreProduct.diagonalMap (baseRestrict f) (S.restrict f)
    (T.restrict f) (S.restrict_algebraMap f) (T.restrict_algebraMap f)

/-- The structure map `Γ(U, 𝒪_X) → (S ×_X T)(U)`, `a ↦ a ⊗ 1`. -/
def diagonalAlgebraMap (U : X.AffineZariskiSite) : Γ(X, U.1) →+* S.diagonalSections T U :=
  algebraMap _ _

/-- The functor `U ↦ (S ×_X T)(U)` on affine opens. -/
def diagonalFunctor : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u} where
  obj U := CommRingCat.of (S.diagonalSections T U.unop)
  map f := CommRingCat.ofHom (S.diagonalRestrict T f.unop)
  map_id U := by
    refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    change S.diagonalRestrict T (𝟙 U.unop) x = x
    refine SegreProduct.diagonalMap_id _ _ _ _ _ (fun s => ?_) (fun t => ?_) x
    · change S.obj.map (𝟙 U.unop).op s = s
      simp
    · change T.obj.map (𝟙 U.unop).op t = t
      simp
  map_comp f g := by
    refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    change S.diagonalRestrict T (g.unop ≫ f.unop) x =
      S.diagonalRestrict T g.unop (S.diagonalRestrict T f.unop x)
    refine SegreProduct.diagonalMap_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun s => ?_)
      (fun t => ?_) x
    · change S.obj.map (g.unop ≫ f.unop).op s = S.obj.map g.unop.op (S.obj.map f.unop.op s)
      simp
    · change T.obj.map (g.unop ≫ f.unop).op t = T.obj.map g.unop.op (T.obj.map f.unop.op t)
      simp

/-- The structure maps `Γ(U, 𝒪_X) → (S ×_X T)(U)`. -/
def diagonalStructureMap : (toOpensFunctor X).op ⋙ X.presheaf ⟶ S.diagonalFunctor T where
  app U := CommRingCat.ofHom (S.diagonalAlgebraMap T U.unop)
  naturality U V f := by
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    change algebraMap Γ(X, V.unop.1) (S.diagonalSections T V.unop) (baseRestrict f.unop a) =
      S.diagonalRestrict T f.unop (algebraMap Γ(X, U.unop.1) (S.diagonalSections T U.unop) a)
    exact (SegreProduct.diagonalMap_algebraMap (A := Γ(X, U.unop.1))
      (S := S.obj.obj (.op U.unop)) (T := T.obj.obj (.op U.unop)) (baseRestrict f.unop)
      (S.restrict f.unop) (T.restrict f.unop) (S.restrict_algebraMap _) (T.restrict_algebraMap _)
      a).symm

theorem diagonalStructureMap_coequifibered : (S.diagonalStructureMap T).Coequifibered := by
  refine coequifibered_iff_forall_isLocalizationAway.mpr fun U r => ?_
  exact SegreProduct.isLocalizationAway_diagonalMap (A := Γ(X, U.1)) (S := S.obj.obj (.op U))
    (T := T.obj.obj (.op U)) (baseRestrict (homOfLE (U.basicOpen_le r)))
    (S.restrict (homOfLE (U.basicOpen_le r))) (T.restrict (homOfLE (U.basicOpen_le r)))
    (S.restrict_algebraMap _) (T.restrict_algebraMap _) r (S.algebraMap_sections_mem U)
    (T.algebraMap_sections_mem U) (S.algebraMap_sections_mem _) (T.algebraMap_sections_mem _)
    (U.2.isLocalization_basicOpen r) (S.isLocalizationAway U r) (T.isLocalizationAway U r)

/-- **The diagonal product** `S ×_X T` of two quasi-coherent graded `𝒪_X`-algebras: over an affine
open `U` its sections are `⊕_d S(U)_d ⊗_{Γ(U, 𝒪_X)} T(U)_d`, graded by `d`. -/
def diagonalProduct : QuasiCoherentGradedAlgebra X where
  obj := S.diagonalFunctor T
  structureMap := S.diagonalStructureMap T
  coequifibered := S.diagonalStructureMap_coequifibered T
  grading U := SegreProduct.grading Γ(X, U.1) (S.grading U) (T.grading U)
  gradedRing U := SegreProduct.gradedRing Γ(X, U.1) (S.grading U) (T.grading U)
    (S.algebraMap_sections_mem U) (T.algebraMap_sections_mem U)
  map_mem _ _ _ hx := SegreProduct.diagonalMap_mem_grading _ _ _ _ _ hx
  structureMap_mem _ r := SegreProduct.algebraMap_mem_grading _ _ r

theorem diagonalProduct_obj_obj (U : X.AffineZariskiSite) :
    (S.diagonalProduct T).obj.obj (.op U) = CommRingCat.of (S.diagonalSections T U) :=
  rfl

theorem mem_diagonalProduct_grading {U : X.AffineZariskiSite} {d : ℕ}
    {x : S.diagonalSections T U} :
    x ∈ (S.diagonalProduct T).grading U d ↔
      (x : S.obj.obj (.op U) ⊗[Γ(X, U.1)] T.obj.obj (.op U)) ∈
        SegreProduct.component Γ(X, U.1) (S.grading U) (T.grading U) d :=
  SegreProduct.mem_grading_iff

/-- **The twist `S · L`** of a quasi-coherent graded `𝒪_X`-algebra `S` by an invertible sheaf `L`
(Hartshorne II.7, Lemma 7.9): the diagonal product of `S` with `Sym(L) = ⊕_d Sym^d(L)`, so that
`(S · L)_d = S_d ⊗ Sym^d(L)`, where `Sym^d(L)` is the `d`-th power of `L`. -/
def lineBundleTwist (L : X.Modules) (hL : L.IsInvertible) : QuasiCoherentGradedAlgebra X :=
  S.diagonalProduct (Scheme.Modules.symmetricGradedAlgebra (E := L)
    ((Scheme.Modules.isInvertible_iff L).1 hL).1
    (fun x => by rw [((Scheme.Modules.isInvertible_iff L).1 hL).2 x]; exact Cardinal.one_lt_aleph0))

end QuasiCoherentGradedAlgebra

end Hartshorne

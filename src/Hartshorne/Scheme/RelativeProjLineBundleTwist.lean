/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ProjectiveBundle
import Hartshorne.Scheme.SegreProductTrivialization
import Hartshorne.RingedSpace.PicardGroup

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

variable (L : X.Modules) (hL : L.IsInvertible)

include hL in
theorem isLocallyFree_of_isInvertible : L.IsLocallyFree :=
  ((Scheme.Modules.isInvertible_iff L).1 hL).1

include hL in
theorem rankAt_lt_of_isInvertible (x : X) : L.rankAt x < Cardinal.aleph0 := by
  rw [((Scheme.Modules.isInvertible_iff L).1 hL).2 x]
  exact Cardinal.one_lt_aleph0

/-- The symmetric algebra `Sym(L) = ⊕_d Sym^d(L)` of an invertible sheaf `L`, as a quasi-coherent
graded `𝒪_X`-algebra; `Sym^d(L)` is the `d`-th power of `L`. -/
abbrev lineBundleSym : QuasiCoherentGradedAlgebra X :=
  Scheme.Modules.symmetricGradedAlgebra (E := L) (isLocallyFree_of_isInvertible L hL)
    (rankAt_lt_of_isInvertible L hL)

/-- **The twist `S · L`** of a quasi-coherent graded `𝒪_X`-algebra `S` by an invertible sheaf `L`
(Hartshorne II.7, Lemma 7.9): the diagonal product of `S` with `Sym(L) = ⊕_d Sym^d(L)`, so that
`(S · L)_d = S_d ⊗ Sym^d(L)`, where `Sym^d(L)` is the `d`-th power of `L`. -/
def lineBundleTwist : QuasiCoherentGradedAlgebra X :=
  S.diagonalProduct (lineBundleSym L hL)

/-! ### The local isomorphism over an affine open with a frame of `L` -/

attribute [local instance] MvPolynomial.gradedAlgebra

variable {L hL} {U : X.AffineZariskiSite} {e : ULift.{u} (Fin 1) → Γ(L, U.1)}

/-- The section `t ∈ Γ(U, Sym¹ L)` given by a frame `e` of `L` over `U`. -/
abbrev frameGenerator (e : ULift.{u} (Fin 1) → Γ(L, U.1)) : (lineBundleSym L hL).obj.obj (.op U) :=
  Scheme.Modules.frameGradedHom (isLocallyFree_of_isInvertible L hL)
    (rankAt_lt_of_isInvertible L hL) U.2 (n := 0) e (MvPolynomial.X 0)

theorem frameGenerator_mem : frameGenerator (hL := hL) e ∈ (lineBundleSym L hL).grading U 1 :=
  (Scheme.Modules.frameGradedHom _ _ U.2 (n := 0) e).map_mem
    ((MvPolynomial.mem_homogeneousSubmodule 1 _).2 (MvPolynomial.isHomogeneous_X _ _))

theorem frameGenerator_free (he : Ringed.IsLocalFrame (R := X.sheaf) L U.1 e) :
    ∀ d, ∀ x ∈ (lineBundleSym L hL).grading U d, ∃! a : Γ(X, U.1),
      a • frameGenerator (hL := hL) e ^ d = x :=
  SegreProduct.existsUnique_smul_pow_of_bijective _ _
    (Scheme.Modules.frameGradedHom_bijective _ _ U.2 he) fun a => by
      change L.chartRingHom U.1 e (MvPolynomial.rename ULift.up (MvPolynomial.C a)) = _
      rw [MvPolynomial.rename_C, Scheme.Modules.chartRingHom_C]
      rfl

variable (hL) in
/-- **The local isomorphism** `Proj (S · L)(U) ≅ Proj S(U)` over an affine open `U` with a frame
`e` of `L`: induced by `s ↦ s ⊗ e^d` for `s ∈ S(U)_d`. -/
def lineBundleTwistProjIsoOfFrame (he : Ringed.IsLocalFrame (R := X.sheaf) L U.1 e) :
    Proj ((S.lineBundleTwist L hL).grading U) ≅ Proj (S.grading U) :=
  SegreProduct.projIsoOfGenerator (S.grading U) ((lineBundleSym L hL).grading U)
    (S.algebraMap_sections_mem U) ((lineBundleSym L hL).algebraMap_sections_mem U)
    frameGenerator_mem (frameGenerator_free he)

/-- **Independence of the frame**: two frames of `L` over `U` give the same isomorphism
`Proj (S · L)(U) ≅ Proj S(U)`. -/
theorem lineBundleTwistProjIsoOfFrame_eq {e' : ULift.{u} (Fin 1) → Γ(L, U.1)}
    (he : Ringed.IsLocalFrame (R := X.sheaf) L U.1 e)
    (he' : Ringed.IsLocalFrame (R := X.sheaf) L U.1 e') :
    S.lineBundleTwistProjIsoOfFrame hL he' = S.lineBundleTwistProjIsoOfFrame hL he :=
  SegreProduct.projIsoOfGenerator_eq _ _ _ _ frameGenerator_mem frameGenerator_mem
    (frameGenerator_free he) (frameGenerator_free he')

/-- The restriction of a family of sections of `L` along an arrow `U ⟶ V` of affine opens. -/
abbrev restrictFrame {U V : X.AffineZariskiSite} (f : U ⟶ V)
    (e : ULift.{u} (Fin 1) → Γ(L, V.1)) : ULift.{u} (Fin 1) → Γ(L, U.1) :=
  fun i => L.presheaf.map (homOfLE ((toOpensFunctor X).map f).le).op (e i)

theorem isLocalFrame_restrictFrame {U V : X.AffineZariskiSite} (f : U ⟶ V)
    {e : ULift.{u} (Fin 1) → Γ(L, V.1)} (he : Ringed.IsLocalFrame (R := X.sheaf) L V.1 e) :
    Ringed.IsLocalFrame (R := X.sheaf) L U.1 (restrictFrame f e) :=
  he.restrictLE ((toOpensFunctor X).map f).le

set_option backward.isDefEq.respectTransparency false in
theorem restrict_frameGenerator {U V : X.AffineZariskiSite} (f : U ⟶ V)
    (e : ULift.{u} (Fin 1) → Γ(L, V.1)) :
    (lineBundleSym L hL).restrict f (frameGenerator (hL := hL) e) =
      frameGenerator (hL := hL) (restrictFrame f e) := by
  change ModuleSheafAlgebra.sectionsRestrict _ (homOfLE ((toOpensFunctor X).map f).le)
      (L.chartRingHom V.1 e (MvPolynomial.rename ULift.up (MvPolynomial.X 0))) =
    L.chartRingHom U.1 (restrictFrame f e) (MvPolynomial.rename ULift.up (MvPolynomial.X 0))
  refine (L.chartRingHom_naturality ((toOpensFunctor X).map f).le e _).trans ?_
  simp only [MvPolynomial.rename_X, MvPolynomial.map_X]
  rfl

/-- **Naturality of the local isomorphism** along a basic open inclusion `U ⊆ V`, with the
restricted frame on `U`. -/
theorem lineBundleTwistProjIsoOfFrame_naturality {U V : X.AffineZariskiSite} (f : U ⟶ V)
    {e : ULift.{u} (Fin 1) → Γ(L, V.1)} (he : Ringed.IsLocalFrame (R := X.sheaf) L V.1 e) :
    Proj.map ((S.lineBundleTwist L hL).restrict f) ((S.lineBundleTwist L hL).irrelevant_le f) ≫
        (S.lineBundleTwistProjIsoOfFrame hL he).hom =
      (S.lineBundleTwistProjIsoOfFrame hL (isLocalFrame_restrictFrame f he)).hom ≫
        Proj.map (S.restrict f) (S.irrelevant_le f) := by
  have ht := restrict_frameGenerator (hL := hL) f e
  have hfree' : ∀ d, ∀ x ∈ (lineBundleSym L hL).grading U d, ∃! a : Γ(X, U.1),
      a • (lineBundleSym L hL).restrict f (frameGenerator (hL := hL) e) ^ d = x := by
    rw [ht]
    exact frameGenerator_free (isLocalFrame_restrictFrame f he)
  have key := SegreProduct.projIsoOfGenerator_naturality (S.grading V)
    ((lineBundleSym L hL).grading V) (S.algebraMap_sections_mem V)
    ((lineBundleSym L hL).algebraMap_sections_mem V) frameGenerator_mem
    (S.algebraMap_sections_mem U) ((lineBundleSym L hL).algebraMap_sections_mem U)
    (baseRestrict f) (S.restrict f) ((lineBundleSym L hL).restrict f) (S.restrict_algebraMap f)
    ((lineBundleSym L hL).restrict_algebraMap f) (frameGenerator_free he) hfree'
    ((S.lineBundleTwist L hL).irrelevant_le f) (S.irrelevant_le f)
  refine key.trans ?_
  congr 2
  exact SegreProduct.projIsoOfGenerator_eq _ _ _ _ frameGenerator_mem _
    (frameGenerator_free (isLocalFrame_restrictFrame f he)) hfree'

omit hL in
/-- **Frames of an invertible sheaf exist locally on affine opens**: every point of `X` has an
affine open neighbourhood over which `L` has a frame (a single section generating `L` freely). -/
theorem exists_affine_isLocalFrame (hInv : L.IsInvertible) (x : X) :
    ∃ U : X.AffineZariskiSite, x ∈ U.1 ∧
      ∃ e : ULift.{u} (Fin 1) → Γ(L, U.1), Ringed.IsLocalFrame (R := X.sheaf) L U.1 e := by
  classical
  obtain ⟨W, hxW, ⟨α⟩⟩ := hInv x
  obtain ⟨β⟩ := (Scheme.Modules.nonempty_restrict_iso_free_iff L W _).mp ⟨α⟩
  have he := Ringed.isLocalFrame_of_over_iso (R := X.sheaf) β
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hxW W.2
  exact ⟨⟨V, hV⟩, hxV, _, he.restrictLE hVW⟩

end QuasiCoherentGradedAlgebra

end Hartshorne

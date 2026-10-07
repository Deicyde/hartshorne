/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.FiniteType
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Group.Smooth
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
import Mathlib.CategoryTheory.Monoidal.Mod

/-!
# Algebraic group actions and homogeneous spaces

Hartshorne, *Algebraic Geometry*, III.10 (pp. 272--273).
-/

open CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace Hartshorne

open AlgebraicGeometry

universe u

variable (k : Type u) [Field k]

/-- A group variety over `k`: an integral separated finite-type group object over `Spec k`. -/
structure GroupVariety where
  obj : Over (Spec (CommRingCat.of k))
  [group : GrpObj obj]
  [integral : IsIntegral obj.left]
  [separated : IsSeparated obj.hom]
  finiteType : FiniteType obj.hom

attribute [instance] GroupVariety.group GroupVariety.integral GroupVariety.separated

instance (G : GroupVariety k) : LocallyOfFiniteType G.obj.hom := G.finiteType.1
instance (G : GroupVariety k) : QuasiCompact G.obj.hom := G.finiteType.2

/-- A genuine algebraic action of `G`: the action map is a morphism
`G ×ₖ X ⟶ X` in `Over (Spec k)` satisfying the categorical action diagrams. -/
structure AlgebraicGroupAction (G : GroupVariety k) where
  X : Over (Spec (CommRingCat.of k))
  [action : ModObj G.obj X]

attribute [instance] AlgebraicGroupAction.action

/-- The action morphism `G ×ₖ X ⟶ X`. -/
abbrev AlgebraicGroupAction.actionHom {G : GroupVariety k}
    (A : AlgebraicGroupAction k G) : G.obj ⊗ A.X ⟶ A.X :=
  ModObj.smul (M := G.obj) (X := A.X)

/-- The `k`-rational points of a `k`-scheme. -/
abbrev RationalPoints (X : Over (Spec (CommRingCat.of k))) :=
  𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X

/-- The action induced on genuine `k`-point sections. -/
noncomputable def AlgebraicGroupAction.actPoint {G : GroupVariety k}
    (A : AlgebraicGroupAction k G) (g : RationalPoints k G.obj)
    (x : RationalPoints k A.X) : RationalPoints k A.X :=
  lift g x ≫ A.actionHom

/-- A homogeneous space for `G`: an integral separated finite-type `k`-scheme with a transitive
algebraic `G`-action on its `k`-points. -/
structure HomogeneousSpace (G : GroupVariety k) where
  toAction : AlgebraicGroupAction k G
  [integral : IsIntegral toAction.X.left]
  [separated : IsSeparated toAction.X.hom]
  finiteType : FiniteType toAction.X.hom
  transitive : ∀ x y : RationalPoints k toAction.X,
    ∃ g : RationalPoints k G.obj,
      AlgebraicGroupAction.actPoint (k := k) toAction g x = y

attribute [instance] HomogeneousSpace.integral HomogeneousSpace.separated

instance {G : GroupVariety k} (H : HomogeneousSpace k G) :
    LocallyOfFiniteType H.toAction.X.hom := H.finiteType.1

instance {G : GroupVariety k} (H : HomogeneousSpace k G) :
    QuasiCompact H.toAction.X.hom := H.finiteType.2

private lemma AlgebraicGroupAction.action_assoc {G : GroupVariety k}
    (A : AlgebraicGroupAction k G) {Z : Over (Spec (CommRingCat.of k))}
    (g h : Z ⟶ G.obj) (x : Z ⟶ A.X) :
    lift g (lift h x ≫ A.actionHom) ≫ A.actionHom =
      lift (lift g h ≫ μ[G.obj]) x ≫ A.actionHom := by
  have H := lift (lift g h) x ≫= ModObj.mul_smul (M := G.obj) A.X
  change lift (lift g h) x ≫ (μ[G.obj] ▷ A.X) ≫ A.actionHom =
    lift (lift g h) x ≫ (α_ G.obj G.obj A.X).hom ≫
      (G.obj ◁ A.actionHom) ≫ A.actionHom at H
  rw [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc,
    lift_whiskerLeft_assoc] at H
  exact H.symm

/-- Translation by a rational point of the acting group. -/
noncomputable def AlgebraicGroupAction.translationIso {G : GroupVariety k}
    (A : AlgebraicGroupAction k G) (g : RationalPoints k G.obj) : A.X ≅ A.X where
  hom := lift (toUnit A.X ≫ g) (𝟙 A.X) ≫ A.actionHom
  inv := lift (toUnit A.X ≫ g ≫ GrpObj.inv) (𝟙 A.X) ≫ A.actionHom
  hom_inv_id := by
    simp only [Category.assoc, comp_lift_assoc, Category.comp_id]
    have hc : lift (toUnit A.X ≫ g) (𝟙 A.X) ≫ A.actionHom ≫ toUnit A.X =
        toUnit A.X := toUnit_unique _ _
    rw [reassoc_of% hc]
    rw [AlgebraicGroupAction.action_assoc]
    simp [AlgebraicGroupAction.actionHom, ← comp_lift]
    change (1 : A.X ⟶ G.obj) • (𝟙 A.X) = 𝟙 A.X
    exact one_smul _ _
  inv_hom_id := by
    simp only [Category.assoc, comp_lift_assoc, Category.comp_id]
    have hc : lift (toUnit A.X ≫ g ≫ GrpObj.inv) (𝟙 A.X) ≫ A.actionHom ≫
        toUnit A.X = toUnit A.X := toUnit_unique _ _
    rw [reassoc_of% hc]
    rw [AlgebraicGroupAction.action_assoc]
    simp [AlgebraicGroupAction.actionHom, ← comp_lift]
    change (1 : A.X ⟶ G.obj) • (𝟙 A.X) = 𝟙 A.X
    exact one_smul _ _

/-- Translation is induced by the original action morphism. -/
lemma AlgebraicGroupAction.comp_translationIso_hom {G : GroupVariety k}
    (A : AlgebraicGroupAction k G) (g : RationalPoints k G.obj)
    {Z : Over (Spec (CommRingCat.of k))} (f : Z ⟶ A.X) :
    f ≫ (AlgebraicGroupAction.translationIso (k := k) A g).hom =
      lift (toUnit Z ≫ g) f ≫ A.actionHom := by
  simp [AlgebraicGroupAction.translationIso, AlgebraicGroupAction.actionHom,
    comp_lift_assoc]

/-- On rational points, the translation is the action defined above. -/
lemma AlgebraicGroupAction.actPoint_eq_comp_translation {G : GroupVariety k}
    (A : AlgebraicGroupAction k G) (g : RationalPoints k G.obj)
    (x : RationalPoints k A.X) :
    AlgebraicGroupAction.actPoint (k := k) A g x =
      x ≫ (AlgebraicGroupAction.translationIso (k := k) A g).hom := by
  rw [AlgebraicGroupAction.comp_translationIso_hom (k := k) A]
  simp [AlgebraicGroupAction.actPoint]

/-- Rational points as underlying scheme morphisms over `Spec k`. -/
noncomputable def rationalPointEquivSchemePoint
    (X : Over (Spec (CommRingCat.of k))) :
    RationalPoints k X ≃
      {p : Spec (CommRingCat.of k) ⟶ X.left // p ≫ X.hom = 𝟙 _} where
  toFun x := ⟨x.left, by simpa using x.w⟩
  invFun x := Over.homMk x.1 (by simpa using x.2)
  left_inv x := by
    ext
    rfl
  right_inv x := by
    ext
    rfl

/-- Over an algebraically closed field, rational points are equivalent to closed points. -/
noncomputable def rationalPointEquivClosedPoint [IsAlgClosed k]
    (X : Over (Spec (CommRingCat.of k))) [LocallyOfFiniteType X.hom] :
    RationalPoints k X ≃ closedPoints X.left :=
  (rationalPointEquivSchemePoint (k := k) X).trans
    (AlgebraicGeometry.pointEquivClosedPoint X.hom)

/-- The action induced on closed points over an algebraically closed field. -/
noncomputable def AlgebraicGroupAction.actClosedPoint [IsAlgClosed k]
    {G : GroupVariety k} (A : AlgebraicGroupAction k G)
    [LocallyOfFiniteType A.X.hom] (g : RationalPoints k G.obj)
    (x : closedPoints A.X.left) : closedPoints A.X.left :=
  rationalPointEquivClosedPoint (k := k) A.X
    (AlgebraicGroupAction.actPoint (k := k) A g
      ((rationalPointEquivClosedPoint (k := k) A.X).symm x))

/-- The action of a homogeneous space is transitive on closed points over an algebraically
closed field. -/
theorem HomogeneousSpace.transitive_closedPoints [IsAlgClosed k]
    {G : GroupVariety k} (H : HomogeneousSpace k G)
    (x y : closedPoints H.toAction.X.left) :
    ∃ g : RationalPoints k G.obj,
      AlgebraicGroupAction.actClosedPoint (k := k) H.toAction g x = y := by
  obtain ⟨g, hg⟩ := H.transitive
    ((rationalPointEquivClosedPoint (k := k) H.toAction.X).symm x)
    ((rationalPointEquivClosedPoint (k := k) H.toAction.X).symm y)
  refine ⟨g, ?_⟩
  rw [AlgebraicGroupAction.actClosedPoint, hg]
  exact (rationalPointEquivClosedPoint (k := k) H.toAction.X).apply_symm_apply y

end Hartshorne

/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Sheaves.AddCommGrpCat

/-!
# Stalks of quotient sheaves

Hartshorne, *Algebraic Geometry*, II.1 (p. 65).

The cokernel sheaf of a morphism of sheaves of abelian groups is the sheafification of its
pointwise presheaf cokernel. Its stalk is canonically the quotient of the target stalk by the
range of the induced stalk map.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hartshorne

universe u

noncomputable section

/-- The cokernel sheaf of `φ` constructed by sheafifying its pointwise presheaf cokernel. -/
noncomputable def abelianSheafCokernel
    {X : TopCat.{u}} {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (φ : F ⟶ G) : TopCat.Sheaf AddCommGrpCat.{u} X :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (cokernel φ.hom)

/-- The canonical isomorphism from the categorical sheaf cokernel to the sheafification of the
pointwise presheaf cokernel. -/
noncomputable def abelianSheafCokernelIso
    {X : TopCat.{u}} {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (φ : F ⟶ G) : cokernel φ ≅ abelianSheafCokernel φ :=
  (cokernel.mapIso φ
      ((presheafToSheaf (Opens.grothendieckTopology X)
        AddCommGrpCat.{u}).map φ.hom)
      (sheafificationIso F) (sheafificationIso G)
      ((sheafificationNatIso (Opens.grothendieckTopology X)
        AddCommGrpCat.{u}).hom.naturality φ)).trans
    (PreservesCokernel.iso
      (presheafToSheaf (Opens.grothendieckTopology X)
        AddCommGrpCat.{u}) φ.hom).symm

/-- The quotient of a sheaf of abelian groups by a subsheaf, constructed as the sheafification
of the pointwise quotient. -/
noncomputable abbrev abelianQuotientSheaf
    {X : TopCat.{u}} {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (F' : Subobject F) : TopCat.Sheaf AddCommGrpCat.{u} X :=
  abelianSheafCokernel F'.arrow

/-- The canonical projection to the sheafified pointwise cokernel. -/
noncomputable def abelianSheafCokernelπ
    {X : TopCat.{u}} {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (φ : F ⟶ G) : G ⟶ abelianSheafCokernel φ :=
  cokernel.π φ ≫ (abelianSheafCokernelIso φ).hom

/-- The canonical projection from a sheaf to its quotient by a subsheaf. -/
noncomputable abbrev abelianQuotientSheafπ
    {X : TopCat.{u}} {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (F' : Subobject F) : F ⟶ abelianQuotientSheaf F' :=
  abelianSheafCokernelπ F'.arrow

/-- The stalk of a sheafified pointwise cokernel is additively equivalent to the quotient of
the target stalk by the range of the induced stalk map. -/
noncomputable def abelianSheafCokernelStalkAddEquiv
    {X : TopCat.{u}} {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (φ : F ⟶ G) (x : X) :
    ((abelianSheafCokernel φ).presheaf.stalk x : Type u) ≃+
      ((G.presheaf.stalk x : Type u) ⧸
        AddMonoidHom.range
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map φ.hom).hom) := by
  let S := TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  exact CategoryTheory.Iso.addCommGroupIsoToAddEquiv
    (S.mapIso (abelianSheafCokernelIso φ).symm ≪≫
      PreservesCokernel.iso S φ ≪≫
      AddCommGrpCat.cokernelIsoQuotient
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map φ.hom))

/-- The stalk equivalence for the quotient of a sheaf by a subsheaf. The range of the stalk
map is the canonical realization of the subsheaf stalk as a subgroup of the ambient stalk. -/
noncomputable abbrev abelianQuotientSheafStalkAddEquiv
    {X : TopCat.{u}} {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (F' : Subobject F) (x : X) :
    ((abelianQuotientSheaf F').presheaf.stalk x : Type u) ≃+
      ((F.presheaf.stalk x : Type u) ⧸
        AddMonoidHom.range
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
            F'.arrow.hom).hom) :=
  abelianSheafCokernelStalkAddEquiv F'.arrow x

theorem abelianSheafCokernelStalkAddEquiv_apply_π
    {X : TopCat.{u}} {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (φ : F ⟶ G) (x : X) (y : G.presheaf.stalk x) :
    abelianSheafCokernelStalkAddEquiv φ x
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          (abelianSheafCokernelπ φ).hom y) =
      QuotientAddGroup.mk'
        (AddMonoidHom.range
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map φ.hom).hom) y := by
  let S := TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  change S.obj G at y
  change (((S.map (abelianSheafCokernelπ φ) ≫
    (S.mapIso (abelianSheafCokernelIso φ).symm).hom ≫
    (PreservesCokernel.iso S φ).hom ≫
    (AddCommGrpCat.cokernelIsoQuotient (S.map φ)).hom) y) = _)
  rw [abelianSheafCokernelπ, Functor.map_comp]
  simp only [Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
    Iso.map_hom_inv_id_assoc]
  rw [PreservesCokernel.π_iso_hom_assoc]
  simp [AddCommGrpCat.cokernelIsoQuotient]
  rfl

/-- **Hartshorne II.1.** The stalk of the quotient of a sheaf of abelian groups by a
subsheaf is canonically the quotient of their stalks. The pointwise law records that the
equivalence is induced by the canonical quotient projection. -/
theorem abelianQuotientSheaf_stalkAddEquiv_exists
    {X : TopCat.{u}} {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (F' : Subobject F) (x : X) :
    ∃ e :
        ((abelianQuotientSheaf F').presheaf.stalk x : Type u) ≃+
          ((F.presheaf.stalk x : Type u) ⧸
            AddMonoidHom.range
              ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
                F'.arrow.hom).hom),
      ∀ y : F.presheaf.stalk x,
        e ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
            (abelianQuotientSheafπ F').hom y) =
          QuotientAddGroup.mk'
            (AddMonoidHom.range
              ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
                F'.arrow.hom).hom) y :=
  ⟨abelianQuotientSheafStalkAddEquiv F' x,
    abelianSheafCokernelStalkAddEquiv_apply_π F'.arrow x⟩

end

end Hartshorne

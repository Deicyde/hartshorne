/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.QuasicoherentAbelianClosure

/-!
# Coherent subsheaves of a quasi-coherent sheaf

Hartshorne II, Exercise 5.15(e).  Let `X` be a locally Noetherian scheme and `F` a
quasi-coherent `𝒪_X`-module.  A coherent subsheaf of `F` is a subobject of `F` in the category
of `𝒪_X`-modules whose underlying module is coherent.

We show:

* the kernel and the image of a morphism from a coherent module to a quasi-coherent module are
  coherent (on an affine open `Spec A` this is the statement that a submodule of a finitely
  generated module over a Noetherian ring is finitely generated);
* consequently the sum of two coherent subsheaves (the image of their direct sum) is coherent,
  and the zero subsheaf is coherent, so the poset of coherent subsheaves of `F` is filtered;
* the coherent subsheaves form a diagram in `𝒪_X`-modules with a canonical cocone with vertex
  `F` given by the inclusions.

That this cocone is a colimit cocone on a Noetherian scheme needs, in addition, that every
local section of `F` lies in a coherent subsheaf, which is the extension statement of
Hartshorne II, Exercise 5.15(d).
-/

open CategoryTheory CategoryTheory.Limits

namespace Hartshorne

open AlgebraicGeometry QuasicoherentAbelianAux

universe u

noncomputable section

variable {X : Scheme.{u}}

/-- On a locally Noetherian scheme, the kernel of a morphism from a coherent module to a
quasi-coherent module is coherent. -/
theorem isCoherent_kernel_of_isQuasicoherent [IsLocallyNoetherian X] {A F : X.Modules}
    (f : A ⟶ F) (hA : IsCoherent A) [F.IsQuasicoherent] : IsCoherent (kernel f) := by
  rw [isCoherent_iff_forall_isFiniteTilde] at hA ⊢
  intro U
  have := isNoetherianRing_affineOpen U
  obtain ⟨M, hM, ⟨eA⟩⟩ := hA U
  have hF := (isQuasicoherent_iff_forall_essImage F).mp inferInstance U
  refine ⟨_, ?_, ⟨kernelTildeIso eA hF.getIso _ ≪≫ (specRestrictionKernelIso f U).symm⟩⟩
  exact Module.Finite.of_injective
    (kernel.ι ((tilde.functor _).preimage
      (eA.hom ≫ (specRestrictFunctor U).map f ≫ hF.getIso.inv))).hom
    ((ModuleCat.mono_iff_injective _).mp inferInstance)

/-- On a locally Noetherian scheme, the image of a morphism from a coherent module to a
quasi-coherent module is coherent. -/
theorem isCoherent_image_of_isQuasicoherent [IsLocallyNoetherian X] {A F : X.Modules}
    (f : A ⟶ F) (hA : IsCoherent A) [F.IsQuasicoherent] : IsCoherent (image f) :=
  isCoherent_of_iso (Abelian.coimageIsoImage' f)
    (isCoherent_cokernel _ (isCoherent_kernel_of_isQuasicoherent f hA) hA)

variable (F : X.Modules)

/-- The coherent subsheaves of an `𝒪_X`-module `F`: subobjects of `F` whose underlying module
is coherent, ordered by inclusion. -/
abbrev CoherentSubobject : Type (u + 1) :=
  {P : Subobject F // IsCoherent (P : X.Modules)}

/-- The zero subsheaf is coherent. -/
instance : Nonempty (CoherentSubobject F) :=
  ⟨⟨⊥, isCoherent_of_isZero (IsZero.of_iso (isZero_zero _) Subobject.botCoeIsoZero)⟩⟩

/-- On a locally Noetherian scheme, any two coherent subsheaves of a quasi-coherent module are
contained in a third one, namely the image of their direct sum. -/
instance [IsLocallyNoetherian X] [F.IsQuasicoherent] : IsDirectedOrder (CoherentSubobject F) where
  directed P Q := by
    let g : (P.1 : X.Modules) ⊞ (Q.1 : X.Modules) ⟶ F := biprod.desc P.1.arrow Q.1.arrow
    have hsum : IsCoherent ((P.1 : X.Modules) ⊞ (Q.1 : X.Modules)) :=
      isCoherent_of_iso (biprod.isoProd _ _).symm
        ((coherentModules X).prop_prod _ _ P.2 Q.2)
    refine ⟨⟨imageSubobject g, isCoherent_of_iso (imageSubobjectIso g).symm
      (isCoherent_image_of_isQuasicoherent g hsum)⟩, ?_, ?_⟩
    · exact Subobject.le_of_comm (biprod.inl ≫ factorThruImageSubobject g)
        (by simp [g])
    · exact Subobject.le_of_comm (biprod.inr ≫ factorThruImageSubobject g)
        (by simp [g])

/-- **Hartshorne II, Exercise 5.15(e) (filteredness).** On a locally Noetherian scheme, the
poset of coherent subsheaves of a quasi-coherent module is filtered. -/
theorem coherentSubobject_isFiltered [IsLocallyNoetherian X] [F.IsQuasicoherent] :
    IsFiltered (CoherentSubobject F) :=
  inferInstance

/-- The diagram of coherent subsheaves of `F`, sending each one to its underlying module. -/
@[simps]
def coherentSubobjectDiagram : CoherentSubobject F ⥤ X.Modules where
  obj P := (P.1 : X.Modules)
  map h := Subobject.ofLE _ _ (leOfHom h)
  map_id P := by simp
  map_comp h h' := by simp

/-- The canonical cocone over the diagram of coherent subsheaves of `F`, with vertex `F`, given
by the inclusions. -/
@[simps]
def coherentSubobjectCocone : Cocone (coherentSubobjectDiagram F) where
  pt := F
  ι :=
    { app P := P.1.arrow
      naturality := by
        intros
        exact (Subobject.ofLE_arrow _).trans (Category.comp_id _).symm }

end

end Hartshorne

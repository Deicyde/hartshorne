/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.FormalCompletion
import Mathlib.RingTheory.AdicCompletion.Algebra

/-!
# Affine sections of a formal completion

Hartshorne, *Algebraic Geometry*, II.9, p. 194.
-/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Topology Opposite TopologicalSpace

namespace Hartshorne

universe u

namespace QuasicoherentIdealSubsheaf

variable {X : Scheme.{u}} (I : QuasicoherentIdealSubsheaf X)

@[reassoc (attr := simp)]
lemma infinitesimalNeighborhoodSucc_comp_ι (n : ℕ) :
    I.infinitesimalNeighborhoodSucc n ≫ I.infinitesimalNeighborhoodι (n + 2) =
      I.infinitesimalNeighborhoodι (n + 1) :=
  Scheme.IdealSheafData.inclusion_subschemeι _

/-- The open of `Y_(n+1)` corresponding to `U ∩ |Y|` is the preimage of `U`. -/
lemma functor_obj_preimage_infinitesimalNeighborhoodι (n : ℕ) (U : X.Opens) :
    (I.isOpenEmbedding_infinitesimalNeighborhoodFromOne n).functor.obj
        (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ U) =
      I.infinitesimalNeighborhoodι (n + 1) ⁻¹ᵁ U := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    change (I.infinitesimalNeighborhoodι (n + 1)) (I.infinitesimalNeighborhoodFromOne n y) ∈ U
    rw [← Scheme.Hom.comp_apply, infinitesimalNeighborhoodFromOne_comp_ι]
    exact hy
  · intro hz
    obtain ⟨y, rfl⟩ := I.infinitesimalNeighborhoodFromOne_surjective n z
    refine ⟨y, ?_, rfl⟩
    change (I.infinitesimalNeighborhoodι 1) y ∈ U
    rw [← infinitesimalNeighborhoodFromOne_comp_ι, Scheme.Hom.comp_apply]
    exact hz

/-- `Scheme.Hom.appLE` only depends on the morphism. -/
lemma appLE_congr_hom {A B : Scheme.{u}} {f g : A ⟶ B} (h : f = g) (U : B.Opens) (V : A.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V e' := by
  subst h
  rfl

/-- `Γ(U, 𝒪_X) ⟶ Γ(U ∩ |Y|, 𝒪_{Y_(n+1)})`: restriction of functions to `Y_(n+1)`. -/
def formalCompletionSheafObjSectionsMap (n : ℕ) (U : X.Opens) :
    Γ(X, U) ⟶ (I.formalCompletionSheafObj n).presheaf.obj
      (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ U)) :=
  (I.infinitesimalNeighborhoodι (n + 1)).appLE U
    ((I.isOpenEmbedding_infinitesimalNeighborhoodFromOne n).functor.obj
      (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ U))
    (I.functor_obj_preimage_infinitesimalNeighborhoodι n U).le

lemma formalCompletionSheafObjSectionsMap_comp_map (n : ℕ) (U : X.Opens) :
    I.formalCompletionSheafObjSectionsMap (n + 1) U ≫
        (I.formalCompletionSheafMap n).hom.app (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ U)) =
      I.formalCompletionSheafObjSectionsMap n U := by
  exact (Scheme.Hom.appLE_comp_appLE (I.infinitesimalNeighborhoodSucc n)
    (I.infinitesimalNeighborhoodι (n + 2)) _ _ _ _ _).trans
    (appLE_congr_hom (I.infinitesimalNeighborhoodSucc_comp_ι n) _ _ _ _)

lemma formalCompletionSheafObjSectionsMap_comp_diagram_map {m n : ℕ} (h : m ≤ n)
    (U : X.Opens) :
    I.formalCompletionSheafObjSectionsMap n U ≫
        (I.formalCompletionDiagram.map (homOfLE h).op).hom.app
          (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ U)) =
      I.formalCompletionSheafObjSectionsMap m U := by
  induction n, h using Nat.le_induction with
  | base =>
    have h1 : (homOfLE (le_refl m)).op = 𝟙 (op m) := rfl
    rw [h1, CategoryTheory.Functor.map_id]
    rfl
  | succ n hmn ih =>
    have hc : (homOfLE (hmn.trans n.le_succ)).op =
        (homOfLE n.le_succ).op ≫ (homOfLE hmn).op := rfl
    have hmap : I.formalCompletionDiagram.map (homOfLE n.le_succ).op =
        I.formalCompletionSheafMap n :=
      CategoryTheory.Functor.ofOpSequence_map_homOfLE_succ _ n
    rw [hc, Functor.map_comp, hmap]
    rw [← ih, ← I.formalCompletionSheafObjSectionsMap_comp_map n U]
    exact (Category.assoc _ _ _).symm

/-- Restriction of sections along an equality of opens is bijective. -/
lemma bijective_presheaf_map_of_eq {Z : Scheme.{u}} {V W : Z.Opens} (h : V = W) (i : V ⟶ W) :
    Function.Bijective (Z.presheaf.map i.op).hom := by
  subst h
  rw [Subsingleton.elim i (𝟙 V), op_id, Z.presheaf.map_id, CommRingCat.hom_id]
  exact Function.bijective_id

/-- On an affine open `U`, restriction `Γ(U, 𝒪_X) → Γ(U ∩ |Y|, 𝒪_{Y_(n+1)})` is surjective. -/
lemma surjective_formalCompletionSheafObjSectionsMap (n : ℕ) (U : X.affineOpens) :
    Function.Surjective (I.formalCompletionSheafObjSectionsMap n U).hom := by
  have h1 : Function.Surjective ((I.infinitesimalNeighborhoodι (n + 1)).app U).hom :=
    Scheme.IdealSheafData.subschemeι_app_surjective _ U
  have h2 := bijective_presheaf_map_of_eq
    (I.functor_obj_preimage_infinitesimalNeighborhoodι n U)
    (homOfLE (I.functor_obj_preimage_infinitesimalNeighborhoodι n U).le)
  exact h2.2.comp h1

/-- On an affine open `U`, the kernel of `Γ(U, 𝒪_X) → Γ(U ∩ |Y|, 𝒪_{Y_(n+1)})` is
`I(U) ^ (n + 1)`. -/
lemma ker_formalCompletionSheafObjSectionsMap (n : ℕ) (U : X.affineOpens) :
    RingHom.ker (I.formalCompletionSheafObjSectionsMap n U).hom = I.ideal U ^ (n + 1) := by
  have h2 := bijective_presheaf_map_of_eq
    (I.functor_obj_preimage_infinitesimalNeighborhoodι n U)
    (homOfLE (I.functor_obj_preimage_infinitesimalNeighborhoodι n U).le)
  exact (RingHom.ker_comp_of_injective ((I.infinitesimalNeighborhoodι (n + 1)).app U).hom
    h2.1).trans ((Scheme.IdealSheafData.ker_subschemeι_app _ U).trans (I.ideal_pow (n + 1) U))

/-- Sections of `𝒪_{X̂_Y}` over `V` are the inverse limit of the sections of the
`𝒪_{Y_(n+1)}` over `V`: limits of sheaves are computed sectionwise. -/
def isLimitFormalCompletionSheafSections (V : Opens (I.infinitesimalNeighborhood 1)) :
    IsLimit (((evaluation _ CommRingCat.{u}).obj (op V)).mapCone
      ((sheafToPresheaf _ CommRingCat.{u}).mapCone (limit.cone I.formalCompletionDiagram))) :=
  have hpres : PreservesLimitsOfShape ℕᵒᵖ (sheafToPresheaf
      (Opens.grothendieckTopology (I.infinitesimalNeighborhood 1 : TopCat)) CommRingCat.{u}) :=
    inferInstance
  isLimitOfPreserves ((evaluation _ CommRingCat.{u}).obj (op V))
    ((hpres.preservesLimit (K := I.formalCompletionDiagram)).preserves
      (limit.isLimit I.formalCompletionDiagram)).some

/-- **The canonical map** `Γ(U, 𝒪_X) → Γ(U ∩ |Y|, 𝒪_{X̂_Y})`, induced by the restrictions
`Γ(U, 𝒪_X) → Γ(U ∩ |Y|, 𝒪_{Y_(n+1)})`. -/
def formalCompletionSectionsMap (U : X.Opens) :
    Γ(X, U) ⟶ I.formalCompletionSheaf.presheaf.obj (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ U)) :=
  (I.isLimitFormalCompletionSheafSections _).lift
    { pt := Γ(X, U)
      π :=
        { app n := I.formalCompletionSheafObjSectionsMap n.unop U
          naturality n m f := by
            exact (Category.id_comp _).trans
              (I.formalCompletionSheafObjSectionsMap_comp_diagram_map (leOfHom f.unop) U).symm } }

@[reassoc (attr := simp)]
lemma formalCompletionSectionsMap_π (U : X.Opens) (n : ℕ) :
    I.formalCompletionSectionsMap U ≫
        (limit.π I.formalCompletionDiagram (op n)).hom.app
          (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ U)) =
      I.formalCompletionSheafObjSectionsMap n U :=
  (I.isLimitFormalCompletionSheafSections _).fac _ (op n)

end QuasicoherentIdealSubsheaf

end Hartshorne

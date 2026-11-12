/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.FormalCompletion
import Mathlib.RingTheory.AdicCompletion.Algebra

/-!
# Affine sections of a formal completion

Hartshorne, *Algebraic Geometry*, II.9, p. 194.

Let `I` be a quasi-coherent ideal subsheaf of `𝒪_X` cutting out `Y`, and let `X̂_Y` be the formal
completion, with structure sheaf `lim_(n ≥ 1) (𝒪_X / I ^ n)|_Y` on `|Y|`. For an affine open
`U = Spec A` of `X`, with `I(U) ⊆ A` the ideal of `I` on `U`, the sections of `𝒪_{X̂_Y}` over
`U ∩ |Y|` are the inverse limit `lim_n A ⧸ I(U) ^ (n + 1)`, the `I(U)`-adic completion of `A`.

* `Hartshorne.QuasicoherentIdealSubsheaf.formalCompletionSectionsMap I U`: the canonical map
  `Γ(U, 𝒪_X) → Γ(U ∩ |Y|, 𝒪_{X̂_Y})`, for every open `U`, induced by the restrictions to the
  `Y_(n+1)`; it is natural in `U` (`formalCompletionSectionsMap_naturality`).
* `Hartshorne.QuasicoherentIdealSubsheaf.formalCompletionAffineSectionsIso I U`: for `U` affine,
  the ring isomorphism `Γ(U ∩ |Y|, 𝒪_{X̂_Y}) ≃ AdicCompletion (I(U)) A`, whose `n`-th component is
  the projection to `Γ(U ∩ |Y|, 𝒪_{Y_(n+1)}) = A ⧸ I(U) ^ (n + 1)`
  (`formalCompletionSheafObjAffineEquiv_evalₐ_formalCompletionAffineSectionsIso`).
* `formalCompletionAffineSectionsIso_formalCompletionSectionsMap`: it carries the canonical map
  from ordinary functions to the canonical map `A → Â`.
* `formalCompletionAffineSectionsIso_map`: for affine `W ⊆ U` it carries restriction of sections
  to the map of adic completions induced by restriction `Γ(U, 𝒪_X) → Γ(W, 𝒪_X)`
  (`Hartshorne.adicCompletionMap`).

The proof computes the sections of the limit sheaf as the limit of the sections, and the sections
of `𝒪_{Y_(n+1)}` over the affine open `U ∩ |Y_(n+1)|` as `A ⧸ I(U) ^ (n + 1)` (the restriction map
`Γ(U, 𝒪_X) → Γ(U ∩ |Y_(n+1)|, 𝒪_{Y_(n+1)})` is surjective with kernel `I(U) ^ (n + 1)`).

Hartshorne works over a Noetherian scheme `X`; no finiteness is used, so the results are stated
for every scheme.
-/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Topology Opposite TopologicalSpace

namespace Hartshorne

universe u

section AdicCompletion

variable {A B : Type*} [CommRing A] [CommRing B]

/-- The projections of the adic completion are compatible with the transition maps. -/
lemma factorPow_evalₐ (𝔞 : Ideal A) {m n : ℕ} (h : m ≤ n) (x : AdicCompletion 𝔞 A) :
    Ideal.Quotient.factorPow 𝔞 h (AdicCompletion.evalₐ 𝔞 n x) = AdicCompletion.evalₐ 𝔞 m x := by
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective 𝔞 A x
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, Ideal.Quotient.factor_mk]
  exact AdicCompletion.Ideal.mk_eq_mk 𝔞 h s

/-- Two elements of the adic completion agree as soon as their images in every `A ⧸ 𝔞 ^ (n + 1)`
agree. -/
lemma adicCompletion_ext_succ {𝔞 : Ideal A} {x y : AdicCompletion 𝔞 A}
    (h : ∀ n : ℕ, AdicCompletion.evalₐ 𝔞 (n + 1) x = AdicCompletion.evalₐ 𝔞 (n + 1) y) :
    x = y := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  cases n with
  | succ n => exact h n
  | zero =>
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ 𝔞 0 x)
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ 𝔞 0 y)
    rw [← ha, ← hb, Ideal.Quotient.eq, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top

/-- The ideal powers are carried along a ring homomorphism carrying `𝔞` into `𝔟`. -/
lemma pow_le_comap_pow {𝔞 : Ideal A} {𝔟 : Ideal B} {φ : A →+* B} (h : 𝔞 ≤ 𝔟.comap φ) (n : ℕ) :
    𝔞 ^ n ≤ (𝔟 ^ n).comap φ := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr h) n

/-- The reductions `A ⧸ 𝔞 ^ n → B ⧸ 𝔟 ^ n` of `φ` are compatible with the transition maps. -/
lemma adicCompletionMap_compat {𝔞 : Ideal A} {𝔟 : Ideal B} {φ : A →+* B} (h : 𝔞 ≤ 𝔟.comap φ)
    {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow 𝔟 hle).comp ((Ideal.quotientMap (𝔟 ^ n) φ
        (pow_le_comap_pow h n)).comp (AdicCompletion.evalₐ 𝔞 n).toRingHom) =
      (Ideal.quotientMap (𝔟 ^ m) φ (pow_le_comap_pow h m)).comp
        (AdicCompletion.evalₐ 𝔞 m).toRingHom := by
  ext x
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [← factorPow_evalₐ 𝔞 hle x]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ 𝔞 n x)
  rw [← ha, Ideal.quotientMap_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk,
    Ideal.quotientMap_mk]

/-- The ring homomorphism of adic completions `Â → B̂` induced by a ring homomorphism
`φ : A → B` carrying `𝔞` into `𝔟`: on `A ⧸ 𝔞 ^ n → B ⧸ 𝔟 ^ n` it is reduction of `φ`. -/
def adicCompletionMap (𝔞 : Ideal A) (𝔟 : Ideal B) (φ : A →+* B) (h : 𝔞 ≤ 𝔟.comap φ) :
    AdicCompletion 𝔞 A →+* AdicCompletion 𝔟 B :=
  AdicCompletion.liftRingHom 𝔟
    (fun n => (Ideal.quotientMap (𝔟 ^ n) φ (pow_le_comap_pow h n)).comp
      (AdicCompletion.evalₐ 𝔞 n).toRingHom)
    (adicCompletionMap_compat h)

/-- The components of `adicCompletionMap` are the reductions of `φ`. -/
@[simp]
lemma evalₐ_adicCompletionMap (𝔞 : Ideal A) (𝔟 : Ideal B) (φ : A →+* B) (h : 𝔞 ≤ 𝔟.comap φ)
    (n : ℕ) (x : AdicCompletion 𝔞 A) :
    AdicCompletion.evalₐ 𝔟 n (adicCompletionMap 𝔞 𝔟 φ h x) =
      Ideal.quotientMap (𝔟 ^ n) φ (pow_le_comap_pow h n) (AdicCompletion.evalₐ 𝔞 n x) :=
  AdicCompletion.evalₐ_liftRingHom _ _ (adicCompletionMap_compat h) n x

end AdicCompletion

/-- `Scheme.Hom.appLE` only depends on the morphism. -/
lemma Scheme.Hom.appLE_congr_hom {A B : Scheme.{u}} {f g : A ⟶ B} (h : f = g) (U : B.Opens)
    (V : A.Opens) (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V e' := by
  subst h
  rfl

/-- Restriction of sections along an equality of opens is bijective. -/
lemma Scheme.bijective_presheaf_map_of_eq {Z : Scheme.{u}} {V W : Z.Opens} (h : V = W)
    (i : V ⟶ W) : Function.Bijective (Z.presheaf.map i.op).hom := by
  subst h
  rw [Subsingleton.elim i (𝟙 V), op_id, Z.presheaf.map_id, CommRingCat.hom_id]
  exact Function.bijective_id

namespace QuasicoherentIdealSubsheaf

variable {X : Scheme.{u}} (I : QuasicoherentIdealSubsheaf X)

/-- `Y_(n+1) ⟶ Y_(n+2) ⟶ X` is the closed immersion of `Y_(n+1)`. -/
@[reassoc (attr := simp)]
lemma infinitesimalNeighborhoodSucc_comp_ι (n : ℕ) :
    I.infinitesimalNeighborhoodSucc n ≫ I.infinitesimalNeighborhoodι (n + 2) =
      I.infinitesimalNeighborhoodι (n + 1) :=
  Scheme.IdealSheafData.inclusion_subschemeι _

/-- The open of `Y_(n+1)` corresponding to `U ∩ |Y|` is the preimage of `U` in `Y_(n+1)`. -/
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

/-- `Γ(U, 𝒪_X) ⟶ Γ(U ∩ |Y|, 𝒪_{Y_(n+1)})`: restriction of functions to `Y_(n+1)`, with
`𝒪_{Y_(n+1)}` viewed as a sheaf on `|Y|` as in `formalCompletionSheafObj`. -/
def formalCompletionSheafObjSectionsMap (n : ℕ) (U : X.Opens) :
    Γ(X, U) ⟶ (I.formalCompletionSheafObj n).presheaf.obj
      (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ U)) :=
  (I.infinitesimalNeighborhoodι (n + 1)).appLE U
    ((I.isOpenEmbedding_infinitesimalNeighborhoodFromOne n).functor.obj
      (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ U))
    (I.functor_obj_preimage_infinitesimalNeighborhoodι n U).le

/-- Restriction to `Y_(n+1)` factors through restriction to `Y_(n+2)`. -/
lemma formalCompletionSheafObjSectionsMap_comp_map (n : ℕ) (U : X.Opens) :
    I.formalCompletionSheafObjSectionsMap (n + 1) U ≫
        (I.formalCompletionSheafMap n).hom.app (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ U)) =
      I.formalCompletionSheafObjSectionsMap n U := by
  exact (Scheme.Hom.appLE_comp_appLE (I.infinitesimalNeighborhoodSucc n)
    (I.infinitesimalNeighborhoodι (n + 2)) _ _ _ _ _).trans
    (Scheme.Hom.appLE_congr_hom (I.infinitesimalNeighborhoodSucc_comp_ι n) _ _ _ _)

/-- Restriction to `Y_(m+1)` factors through restriction to `Y_(n+1)`, for `m ≤ n`. -/
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

/-- On an affine open `U`, restriction `Γ(U, 𝒪_X) → Γ(U ∩ |Y|, 𝒪_{Y_(n+1)})` is surjective. -/
lemma surjective_formalCompletionSheafObjSectionsMap (n : ℕ) (U : X.affineOpens) :
    Function.Surjective (I.formalCompletionSheafObjSectionsMap n U).hom := by
  have h1 : Function.Surjective ((I.infinitesimalNeighborhoodι (n + 1)).app U).hom :=
    Scheme.IdealSheafData.subschemeι_app_surjective _ U
  have h2 := Scheme.bijective_presheaf_map_of_eq
    (I.functor_obj_preimage_infinitesimalNeighborhoodι n U)
    (homOfLE (I.functor_obj_preimage_infinitesimalNeighborhoodι n U).le)
  exact h2.2.comp h1

/-- On an affine open `U`, the kernel of `Γ(U, 𝒪_X) → Γ(U ∩ |Y|, 𝒪_{Y_(n+1)})` is
`I(U) ^ (n + 1)`. -/
lemma ker_formalCompletionSheafObjSectionsMap (n : ℕ) (U : X.affineOpens) :
    RingHom.ker (I.formalCompletionSheafObjSectionsMap n U).hom = I.ideal U ^ (n + 1) := by
  have h2 := Scheme.bijective_presheaf_map_of_eq
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

/-- The canonical map followed by the projection to `𝒪_{Y_(n+1)}` is restriction to `Y_(n+1)`. -/
@[reassoc (attr := simp)]
lemma formalCompletionSectionsMap_π (U : X.Opens) (n : ℕ) :
    I.formalCompletionSectionsMap U ≫
        (limit.π I.formalCompletionDiagram (op n)).hom.app
          (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ U)) =
      I.formalCompletionSheafObjSectionsMap n U :=
  (I.isLimitFormalCompletionSheafSections _).fac _ (op n)

/-- Elementwise form of `formalCompletionSheafObjSectionsMap_comp_diagram_map`. -/
lemma formalCompletionSheafObjSectionsMap_diagram_map_apply {m n : ℕ} (h : m ≤ n)
    (U : X.Opens) (a : Γ(X, U)) :
    (I.formalCompletionDiagram.map (homOfLE h).op).hom.app
        (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ U)) (I.formalCompletionSheafObjSectionsMap n U a) =
      I.formalCompletionSheafObjSectionsMap m U a := by
  rw [← I.formalCompletionSheafObjSectionsMap_comp_diagram_map h U]
  rfl

/-- Restriction to `Y_(n+1)` commutes with restriction to a smaller open. -/
lemma formalCompletionSheafObjSectionsMap_naturality (n : ℕ) {U W : X.Opens} (h : W ≤ U) :
    I.formalCompletionSheafObjSectionsMap n U ≫ (I.formalCompletionSheafObj n).presheaf.map
        ((Opens.map (I.infinitesimalNeighborhoodι 1).base).map (homOfLE h)).op =
      X.presheaf.map (homOfLE h).op ≫ I.formalCompletionSheafObjSectionsMap n W :=
  (Scheme.Hom.appLE_map _ _ _).trans (Scheme.Hom.map_appLE _ _ _).symm

/-- The canonical map commutes with restriction to a smaller open. -/
lemma formalCompletionSectionsMap_naturality {U W : X.Opens} (h : W ≤ U) :
    I.formalCompletionSectionsMap U ≫ I.formalCompletionSheaf.presheaf.map
        ((Opens.map (I.infinitesimalNeighborhoodι 1).base).map (homOfLE h)).op =
      X.presheaf.map (homOfLE h).op ≫ I.formalCompletionSectionsMap W := by
  refine (I.isLimitFormalCompletionSheafSections _).hom_ext fun n => ?_
  ext a
  have h1 := congrArg (fun φ => φ a) (I.formalCompletionSectionsMap_π U n.unop)
  have h2 := congrArg (fun φ => φ (X.presheaf.map (homOfLE h).op a))
    (I.formalCompletionSectionsMap_π W n.unop)
  have h3 := congrArg (fun φ => φ a) (I.formalCompletionSheafObjSectionsMap_naturality n.unop h)
  refine (NatTrans.naturality_apply (limit.π I.formalCompletionDiagram (op n.unop)).hom
    ((Opens.map (I.infinitesimalNeighborhoodι 1).base).map (homOfLE h)).op _).trans ?_
  exact ((congrArg _ h1).trans h3).trans h2.symm

/-- Restriction to a smaller affine open `W ⊆ U` carries `I(U)` into `I(W)`. -/
lemma ideal_le_comap_ideal {U W : X.affineOpens} (h : W ≤ U) :
    I.ideal U ≤ (I.ideal W).comap (X.presheaf.map (homOfLE h).op).hom :=
  (quasicoherentIdealSubsheafEquiv I).ideal_le_comap_ideal h

section Affine

variable (U : X.affineOpens)

/-- `A ⧸ I(U) ^ (n + 1) ≃ Γ(U ∩ |Y|, 𝒪_{Y_(n+1)})` for `U = Spec A` affine. -/
def formalCompletionSheafObjAffineEquiv (n : ℕ) :
    Γ(X, U) ⧸ I.ideal U ^ (n + 1) ≃+* (I.formalCompletionSheafObj n).presheaf.obj
      (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ (U : X.Opens))) :=
  (Ideal.quotEquivOfEq (I.ker_formalCompletionSheafObjSectionsMap n U).symm).trans
    (RingHom.quotientKerEquivOfSurjective (I.surjective_formalCompletionSheafObjSectionsMap n U))

/-- `formalCompletionSheafObjAffineEquiv` is induced by restriction to `Y_(n+1)`. -/
lemma formalCompletionSheafObjAffineEquiv_mk (n : ℕ) (a : Γ(X, U)) :
    I.formalCompletionSheafObjAffineEquiv U n (Ideal.Quotient.mk _ a) =
      I.formalCompletionSheafObjSectionsMap n U a :=
  rfl

/-- The projection `Γ(U ∩ |Y|, 𝒪_{X̂_Y}) → A ⧸ I(U) ^ (n + 1)`. -/
def formalCompletionAffineProj (n : ℕ) :
    I.formalCompletionSheaf.presheaf.obj (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ (U : X.Opens)))
      →+* Γ(X, U) ⧸ I.ideal U ^ (n + 1) :=
  (I.formalCompletionSheafObjAffineEquiv U n).symm.toRingHom.comp
    ((limit.π I.formalCompletionDiagram (op n)).hom.app
      (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ (U : X.Opens)))).hom

/-- `formalCompletionAffineProj` is the projection to `𝒪_{Y_(n+1)}`, read in
`A ⧸ I(U) ^ (n + 1)`. -/
lemma formalCompletionSheafObjAffineEquiv_formalCompletionAffineProj (n : ℕ)
    (s : I.formalCompletionSheaf.presheaf.obj
      (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ (U : X.Opens)))) :
    I.formalCompletionSheafObjAffineEquiv U n (I.formalCompletionAffineProj U n s) =
      (limit.π I.formalCompletionDiagram (op n)).hom.app
        (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ (U : X.Opens))) s :=
  (I.formalCompletionSheafObjAffineEquiv U n).apply_symm_apply _

/-- The projections to the `A ⧸ I(U) ^ (n + 1)` are compatible with the transition maps. -/
lemma factorPow_formalCompletionAffineProj {m n : ℕ} (h : m ≤ n)
    (s : I.formalCompletionSheaf.presheaf.obj
      (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ (U : X.Opens)))) :
    Ideal.Quotient.factorPow (I.ideal U) (Nat.succ_le_succ h)
        (I.formalCompletionAffineProj U n s) = I.formalCompletionAffineProj U m s := by
  apply (I.formalCompletionSheafObjAffineEquiv U m).injective
  rw [formalCompletionSheafObjAffineEquiv_formalCompletionAffineProj]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I.formalCompletionAffineProj U n s)
  have hw := congrArg (fun φ => φ.hom.app (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ (U : X.Opens))) s)
    (limit.w I.formalCompletionDiagram (homOfLE h).op)
  have hn := I.formalCompletionSheafObjAffineEquiv_formalCompletionAffineProj U n s
  rw [← ha, formalCompletionSheafObjAffineEquiv_mk] at hn
  rw [← ha, Ideal.Quotient.factor_mk, formalCompletionSheafObjAffineEquiv_mk, ← hw]
  change _ = (I.formalCompletionDiagram.map (homOfLE h).op).hom.app _
    ((limit.π I.formalCompletionDiagram (op n)).hom.app _ s)
  rw [← hn, formalCompletionSheafObjSectionsMap_diagram_map_apply]

/-- The compatibility of the projections in the form used by `AdicCompletion.liftRingHom`. -/
lemma formalCompletionAffineProj_compat {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (I.ideal U) hle).comp
        ((Ideal.Quotient.factorPow (I.ideal U) n.le_succ).comp (I.formalCompletionAffineProj U n)) =
      (Ideal.Quotient.factorPow (I.ideal U) m.le_succ).comp (I.formalCompletionAffineProj U m) := by
  ext s
  simp only [RingHom.comp_apply]
  rw [← I.factorPow_formalCompletionAffineProj U hle s]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I.formalCompletionAffineProj U n s)
  rw [← ha, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk,
    Ideal.Quotient.factor_mk]

/-- The map `Γ(U ∩ |Y|, 𝒪_{X̂_Y}) → lim_n A ⧸ I(U) ^ (n + 1)` induced by the projections. -/
def formalCompletionAffineSectionsToAdic :
    I.formalCompletionSheaf.presheaf.obj (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ (U : X.Opens)))
      →+* AdicCompletion (I.ideal U) Γ(X, U) :=
  AdicCompletion.liftRingHom (I.ideal U)
    (fun n => (Ideal.Quotient.factorPow (I.ideal U) n.le_succ).comp
      (I.formalCompletionAffineProj U n))
    (I.formalCompletionAffineProj_compat U)

/-- The components of `formalCompletionAffineSectionsToAdic` are the projections. -/
lemma evalₐ_formalCompletionAffineSectionsToAdic (n : ℕ)
    (s : I.formalCompletionSheaf.presheaf.obj
      (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ (U : X.Opens)))) :
    AdicCompletion.evalₐ (I.ideal U) (n + 1) (I.formalCompletionAffineSectionsToAdic U s) =
      I.formalCompletionAffineProj U n s :=
  (AdicCompletion.evalₐ_liftRingHom _ _ (I.formalCompletionAffineProj_compat U) (n + 1) s).trans
    (I.factorPow_formalCompletionAffineProj U n.le_succ s)

/-- The projections of the adic completion, read in the `Γ(U ∩ |Y|, 𝒪_{Y_(n+1)})`, are
compatible with the transition maps. -/
lemma formalCompletionSheafObjAffineEquiv_evalₐ_diagram_map {m n : ℕ} (h : m ≤ n)
    (x : AdicCompletion (I.ideal U) Γ(X, U)) :
    (I.formalCompletionDiagram.map (homOfLE h).op).hom.app
        (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ (U : X.Opens)))
        (I.formalCompletionSheafObjAffineEquiv U n (AdicCompletion.evalₐ _ (n + 1) x)) =
      I.formalCompletionSheafObjAffineEquiv U m (AdicCompletion.evalₐ _ (m + 1) x) := by
  rw [← factorPow_evalₐ (I.ideal U) (Nat.succ_le_succ h) x]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (I.ideal U) (n + 1) x)
  rw [← ha, Ideal.Quotient.factor_mk, formalCompletionSheafObjAffineEquiv_mk,
    formalCompletionSheafObjAffineEquiv_mk, formalCompletionSheafObjSectionsMap_diagram_map_apply]

/-- The cone with point `lim_n A ⧸ I(U) ^ (n + 1)` over the sections over `U ∩ |Y|` of the
inverse system `n ↦ 𝒪_{Y_(n+1)}`. -/
def formalCompletionAffineAdicCone :
    Cone ((I.formalCompletionDiagram ⋙ sheafToPresheaf
      (Opens.grothendieckTopology (I.infinitesimalNeighborhood 1)) CommRingCat.{u}) ⋙
        (evaluation _ CommRingCat.{u}).obj
          (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ (U : X.Opens)))) where
  pt := CommRingCat.of (AdicCompletion (I.ideal U) Γ(X, U))
  π :=
    { app n := CommRingCat.ofHom ((I.formalCompletionSheafObjAffineEquiv U n.unop).toRingHom.comp
        (AdicCompletion.evalₐ (I.ideal U) (n.unop + 1)).toRingHom)
      naturality n m f := by
        refine (Category.id_comp _).trans ?_
        ext x
        exact (I.formalCompletionSheafObjAffineEquiv_evalₐ_diagram_map U
          (leOfHom f.unop) x).symm }

/-- The inverse map `lim_n A ⧸ I(U) ^ (n + 1) → Γ(U ∩ |Y|, 𝒪_{X̂_Y})`. -/
def adicToFormalCompletionAffineSections :
    CommRingCat.of (AdicCompletion (I.ideal U) Γ(X, U)) ⟶
      I.formalCompletionSheaf.presheaf.obj
        (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ (U : X.Opens))) :=
  (I.isLimitFormalCompletionSheafSections _).lift (I.formalCompletionAffineAdicCone U)

/-- The components of `adicToFormalCompletionAffineSections`. -/
lemma adicToFormalCompletionAffineSections_π (n : ℕ)
    (x : AdicCompletion (I.ideal U) Γ(X, U)) :
    (limit.π I.formalCompletionDiagram (op n)).hom.app
        (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ (U : X.Opens)))
        (I.adicToFormalCompletionAffineSections U x) =
      I.formalCompletionSheafObjAffineEquiv U n (AdicCompletion.evalₐ _ (n + 1) x) := by
  have := (I.isLimitFormalCompletionSheafSections
    (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ (U : X.Opens))).fac
      (I.formalCompletionAffineAdicCone U) (op n)
  exact congrArg (fun φ => φ x) this

/-- **Affine sections of the formal completion** (Hartshorne II.9, p. 194). For an affine open
`U = Spec A` of `X`, with `I(U) ⊆ A` the ideal of `I` on `U`,
`Γ(U ∩ |Y|, 𝒪_{X̂_Y}) ≅ lim_n A ⧸ I(U) ^ (n + 1)`, the `I(U)`-adic completion of `A`. The
`n`-th component is the projection to `Γ(U ∩ |Y|, 𝒪_{Y_(n+1)}) = A ⧸ I(U) ^ (n + 1)`
(`formalCompletionSheafObjAffineEquiv_evalₐ_formalCompletionAffineSectionsIso`). -/
def formalCompletionAffineSectionsIso :
    I.formalCompletionSheaf.presheaf.obj (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ (U : X.Opens)))
      ≃+* AdicCompletion (I.ideal U) Γ(X, U) where
  toFun := I.formalCompletionAffineSectionsToAdic U
  invFun := I.adicToFormalCompletionAffineSections U
  left_inv s := by
    refine Concrete.isLimit_ext _ (I.isLimitFormalCompletionSheafSections _) _ _ fun n => ?_
    change (limit.π I.formalCompletionDiagram (op n.unop)).hom.app _
        (I.adicToFormalCompletionAffineSections U _) =
      (limit.π I.formalCompletionDiagram (op n.unop)).hom.app _ s
    rw [adicToFormalCompletionAffineSections_π, evalₐ_formalCompletionAffineSectionsToAdic,
      formalCompletionSheafObjAffineEquiv_formalCompletionAffineProj]
  right_inv x := by
    refine adicCompletion_ext_succ fun n => ?_
    rw [evalₐ_formalCompletionAffineSectionsToAdic]
    apply (I.formalCompletionSheafObjAffineEquiv U n).injective
    rw [formalCompletionSheafObjAffineEquiv_formalCompletionAffineProj,
      adicToFormalCompletionAffineSections_π]
  map_mul' := map_mul _
  map_add' := map_add _

/-- The `n`-th component of `formalCompletionAffineSectionsIso` is the projection to
`Γ(U ∩ |Y|, 𝒪_{Y_(n+1)}) = A ⧸ I(U) ^ (n + 1)`. -/
theorem formalCompletionSheafObjAffineEquiv_evalₐ_formalCompletionAffineSectionsIso (n : ℕ)
    (s : I.formalCompletionSheaf.presheaf.obj
      (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ (U : X.Opens)))) :
    I.formalCompletionSheafObjAffineEquiv U n
        (AdicCompletion.evalₐ (I.ideal U) (n + 1) (I.formalCompletionAffineSectionsIso U s)) =
      (limit.π I.formalCompletionDiagram (op n)).hom.app
        (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ (U : X.Opens))) s := by
  change I.formalCompletionSheafObjAffineEquiv U n
    (AdicCompletion.evalₐ (I.ideal U) (n + 1) (I.formalCompletionAffineSectionsToAdic U s)) = _
  rw [evalₐ_formalCompletionAffineSectionsToAdic,
    formalCompletionSheafObjAffineEquiv_formalCompletionAffineProj]

/-- **Compatibility with ordinary functions** (Hartshorne II.9, p. 194): under
`formalCompletionAffineSectionsIso`, the canonical map `Γ(U, 𝒪_X) → Γ(U ∩ |Y|, 𝒪_{X̂_Y})` is
the canonical map `A → Â`. -/
theorem formalCompletionAffineSectionsIso_formalCompletionSectionsMap (a : Γ(X, U)) :
    I.formalCompletionAffineSectionsIso U (I.formalCompletionSectionsMap U a) =
      AdicCompletion.of (I.ideal U) Γ(X, U) a := by
  refine adicCompletion_ext_succ fun n => ?_
  rw [AdicCompletion.evalₐ_of]
  apply (I.formalCompletionSheafObjAffineEquiv U n).injective
  rw [formalCompletionSheafObjAffineEquiv_evalₐ_formalCompletionAffineSectionsIso,
    formalCompletionSheafObjAffineEquiv_mk]
  exact congrArg (fun φ => φ a) (I.formalCompletionSectionsMap_π U n)

/-- **Compatibility with restriction** (Hartshorne II.9, p. 194): for affine opens `W ⊆ U`,
restriction `Γ(U ∩ |Y|, 𝒪_{X̂_Y}) → Γ(W ∩ |Y|, 𝒪_{X̂_Y})` corresponds under
`formalCompletionAffineSectionsIso` to the map of adic completions induced by restriction
`Γ(U, 𝒪_X) → Γ(W, 𝒪_X)`. -/
theorem formalCompletionAffineSectionsIso_map {U W : X.affineOpens} (h : W ≤ U)
    (s : I.formalCompletionSheaf.presheaf.obj
      (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ (U : X.Opens)))) :
    I.formalCompletionAffineSectionsIso W (I.formalCompletionSheaf.presheaf.map
        ((Opens.map (I.infinitesimalNeighborhoodι 1).base).map (homOfLE h)).op s) =
      adicCompletionMap (I.ideal U) (I.ideal W) (X.presheaf.map (homOfLE h).op).hom
        (I.ideal_le_comap_ideal h)
        (I.formalCompletionAffineSectionsIso U s) := by
  refine adicCompletion_ext_succ fun n => ?_
  rw [evalₐ_adicCompletionMap]
  apply (I.formalCompletionSheafObjAffineEquiv W n).injective
  rw [formalCompletionSheafObjAffineEquiv_evalₐ_formalCompletionAffineSectionsIso]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ (I.ideal U) (n + 1) (I.formalCompletionAffineSectionsIso U s))
  have hU := I.formalCompletionSheafObjAffineEquiv_evalₐ_formalCompletionAffineSectionsIso U n s
  rw [← ha, formalCompletionSheafObjAffineEquiv_mk] at hU
  rw [← ha, Ideal.quotientMap_mk, formalCompletionSheafObjAffineEquiv_mk]
  refine (NatTrans.naturality_apply (limit.π I.formalCompletionDiagram (op n)).hom
    ((Opens.map (I.infinitesimalNeighborhoodι 1).base).map (homOfLE h)).op s).trans ?_
  rw [← hU]
  exact congrArg (fun φ => φ a) (I.formalCompletionSheafObjSectionsMap_naturality n h)

end Affine

end QuasicoherentIdealSubsheaf

end Hartshorne

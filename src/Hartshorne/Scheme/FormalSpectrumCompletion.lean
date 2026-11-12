/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.FormalSpectrum
import Hartshorne.Scheme.AdicCompletionQuotient
import Hartshorne.Scheme.AdicCompletionNoetherian

/-!
# The formal spectrum is invariant under adic completion

A project-authored comparison supporting Hartshorne, *Algebraic Geometry*, II.9 (the replacement
of an affine Noetherian ring by its completion in Proposition 9.6, pp. 197–198). Hartshorne does
not use the notation `Spf`; here `Spf_I(A)` is the project's formal completion of `Spec A` along
`V(I)` (`Hartshorne.Spf`), with no topology on the section rings.

* `Hartshorne.QuasicoherentIdealSubsheaf.formalCompletionIsoOfNeighborhoodIso`: a family of
  isomorphisms `φ_n : Y_(n+1) ≅ Y'_(n+1)` between the infinitesimal neighbourhoods of two closed
  subschemes, compatible with the inclusions `Y_(n+1) ⟶ Y_(n+2)`, induces an isomorphism of the
  formal completions: `φ_0` on spaces, and the induced isomorphism of the inverse limits of the
  `𝒪_{Y_(n+1)}` on structure sheaves
  (`QuasicoherentIdealSubsheaf.formalCompletionIsoOfNeighborhoodIso_hom_c_app_π`).
* `Hartshorne.spfCompletionNeighborhoodIso A I n`: for Noetherian `A` with `I`-adic completion
  `Â` and `Î = I Â`, the isomorphism between the closed subschemes of `Spec A` and `Spec Â` cut out
  by `I ^ (n + 1)` and `Î ^ (n + 1)`, through
  `Spec (A ⧸ I ^ (n + 1)) ≅ Spec (Â ⧸ Î ^ (n + 1))` (Hartshorne II.9.3A(a),
  `Hartshorne.exists_adicCompletionQuotientRingEquiv`). It lies over `Spec A`
  (`Hartshorne.spfCompletionNeighborhoodIso_hom_comp_ι_comp`).
* `Hartshorne.spfCompletionIso A I : Spf_I(A) ≅ Spf_Î(Â)`, the induced isomorphism of locally
  ringed spaces, with `Hartshorne.spec_map_algebraMap_spfCompletionIso_hom_base` (on points it lies
  over `Spec A`) and `Hartshorne.spfCompletionIso_hom_c_app_π` (on sections it is compatible with
  the projections to the infinitesimal neighbourhoods).
* `Hartshorne.spf_completion_invariant`: the statement of the comparison.

This does not identify morphisms of formal schemes with continuous ring homomorphisms.
-/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Topology Opposite TopologicalSpace

namespace Hartshorne

universe u

namespace QuasicoherentIdealSubsheaf

variable {X X' : Scheme.{u}} (I : QuasicoherentIdealSubsheaf X)
  (I' : QuasicoherentIdealSubsheaf X')
  (φ : ∀ n : ℕ, I.infinitesimalNeighborhood (n + 1) ≅ I'.infinitesimalNeighborhood (n + 1))
  (hφ : ∀ n : ℕ, (φ n).hom ≫ I'.infinitesimalNeighborhoodSucc n =
    I.infinitesimalNeighborhoodSucc n ≫ (φ (n + 1)).hom)

include hφ in
/-- A compatible family of isomorphisms of the infinitesimal neighbourhoods is compatible with
the inclusions `Y_1 ⟶ Y_(n+1)`. -/
lemma neighborhoodIso_comp_infinitesimalNeighborhoodFromOne (n : ℕ) :
    (φ 0).hom ≫ I'.infinitesimalNeighborhoodFromOne n =
      I.infinitesimalNeighborhoodFromOne n ≫ (φ n).hom := by
  induction n with
  | zero =>
    change (φ 0).hom ≫ Scheme.IdealSheafData.inclusion le_rfl =
      Scheme.IdealSheafData.inclusion le_rfl ≫ (φ 0).hom
    rw [Scheme.IdealSheafData.inclusion_id, Scheme.IdealSheafData.inclusion_id]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  | succ n ih =>
    rw [← infinitesimalNeighborhoodFromOne_comp_succ, ← infinitesimalNeighborhoodFromOne_comp_succ,
      reassoc_of% ih, hφ, Category.assoc]

/-- The underlying homeomorphism `|Y_1| ≅ |Y'_1|` of a family of isomorphisms of infinitesimal
neighbourhoods. -/
def neighborhoodIsoBase : (I.infinitesimalNeighborhood 1).toTopCat ≅
    (I'.infinitesimalNeighborhood 1).toTopCat where
  hom := (φ 0).hom.base
  inv := (φ 0).inv.base
  hom_inv_id := by rw [← Scheme.Hom.comp_base, Iso.hom_inv_id, Scheme.Hom.id_base]; rfl
  inv_hom_id := by rw [← Scheme.Hom.comp_base, Iso.inv_hom_id, Scheme.Hom.id_base]; rfl

include hφ in
/-- Under a compatible family of isomorphisms `φ_n : Y_(n+1) ≅ Y'_(n+1)`, the image in `Y_(n+1)`
of the preimage under `φ_0` of an open `W ⊆ |Y'_1|` is the preimage under `φ_n` of the image of
`W` in `Y'_(n+1)`. -/
lemma functor_obj_map_neighborhoodIso (n : ℕ) (W : Opens (I'.infinitesimalNeighborhood 1)) :
    (I.isOpenEmbedding_infinitesimalNeighborhoodFromOne n).functor.obj
        ((Opens.map (φ 0).hom.base).obj W) =
      (φ n).hom ⁻¹ᵁ (I'.isOpenEmbedding_infinitesimalNeighborhoodFromOne n).functor.obj W := by
  have hc (y : I.infinitesimalNeighborhood 1) :
      I'.infinitesimalNeighborhoodFromOne n ((φ 0).hom y) =
        (φ n).hom (I.infinitesimalNeighborhoodFromOne n y) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
      neighborhoodIso_comp_infinitesimalNeighborhoodFromOne I I' φ hφ n]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(φ 0).hom y, hy, hc y⟩
  · rintro ⟨w, hw, hwx⟩
    obtain ⟨y, rfl⟩ := I.infinitesimalNeighborhoodFromOne_surjective n x
    refine ⟨y, ?_, rfl⟩
    rw [← hc] at hwx
    have := (I'.isOpenEmbedding_infinitesimalNeighborhoodFromOne n).injective hwx
    change (φ 0).hom y ∈ W
    rw [← this]
    exact hw

include hφ in
/-- The `n`-th component of the comparison: `φ_n` identifies `𝒪_{Y'_(n+1)}` on `|Y'_1|` with the
pushforward along `φ_0` of `𝒪_{Y_(n+1)}` on `|Y_1|`. -/
def neighborhoodIsoApp (n : ℕ) :
    (I'.formalCompletionSheafObj n).obj ⟶
      (TopCat.Presheaf.pushforward _ (neighborhoodIsoBase I I' φ).hom).obj
        (I.formalCompletionSheafObj n).obj where
  app W := (φ n).hom.appLE _ _ (functor_obj_map_neighborhoodIso I I' φ hφ n W.unop).le
  naturality W W' i := by
    change (I'.infinitesimalNeighborhood (n + 1)).presheaf.map _ ≫ (φ n).hom.appLE _ _ _ =
      (φ n).hom.appLE _ _ _ ≫ (I.infinitesimalNeighborhood (n + 1)).presheaf.map _
    exact (Scheme.Hom.map_appLE _ _ _).trans (Scheme.Hom.appLE_map _ _ _).symm

lemma neighborhoodIsoApp_app (n : ℕ) (W : (Opens (I'.infinitesimalNeighborhood 1))ᵒᵖ) :
    (neighborhoodIsoApp I I' φ hφ n).app W =
      (φ n).hom.appLE _ _ (functor_obj_map_neighborhoodIso I I' φ hφ n W.unop).le :=
  rfl

instance (n : ℕ) : IsIso (neighborhoodIsoApp I I' φ hφ n) := by
  have (W : (Opens (I'.infinitesimalNeighborhood 1))ᵒᵖ) :
      IsIso ((neighborhoodIsoApp I I' φ hφ n).app W) := by
    rw [neighborhoodIsoApp_app, Scheme.Hom.appLE]
    have h0 : IsIso (homOfLE (functor_obj_map_neighborhoodIso I I' φ hφ n W.unop).le).op :=
      ⟨(homOfLE (functor_obj_map_neighborhoodIso I I' φ hφ n W.unop).ge).op,
        Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    have h1 : IsIso ((φ n).hom.app
        ((I'.isOpenEmbedding_infinitesimalNeighborhoodFromOne n).functor.obj W.unop)) := by
      have := PresheafedSpace.c_isIso_of_iso (φ n).hom.toPshHom
      exact NatIso.isIso_app_of_isIso (φ n).hom.c _
    have h2 : IsIso ((I.infinitesimalNeighborhood (n + 1)).presheaf.map
        (homOfLE (functor_obj_map_neighborhoodIso I I' φ hφ n W.unop).le).op) :=
      Functor.map_isIso _ _
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2
  exact NatIso.isIso_of_isIso_app _

private lemma appLE_congr_hom {A B : Scheme.{u}} {f g : A ⟶ B} (h : f = g) (U : B.Opens)
    (V : A.Opens) (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V e' := by
  subst h
  rfl

private lemma appLE_comp_appLE_eq {A B C D : Scheme.{u}} {f : A ⟶ B} {g : B ⟶ D} {f' : A ⟶ C}
    {g' : C ⟶ D} (h : f ≫ g = f' ≫ g') (U : D.Opens) (V : B.Opens) (V' : C.Opens) (W : A.Opens)
    (e₁ : V ≤ g ⁻¹ᵁ U) (e₂ : W ≤ f ⁻¹ᵁ V) (e₁' : V' ≤ g' ⁻¹ᵁ U) (e₂' : W ≤ f' ⁻¹ᵁ V') :
    g.appLE U V e₁ ≫ f.appLE V W e₂ = g'.appLE U V' e₁' ≫ f'.appLE V' W e₂' := by
  rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
  exact appLE_congr_hom h _ _ _ _

include hφ in
private lemma appLE_succ_comp_appLE (n : ℕ) (W : Opens (I'.infinitesimalNeighborhood 1)) :
    (I'.infinitesimalNeighborhoodSucc n).appLE
        ((I'.isOpenEmbedding_infinitesimalNeighborhoodFromOne (n + 1)).functor.obj W)
        ((I'.isOpenEmbedding_infinitesimalNeighborhoodFromOne n).functor.obj W)
        (I'.functor_obj_le_preimage_infinitesimalNeighborhoodSucc n W) ≫
      (φ n).hom.appLE _ _ (functor_obj_map_neighborhoodIso I I' φ hφ n W).le =
    (φ (n + 1)).hom.appLE _ _ (functor_obj_map_neighborhoodIso I I' φ hφ (n + 1) W).le ≫
      (I.infinitesimalNeighborhoodSucc n).appLE _ _
        (I.functor_obj_le_preimage_infinitesimalNeighborhoodSucc n
          ((Opens.map (φ 0).hom.base).obj W)) := by
  exact appLE_comp_appLE_eq (hφ n) _ _ _ _ _ _ _ _

include hφ in
/-- The comparison of the inverse systems `n ↦ 𝒪_{Y'_(n+1)}` and `n ↦ 𝒪_{Y_(n+1)}`, the latter
pushed forward along `φ_0`. -/
def neighborhoodIsoCompare :
    I'.formalCompletionDiagram ⋙ sheafToPresheaf _ _ ⟶
      (I.formalCompletionDiagram ⋙ sheafToPresheaf _ _) ⋙
        TopCat.Presheaf.pushforward _ (neighborhoodIsoBase I I' φ).hom :=
  NatTrans.ofOpSequence (fun n => neighborhoodIsoApp I I' φ hφ n) (fun n => by
    have hmap : I.formalCompletionDiagram.map (homOfLE (Nat.le_add_right n 1)).op =
        I.formalCompletionSheafMap n :=
      CategoryTheory.Functor.ofOpSequence_map_homOfLE_succ _ n
    have hmap' : I'.formalCompletionDiagram.map (homOfLE (Nat.le_add_right n 1)).op =
        I'.formalCompletionSheafMap n :=
      CategoryTheory.Functor.ofOpSequence_map_homOfLE_succ _ n
    refine NatTrans.ext (funext fun W => ?_)
    change (I'.formalCompletionDiagram.map (homOfLE (Nat.le_add_right n 1)).op).hom.app W ≫
        (neighborhoodIsoApp I I' φ hφ n).app W =
      (neighborhoodIsoApp I I' φ hφ (n + 1)).app W ≫
        (I.formalCompletionDiagram.map (homOfLE (Nat.le_add_right n 1)).op).hom.app _
    rw [hmap, hmap']
    exact appLE_succ_comp_appLE I I' φ hφ n W.unop)

instance isIso_neighborhoodIsoCompare : IsIso (neighborhoodIsoCompare I I' φ hφ) := by
  have (n : ℕᵒᵖ) : IsIso ((neighborhoodIsoCompare I I' φ hφ).app n) := by
    change IsIso (neighborhoodIsoApp I I' φ hφ n.unop)
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- The limit of an inverse system of sheaves of rings is preserved by forgetting the sheaf
condition. -/
private def sheafLimitIsLimit {T : TopCat.{u}} (D : ℕᵒᵖ ⥤ TopCat.Sheaf CommRingCat.{u} T) :
    IsLimit ((sheafToPresheaf (Opens.grothendieckTopology T) CommRingCat.{u}).mapCone
      (limit.cone D)) :=
  have hpres : PreservesLimitsOfShape ℕᵒᵖ
      (sheafToPresheaf (Opens.grothendieckTopology T) CommRingCat.{u}) := inferInstance
  ((hpres.preservesLimit (K := D)).preserves (limit.isLimit D)).some

/-- The sections of the limit sheaf are the limit of the presheaves. -/
private def sheafLimitIso {T : TopCat.{u}} (D : ℕᵒᵖ ⥤ TopCat.Sheaf CommRingCat.{u} T) :
    (limit D).presheaf ≅ limit (D ⋙ sheafToPresheaf _ _) :=
  (sheafLimitIsLimit D).conePointUniqueUpToIso (limit.isLimit _)

private lemma sheafLimitIso_hom_π {T : TopCat.{u}} (D : ℕᵒᵖ ⥤ TopCat.Sheaf CommRingCat.{u} T)
    (j : ℕᵒᵖ) : (sheafLimitIso D).hom ≫ limit.π (D ⋙ sheafToPresheaf _ _) j = (limit.π D j).hom :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ j

private lemma sheafLimitIso_inv_π {T : TopCat.{u}} (D : ℕᵒᵖ ⥤ TopCat.Sheaf CommRingCat.{u} T)
    (j : ℕᵒᵖ) : (sheafLimitIso D).inv ≫ (limit.π D j).hom = limit.π (D ⋙ sheafToPresheaf _ _) j :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ j

include hφ in
/-- The structure sheaf of `X̂'_{Y'}` is the pushforward along `φ_0` of that of `X̂_Y`: the
compatible isomorphisms of the inverse systems induce an isomorphism of the limit sheaves. -/
def neighborhoodIsoSheafIso :
    (limit I'.formalCompletionDiagram).presheaf ≅
      (neighborhoodIsoBase I I' φ).hom _* (limit I.formalCompletionDiagram).presheaf :=
  haveI : PreservesLimitsOfShape ℕᵒᵖ
      (TopCat.Presheaf.pushforward CommRingCat.{u} (neighborhoodIsoBase I I' φ).hom) :=
    inferInstanceAs (PreservesLimitsOfShape ℕᵒᵖ ((Functor.whiskeringLeft _ _ _).obj _))
  sheafLimitIso I'.formalCompletionDiagram ≪≫
    HasLimit.isoOfNatIso (@asIso _ _ _ _ (neighborhoodIsoCompare I I' φ hφ)
      (isIso_neighborhoodIsoCompare I I' φ hφ)) ≪≫
    (preservesLimitIso (TopCat.Presheaf.pushforward _ (neighborhoodIsoBase I I' φ).hom)
      (I.formalCompletionDiagram ⋙ sheafToPresheaf _ _)).symm ≪≫
    (TopCat.Presheaf.pushforward _ (neighborhoodIsoBase I I' φ).hom).mapIso
      (sheafLimitIso I.formalCompletionDiagram).symm

lemma neighborhoodIsoSheafIso_hom_π (n : ℕ) :
    (neighborhoodIsoSheafIso I I' φ hφ).hom ≫
        (TopCat.Presheaf.pushforward _ (neighborhoodIsoBase I I' φ).hom).map
          (limit.π I.formalCompletionDiagram (op n)).hom =
      (limit.π I'.formalCompletionDiagram (op n)).hom ≫ neighborhoodIsoApp I I' φ hφ n := by
  have : PreservesLimitsOfShape ℕᵒᵖ
      (TopCat.Presheaf.pushforward CommRingCat.{u} (neighborhoodIsoBase I I' φ).hom) :=
    inferInstanceAs (PreservesLimitsOfShape ℕᵒᵖ ((Functor.whiskeringLeft _ _ _).obj _))
  have h1 := sheafLimitIso_inv_π I.formalCompletionDiagram (op n)
  have h2 := preservesLimitIso_inv_π
    (TopCat.Presheaf.pushforward _ (neighborhoodIsoBase I I' φ).hom)
    (I.formalCompletionDiagram ⋙ sheafToPresheaf _ _) (op n)
  have h3 := sheafLimitIso_hom_π I'.formalCompletionDiagram (op n)
  simp only [neighborhoodIsoSheafIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc]
  erw [← Functor.map_comp, h1, h2, HasLimit.isoOfNatIso_hom_π, ← Category.assoc, h3]
  rfl

include hφ in
/-- **Formal completions along compatible neighbourhoods are isomorphic.** A family of
isomorphisms `φ_n : Y_(n+1) ≅ Y'_(n+1)` of the infinitesimal neighbourhoods of two closed
subschemes, compatible with the inclusions `Y_(n+1) ⟶ Y_(n+2)`, induces an isomorphism of
the formal completions `X̂_Y ≅ X̂'_{Y'}` of locally ringed spaces: on spaces it is `φ_0`, and on
structure sheaves it is the isomorphism of the inverse limits of the `𝒪_{Y_(n+1)}` induced by the
`φ_n`. -/
def formalCompletionIsoOfNeighborhoodIso : I.formalCompletion ≅ I'.formalCompletion :=
  LocallyRingedSpace.isoOfSheafedSpaceIso (SheafedSpace.isoMk
    (PresheafedSpace.isoOfComponents (neighborhoodIsoBase I I' φ)
      (neighborhoodIsoSheafIso I I' φ hφ).symm))

/-- On points, `formalCompletionIsoOfNeighborhoodIso` is `φ_0`. -/
lemma formalCompletionIsoOfNeighborhoodIso_hom_base_apply (y : I.formalCompletion) :
    (formalCompletionIsoOfNeighborhoodIso I I' φ hφ).hom.base y = (φ 0).hom y :=
  rfl

/-- On sections, `formalCompletionIsoOfNeighborhoodIso` followed by the projection to
`𝒪_{Y_(n+1)}` is the projection to `𝒪_{Y'_(n+1)}` followed by pullback along `φ_n`. -/
lemma formalCompletionIsoOfNeighborhoodIso_hom_c_app_π (n : ℕ)
    (V : Opens (I'.infinitesimalNeighborhood 1)) :
    (formalCompletionIsoOfNeighborhoodIso I I' φ hφ).hom.c.app (op V) ≫
        (limit.π I.formalCompletionDiagram (op n)).hom.app
          (op ((Opens.map (formalCompletionIsoOfNeighborhoodIso I I' φ hφ).hom.base).obj V)) =
      (limit.π I'.formalCompletionDiagram (op n)).hom.app (op V) ≫
        (φ n).hom.appLE _ _ (functor_obj_map_neighborhoodIso I I' φ hφ n V).le :=
  congrArg (fun f => f.app (op V)) (neighborhoodIsoSheafIso_hom_π I I' φ hφ n)

end QuasicoherentIdealSubsheaf

/-! ### The infinitesimal neighbourhoods of `Spec B` along `V(J)` -/

section SpecNeighborhood

variable (B : Type u) [CommRing B] (J : Ideal B)

/-- The kernel of the map on global sections of `Spec (B ⧸ K) ⟶ Spec B` is `K`. -/
private lemma ker_appTop_spec_map_quotient_mk (K : Ideal B) :
    RingHom.ker (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))).appTop.hom =
      K.map (Scheme.ΓSpecIso (CommRingCat.of B)).commRingCatIsoToRingEquiv.symm := by
  rw [Ideal.map_symm]
  ext x
  have h := congrArg (fun f => f.hom x)
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk K)))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  rw [RingHom.mem_ker, Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
  change _ ↔ Ideal.Quotient.mk K ((Scheme.ΓSpecIso (CommRingCat.of B)).hom x) = 0
  rw [← h]
  exact (map_eq_zero_iff _
    (Scheme.ΓSpecIso (CommRingCat.of (B ⧸ K))).commRingCatIsoToRingEquiv.injective).symm

/-- The ideal data of the `(n+1)`-st power of the ideal sheaf attached to `J` is the kernel of
`Spec (B ⧸ J ^ (n + 1)) ⟶ Spec B`. -/
private lemma quasicoherentIdealSubsheafEquiv_specIdealSubsheaf_pow (n : ℕ) :
    quasicoherentIdealSubsheafEquiv (specIdealSubsheaf B J ^ (n + 1)) =
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J ^ (n + 1))))).ker := by
  rw [quasicoherentIdealSubsheafEquiv_pow, specIdealSubsheaf, Equiv.apply_symm_apply]
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Scheme.Hom.ker_apply, Scheme.Hom.ker_apply]
  change (RingHom.ker (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).appTop.hom) ^ (n + 1) =
    RingHom.ker (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J ^ (n + 1))))).appTop.hom
  rw [ker_appTop_spec_map_quotient_mk, ker_appTop_spec_map_quotient_mk, Ideal.map_pow]

/-- The closed subschemes cut out by equal ideal data are isomorphic over the ambient scheme. -/
private def subschemeIsoOfEq' {Z : Scheme.{u}} {K L : Z.IdealSheafData} (h : K = L) :
    K.subscheme ≅ L.subscheme where
  hom := Scheme.IdealSheafData.inclusion h.ge
  inv := Scheme.IdealSheafData.inclusion h.le
  hom_inv_id := by simp
  inv_hom_id := by simp

/-- The `(n+1)`-st infinitesimal neighbourhood of `V(J)` in `Spec B` is `Spec (B ⧸ J ^ (n + 1))`,
over `Spec B`. -/
private def specNeighborhoodIso (n : ℕ) :
    (specIdealSubsheaf B J).infinitesimalNeighborhood (n + 1) ≅
      Spec (CommRingCat.of (B ⧸ J ^ (n + 1))) :=
  subschemeIsoOfEq' (quasicoherentIdealSubsheafEquiv_specIdealSubsheaf_pow B J n) ≪≫
    (asIso (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J ^ (n + 1))))).toImage).symm

@[reassoc]
private lemma specNeighborhoodIso_hom_comp (n : ℕ) :
    (specNeighborhoodIso B J n).hom ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J ^ (n + 1)))) =
      (specIdealSubsheaf B J).infinitesimalNeighborhoodι (n + 1) := by
  have hf : inv (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J ^ (n + 1))))).toImage ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J ^ (n + 1)))) =
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J ^ (n + 1))))).imageι := by
    rw [IsIso.inv_comp_eq, Scheme.Hom.toImage_imageι]
  change (Scheme.IdealSheafData.inclusion _ ≫ inv _) ≫ _ = _
  rw [Category.assoc, hf]
  exact Scheme.IdealSheafData.inclusion_subschemeι _

@[reassoc]
private lemma specNeighborhoodIso_inv_comp (n : ℕ) :
    (specNeighborhoodIso B J n).inv ≫
        (specIdealSubsheaf B J).infinitesimalNeighborhoodι (n + 1) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J ^ (n + 1)))) := by
  rw [Iso.inv_comp_eq, specNeighborhoodIso_hom_comp]

/-- The transition map between consecutive quotients by powers of `J`. -/
private abbrev quotientPowSucc (n : ℕ) : B ⧸ J ^ (n + 2) →+* B ⧸ J ^ (n + 1) :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))

/-- The identifications `Y_(n+1) ≅ Spec (B ⧸ J ^ (n + 1))` are compatible with the inclusions
`Y_(n+1) ⟶ Y_(n+2)`. -/
private lemma infinitesimalNeighborhoodSucc_specNeighborhoodIso (n : ℕ) :
    (specIdealSubsheaf B J).infinitesimalNeighborhoodSucc n ≫
        (specNeighborhoodIso B J (n + 1)).hom =
      (specNeighborhoodIso B J n).hom ≫
        Spec.map (CommRingCat.ofHom (quotientPowSucc B J n)) := by
  rw [← cancel_mono (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J ^ (n + 1 + 1))))),
    Category.assoc, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    Ideal.Quotient.factor_comp_mk, specNeighborhoodIso_hom_comp, specNeighborhoodIso_hom_comp]
  exact Scheme.IdealSheafData.inclusion_subschemeι _

end SpecNeighborhood

/-! ### Completion -/

section Completion

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)

attribute [local instance] isNoetherianRing_adicCompletion

/-- The ideal `Î = I Â` of the `I`-adic completion `Â` of `A`. -/
local notation "Î" => I.map (algebraMap A (AdicCompletion I A))

/-- The isomorphism `Â ⧸ Î ^ (n + 1) ≅ A ⧸ I ^ (n + 1)` induced by reduction. -/
private def completionQuotientEquiv (n : ℕ) :
    AdicCompletion I A ⧸ Î ^ (n + 1) ≃+* A ⧸ I ^ (n + 1) :=
  (Ideal.quotEquivOfEq (Ideal.map_pow _ _ _).symm).trans
    (exists_adicCompletionQuotientRingEquiv I n).choose

private lemma completionQuotientEquiv_comp_mk (n : ℕ) :
    (completionQuotientEquiv A I n).toRingHom.comp (Ideal.Quotient.mk (Î ^ (n + 1))) =
      (AdicCompletion.evalₐ I (n + 1)).toRingHom := by
  ext x
  have h := congrArg (fun f => f x) (exists_adicCompletionQuotientRingEquiv I n).choose_spec
  change (exists_adicCompletionQuotientRingEquiv I n).choose
    (Ideal.quotEquivOfEq _ (Ideal.Quotient.mk _ x)) = _
  rw [Ideal.quotEquivOfEq_mk]
  exact h

omit [IsNoetherianRing A] in
private lemma factor_evalₐ_succ (n : ℕ) (x : AdicCompletion I A) :
    quotientPowSucc A I n (AdicCompletion.evalₐ I (n + 2) x) =
      AdicCompletion.evalₐ I (n + 1) x := by
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective I A x
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, Ideal.Quotient.factor_mk]
  exact AdicCompletion.Ideal.mk_eq_mk I (Nat.le_succ (n + 1)) s

/-- **The infinitesimal neighbourhoods of `Spf_I(A)` and `Spf_Î(Â)` agree.** The isomorphism
`Y_(n+1) ≅ Y'_(n+1)` between the closed subschemes of `Spec A` and `Spec Â` cut out by `I ^ (n + 1)`
and `Î ^ (n + 1)`, through `Spec (A ⧸ I ^ (n + 1)) ≅ Spec (Â ⧸ Î ^ (n + 1))`. -/
def spfCompletionNeighborhoodIso (n : ℕ) :
    (specIdealSubsheaf A I).infinitesimalNeighborhood (n + 1) ≅
      (specIdealSubsheaf (AdicCompletion I A) Î).infinitesimalNeighborhood (n + 1) :=
  specNeighborhoodIso A I n ≪≫
    Scheme.Spec.mapIso (completionQuotientEquiv A I n).toCommRingCatIso.op ≪≫
    (specNeighborhoodIso (AdicCompletion I A) Î n).symm

private lemma spfCompletionNeighborhoodIso_hom_comp_ι (n : ℕ) :
    (spfCompletionNeighborhoodIso A I n).hom ≫
        (specIdealSubsheaf (AdicCompletion I A) Î).infinitesimalNeighborhoodι (n + 1) =
      (specNeighborhoodIso A I n).hom ≫
        Spec.map (CommRingCat.ofHom (AdicCompletion.evalₐ I (n + 1)).toRingHom) := by
  simp only [spfCompletionNeighborhoodIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    specNeighborhoodIso_inv_comp]
  refine congrArg (_ ≫ ·) ?_
  change Spec.map (CommRingCat.ofHom (completionQuotientEquiv A I n).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Î ^ (n + 1)))) = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (completionQuotientEquiv_comp_mk A I n)

/-- The isomorphisms `spfCompletionNeighborhoodIso` are compatible with the inclusions
`Y_(n+1) ⟶ Y_(n+2)`. -/
lemma spfCompletionNeighborhoodIso_hom_comp_succ (n : ℕ) :
    (spfCompletionNeighborhoodIso A I n).hom ≫
        (specIdealSubsheaf (AdicCompletion I A) Î).infinitesimalNeighborhoodSucc n =
      (specIdealSubsheaf A I).infinitesimalNeighborhoodSucc n ≫
        (spfCompletionNeighborhoodIso A I (n + 1)).hom := by
  have e1 : (specIdealSubsheaf (AdicCompletion I A) Î).infinitesimalNeighborhoodSucc n ≫
      (specIdealSubsheaf (AdicCompletion I A) Î).infinitesimalNeighborhoodι (n + 1 + 1) =
        (specIdealSubsheaf (AdicCompletion I A) Î).infinitesimalNeighborhoodι (n + 1) :=
    Scheme.IdealSheafData.inclusion_subschemeι _
  rw [← cancel_mono ((specIdealSubsheaf (AdicCompletion I A) Î).infinitesimalNeighborhoodι
      (n + 1 + 1)), Category.assoc, Category.assoc, e1, spfCompletionNeighborhoodIso_hom_comp_ι,
    spfCompletionNeighborhoodIso_hom_comp_ι,
    reassoc_of% infinitesimalNeighborhoodSucc_specNeighborhoodIso,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 3
  ext x
  exact (factor_evalₐ_succ A I n x).symm

/-- The isomorphisms `spfCompletionNeighborhoodIso` lie over `Spec A`: composed with the closed
immersion into `Spec Â` and with `Spec Â ⟶ Spec A`, they give the closed immersion
`Y_(n+1) ⟶ Spec A`. -/
@[reassoc]
lemma spfCompletionNeighborhoodIso_hom_comp_ι_comp (n : ℕ) :
    (spfCompletionNeighborhoodIso A I n).hom ≫
        (specIdealSubsheaf (AdicCompletion I A) Î).infinitesimalNeighborhoodι (n + 1) ≫
          Spec.map (CommRingCat.ofHom (algebraMap A (AdicCompletion I A))) =
      (specIdealSubsheaf A I).infinitesimalNeighborhoodι (n + 1) := by
  have h : (AdicCompletion.evalₐ I (n + 1)).toRingHom.comp (algebraMap A (AdicCompletion I A)) =
      Ideal.Quotient.mk (I ^ (n + 1)) :=
    RingHom.ext fun x => (AdicCompletion.evalₐ I (n + 1)).commutes x
  rw [reassoc_of% spfCompletionNeighborhoodIso_hom_comp_ι, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, h, specNeighborhoodIso_hom_comp]

/-- **The formal spectrum is invariant under adic completion** (a project-authored comparison
supporting Hartshorne II.9, Proposition 9.6, pp. 197–198, where an affine Noetherian ring is
replaced by its completion). For a Noetherian ring `A`, an ideal `I`, the `I`-adic completion `Â`
and `Î = I Â`, the isomorphisms `Spec (A ⧸ I ^ (n + 1)) ≅ Spec (Â ⧸ Î ^ (n + 1))` of the
infinitesimal neighbourhoods induce an isomorphism `Spf_I(A) ≅ Spf_Î(Â)` of locally ringed
spaces. -/
def spfCompletionIso :
    Spf A I ≅ Spf (AdicCompletion I A) Î :=
  QuasicoherentIdealSubsheaf.formalCompletionIsoOfNeighborhoodIso _ _
    (spfCompletionNeighborhoodIso A I) (spfCompletionNeighborhoodIso_hom_comp_succ A I)

/-- On points, `spfCompletionIso` lies over `Spec A`: a point of `V(Î) ⊆ Spec Â` goes to its image
under `Spec Â ⟶ Spec A`, the point of `V(I)` it came from. -/
theorem spec_map_algebraMap_spfCompletionIso_hom_base (y : Spf A I) :
    Spec.map (CommRingCat.ofHom (algebraMap A (AdicCompletion I A)))
        ((specIdealSubsheaf (AdicCompletion I A) Î).infinitesimalNeighborhoodι 1
          ((spfCompletionIso A I).hom.base y)) =
      (specIdealSubsheaf A I).infinitesimalNeighborhoodι 1 y := by
  have h : (spfCompletionNeighborhoodIso A I 0).hom ≫
      (specIdealSubsheaf (AdicCompletion I A) Î).infinitesimalNeighborhoodι 1 ≫
        Spec.map (CommRingCat.ofHom (algebraMap A (AdicCompletion I A))) =
      (specIdealSubsheaf A I).infinitesimalNeighborhoodι 1 :=
    spfCompletionNeighborhoodIso_hom_comp_ι_comp A I 0
  rw [← h]
  rfl

/-- On sections, `spfCompletionIso` followed by the projection to `𝒪_{Y_(n+1)}` is the projection
to `𝒪_{Y'_(n+1)}` followed by pullback along `spfCompletionNeighborhoodIso`, where `Y_(n+1)` and
`Y'_(n+1)` are cut out by `I ^ (n + 1)` and `Î ^ (n + 1)`. -/
theorem spfCompletionIso_hom_c_app_π (n : ℕ)
    (V : Opens ((specIdealSubsheaf (AdicCompletion I A) Î).infinitesimalNeighborhood 1)) :
    (spfCompletionIso A I).hom.c.app (op V) ≫
        (limit.π (specIdealSubsheaf A I).formalCompletionDiagram (op n)).hom.app
          (op ((Opens.map (spfCompletionIso A I).hom.base).obj V)) =
      (limit.π (specIdealSubsheaf (AdicCompletion I A) Î).formalCompletionDiagram
          (op n)).hom.app (op V) ≫
        (spfCompletionNeighborhoodIso A I n).hom.appLE _ _
          (QuasicoherentIdealSubsheaf.functor_obj_map_neighborhoodIso _ _ _
            (spfCompletionNeighborhoodIso_hom_comp_succ A I) n V).le :=
  QuasicoherentIdealSubsheaf.formalCompletionIsoOfNeighborhoodIso_hom_c_app_π _ _ _ _ n V

/-- **The formal spectrum is invariant under adic completion** (a project-authored comparison
supporting Hartshorne II.9, Proposition 9.6, pp. 197–198). For a Noetherian ring `A` and an ideal
`I`, with `I`-adic completion `Â` and `Î = I Â`, there is an isomorphism of locally ringed spaces
`Spf_I(A) ≅ Spf_Î(Â)` lying over `Spec A` on points: it sends a point of `V(I)` to the point of
`V(Î) ⊆ Spec Â` mapping to it under `Spec Â ⟶ Spec A`. On sections it is induced by the
isomorphisms `Â ⧸ Î ^ (n + 1) ≅ A ⧸ I ^ (n + 1)` (`spfCompletionIso_hom_c_app_π`). -/
theorem spf_completion_invariant :
    ∃ e : Spf A I ≅ Spf (AdicCompletion I A) Î, ∀ y : Spf A I,
      Spec.map (CommRingCat.ofHom (algebraMap A (AdicCompletion I A)))
          ((specIdealSubsheaf (AdicCompletion I A) Î).infinitesimalNeighborhoodι 1 (e.hom.base y)) =
        (specIdealSubsheaf A I).infinitesimalNeighborhoodι 1 y :=
  ⟨spfCompletionIso A I, spec_map_algebraMap_spfCompletionIso_hom_base A I⟩

end Completion

end Hartshorne

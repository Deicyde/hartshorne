/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.RingedSpace.PicardGroup

/-!
# Tensoring with an invertible sheaf is an autoequivalence

Let `(X, 𝒪_X)` be a ringed space and `L` an invertible `𝒪_X`-module. Then `F ↦ L ⊗ F` is an
autoequivalence of the category of `𝒪_X`-modules, with quasi-inverse `F ↦ L^∨ ⊗ F`
(`invertibleTensorEquivalence`). It is built from the natural isomorphisms
`M ⊗ (N ⊗ F) ≅ (M ⊗ N) ⊗ F ≅ 𝒪_X ⊗ F ≅ F`, available whenever `M ⊗ N ≅ 𝒪_X`
(`tensorLeftCompIsoOfTensorIso`). We also show:

* if `L` is invertible and `F` is locally free of rank `r`, then `L ⊗ F` is locally free of
  rank `r` (`isLocallyFreeOfRank_moduleSheafTensor_of_isInvertible`);
* an `𝒪_X`-module is locally free of rank `0` exactly when it is a zero object
  (`isZero_of_isLocallyFreeOfRank_zero`, `isLocallyFreeOfRank_zero_of_isZero`).
-/

universe u

open CategoryTheory Opposite TopologicalSpace Limits

namespace Hartshorne

namespace Ringed

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

set_option hygiene false in
/-- `𝒪_X`-modules. -/
local notation "𝓜" => SheafOfModules.{u} (ringCatSheafOf R)

set_option hygiene false in
/-- Sections of the structure sheaf over an open. -/
local notation3 "𝒪(" U ")" => R.obj.obj (Opposite.op U)

/-- Sections of a module sheaf over an open, as an abelian group. -/
local notation3 "Γ(" M ", " U ")" => (PresheafOfModules.presheaf (SheafOfModules.val M)).obj
  (Opposite.op U)

section TensorFunctor

/-- The functor `F ↦ M ⊗ F` on `𝒪_X`-modules. -/
noncomputable def moduleSheafTensorLeft (M : 𝓜) : 𝓜 ⥤ 𝓜 where
  obj F := moduleSheafTensor M F
  map φ := modulesTensorMap (𝟙 M) φ
  map_id F := modulesTensorMap_id M F
  map_comp φ ψ := by
    rw [← modulesTensorMap_comp, Category.id_comp]

/-- The associativity isomorphism `(M ⊗ N) ⊗ F ≅ M ⊗ (N ⊗ F)` is natural in `F`. -/
lemma moduleSheafTensorAssoc_hom_naturality (M N : 𝓜) {F F' : 𝓜} (φ : F ⟶ F') :
    modulesTensorMap (𝟙 (moduleSheafTensor M N)) φ ≫ (moduleSheafTensorAssoc M N F').hom =
      (moduleSheafTensorAssoc M N F).hom ≫ modulesTensorMap (𝟙 M) (modulesTensorMap (𝟙 N) φ) := by
  refine moduleSheafTensor_assoc_hom_ext fun U m n f => ?_
  change sectionsMap (moduleSheafTensorAssoc M N F').hom U
      (sectionsMap (modulesTensorMap (𝟙 (moduleSheafTensor M N)) φ) U _) =
    sectionsMap (modulesTensorMap (𝟙 M) (modulesTensorMap (𝟙 N) φ)) U
      (sectionsMap (moduleSheafTensorAssoc M N F).hom U _)
  have h1 := modulesTensorMap_tmul (𝟙 (moduleSheafTensor M N)) φ
    ((moduleSheafTensorBilinear M N).app (op U) m n) f
  refine ((congrArg (sectionsMap (moduleSheafTensorAssoc M N F').hom U) h1).trans
    ((assocTrilinear M N F').tensorDesc_tmul m n _)).trans ?_
  refine Eq.trans ?_ (congrArg (sectionsMap (modulesTensorMap (𝟙 M) (modulesTensorMap (𝟙 N) φ)) U)
    ((assocTrilinear M N F).tensorDesc_tmul m n f)).symm
  refine Eq.trans ?_ (modulesTensorMap_tmul (𝟙 M) (modulesTensorMap (𝟙 N) φ) m
    ((moduleSheafTensorBilinear N F).app (op U) n f)).symm
  exact congrArg ((moduleSheafTensorBilinear M (moduleSheafTensor N F')).app (op U) m)
    (modulesTensorMap_tmul (𝟙 N) φ n f).symm

/-- The unit isomorphism `𝒪_X ⊗ F ≅ F` is natural in `F`. -/
lemma moduleSheafUnitTensor_hom_naturality {F F' : 𝓜} (φ : F ⟶ F') :
    modulesTensorMap (𝟙 (structureModule R)) φ ≫ (moduleSheafUnitTensor F').hom =
      (moduleSheafUnitTensor F).hom ≫ φ := by
  refine modulesTensor_hom_ext fun U r f => ?_
  change sectionsMap (moduleSheafUnitTensor F').hom U
      (sectionsMap (modulesTensorMap (𝟙 (structureModule R)) φ) U _) =
    sectionsMap φ U (sectionsMap (moduleSheafUnitTensor F).hom U _)
  refine ((congrArg (sectionsMap (moduleSheafUnitTensor F').hom U)
    (modulesTensorMap_tmul (𝟙 (structureModule R)) φ r f)).trans
    (moduleSheafTensorHomEquiv_symm_tmul (unitSMulBilinear F') _ _)).trans ?_
  refine Eq.trans ?_ (congrArg (sectionsMap φ U)
    (moduleSheafTensorHomEquiv_symm_tmul (unitSMulBilinear F) r f)).symm
  exact ((φ.val.app (op U)).hom.map_smul (show 𝒪(U) from r) f).symm

variable {M N : 𝓜}

/-- Given `e : M ⊗ N ≅ 𝒪_X`, the natural isomorphism `M ⊗ (N ⊗ F) ≅ F`. -/
noncomputable def tensorLeftCompIsoOfTensorIso
    (e : @Iso 𝓜 _ (moduleSheafTensor M N) (structureModule R)) :
    moduleSheafTensorLeft N ⋙ moduleSheafTensorLeft M ≅ 𝟭 𝓜 :=
  NatIso.ofComponents
    (fun F => (moduleSheafTensorAssoc M N F).symm ≪≫ moduleSheafTensorIsoOfIso e (Iso.refl F) ≪≫
      moduleSheafUnitTensor F)
    (fun {F F'} φ => by
      change modulesTensorMap (𝟙 M) (modulesTensorMap (𝟙 N) φ) ≫
          ((moduleSheafTensorAssoc M N F').inv ≫ modulesTensorMap e.hom (𝟙 F') ≫
            (moduleSheafUnitTensor F').hom) =
        ((moduleSheafTensorAssoc M N F).inv ≫ modulesTensorMap e.hom (𝟙 F) ≫
          (moduleSheafUnitTensor F).hom) ≫ φ
      have hA : modulesTensorMap (𝟙 M) (modulesTensorMap (𝟙 N) φ) ≫
          (moduleSheafTensorAssoc M N F').inv =
          (moduleSheafTensorAssoc M N F).inv ≫ modulesTensorMap (𝟙 (moduleSheafTensor M N)) φ := by
        rw [Iso.comp_inv_eq, Category.assoc, moduleSheafTensorAssoc_hom_naturality,
          Iso.inv_hom_id_assoc]
      rw [← Category.assoc, hA, Category.assoc, Category.assoc, Category.assoc,
        ← moduleSheafUnitTensor_hom_naturality]
      congr 1
      rw [← Category.assoc, ← modulesTensorMap_comp, ← Category.assoc, ← modulesTensorMap_comp]
      simp only [Category.id_comp, Category.comp_id])

/-- **Tensoring with an invertible sheaf is an autoequivalence**: for an invertible `L`, the
functor `F ↦ L ⊗ F` is an equivalence, with quasi-inverse `F ↦ L^∨ ⊗ F`. -/
noncomputable def invertibleTensorEquivalence {L : 𝓜} (hL : IsInvertible L) : 𝓜 ≌ 𝓜 :=
  CategoryTheory.Equivalence.mk (moduleSheafTensorLeft L)
    (moduleSheafTensorLeft (moduleSheafDual L))
    (tensorLeftCompIsoOfTensorIso
      (moduleSheafTensorComm _ _ ≪≫ moduleSheafDualEvalIso L hL)).symm
    (tensorLeftCompIsoOfTensorIso (moduleSheafDualEvalIso L hL))

end TensorFunctor

section Rank

/-- **Twisting preserves the rank**: if `L` is invertible and `F` is locally free of rank `r`,
then `L ⊗ F` is locally free of rank `r`. -/
theorem isLocallyFreeOfRank_moduleSheafTensor_of_isInvertible {L F : 𝓜} {r : ℕ}
    (hL : IsInvertible L) (hF : IsLocallyFreeOfRank F r) :
    IsLocallyFreeOfRank (moduleSheafTensor L F) r := by
  refine isLocallyFreeOfRank_of_isLocalFrame fun x => ?_
  obtain ⟨U₁, e, hx₁, he⟩ := exists_isLocalFrame_of_isLocallyFreeOfRank hL x
  obtain ⟨U₂, f, hx₂, hf⟩ := exists_isLocalFrame_of_isLocallyFreeOfRank hF x
  have hd := (he.restrictLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).dual
  have hf' := hf.restrictLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)
  exact ⟨U₁ ⊓ U₂, _, ⟨hx₁, hx₂⟩, ((hd.homFrame hf').of_iso (tensorIsoHomDual hL F).symm).reindex
    (Equiv.uniqueProd (ULift.{u} (Fin r)) (ULift.{u} (Fin 1))).symm⟩

private lemma sections_subsingleton_of_isZero {F : 𝓜} (hF : IsZero F) (V : Opens X) :
    Subsingleton Γ(F, V) := by
  refine ⟨fun a b => ?_⟩
  have h : ∀ c : Γ(F, V), c = 0 := fun c => by
    have := congrArg (fun φ : F ⟶ F => sectionsMap φ V c) (hF.eq_of_src (𝟙 F) 0)
    exact this
  rw [h a, h b]

/-- A zero `𝒪_X`-module is locally free of rank `0`. -/
theorem isLocallyFreeOfRank_zero_of_isZero {F : 𝓜} (hF : IsZero F) :
    IsLocallyFreeOfRank F 0 := by
  refine isLocallyFreeOfRank_of_isLocalFrame fun x => ⟨⊤, fun i => i.down.elim0, trivial, ?_⟩
  intro V h
  have := sections_subsingleton_of_isZero hF V
  refine ⟨fun a b _ => funext fun i => i.down.elim0, fun c => ⟨fun i => i.down.elim0, ?_⟩⟩
  exact Subsingleton.elim _ _

/-- An `𝒪_X`-module that is locally free of rank `0` is a zero object. -/
theorem isZero_of_isLocallyFreeOfRank_zero {F : 𝓜} (hF : IsLocallyFreeOfRank F 0) :
    IsZero F := by
  have hloc : ∀ x : X, ∃ U : Opens X, x ∈ U ∧ ∀ V ≤ U, ∀ c : Γ(F, V), c = 0 := fun x => by
    obtain ⟨U, e, hx, he⟩ := exists_isLocalFrame_of_isLocallyFreeOfRank hF x
    refine ⟨U, hx, fun V hV c => ?_⟩
    obtain ⟨a, rfl⟩ := (he V hV).2 c
    obtain ⟨b, hb⟩ := (he V hV).2 0
    rw [← hb]
    exact congrArg _ (funext fun i => i.down.elim0)
  have hzero : ∀ (W : Opens X) (c : Γ(F, W)), c = 0 := by
    intro W c
    refine TopCat.Presheaf.IsSheaf.section_ext
      ((SheafOfModules.toSheaf _).obj F).2 fun y hy => ?_
    obtain ⟨U, hyU, hU⟩ := hloc y
    refine ⟨W ⊓ U, inf_le_left, ⟨hy, hyU⟩, ?_⟩
    exact (hU _ inf_le_right _).trans (hU _ inf_le_right _).symm
  refine (IsZero.iff_id_eq_zero F).mpr ?_
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext c
  exact (hzero U.unop _).trans (hzero U.unop _).symm

end Rank

end Ringed

end Hartshorne

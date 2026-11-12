/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ProjectiveGlobalSectionsFinite
import Hartshorne.Scheme.ProjectiveMorphismCalculus
import Hartshorne.Scheme.ProjectiveSpaceProper
import Hartshorne.Scheme.PullbackQuasicoherent
import Hartshorne.Scheme.QcqsPushforwardQuasicoherent

/-!
# Coherence of projective pushforward

Hartshorne, *Algebraic Geometry*, II, Corollary 5.20 (p. 123).

Let `f : X ⟶ Y` be a projective morphism of schemes of finite type over a field `k`. For every
coherent sheaf `F` on `X`, the direct image `f_* F` is coherent
(`isCoherent_pushforward_of_projective`).

## Proof

Following Hartshorne. The pushforward `f_* F` is quasi-coherent because `f` is proper, hence
quasi-compact and quasi-separated (`isQuasicoherent_pushforward_of_qcqs`). Coherence is then checked
on the affine opens `V = Spec A` of `Y` (`coherent_affine_local_tfae`, `Y` is locally
Noetherian). Such an `A` is a finitely generated `k`-algebra, the restriction `f⁻¹ V ⟶ V` is
projective (projectivity is stable under base change), and `Γ(V, f_* F) = Γ(f⁻¹ V, F)` is a
finitely generated `A`-module by Theorem 5.19 (`moduleFinite_globalSections_of_projective`)
applied to the coherent restriction `F|_{f⁻¹ V}`.

Only the finite type of `Y` over `k` enters the proof
(`isCoherent_pushforward_of_projective_of_locallyOfFiniteType` assumes just that `Y` is locally
of finite type over `k`).
-/

universe u

noncomputable section

namespace Hartshorne

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace ProjectivePushforwardCoherent

/-- Projectivity is stable under base change. -/
private theorem projective_of_isPullback {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {fst : X' ⟶ X} {f' : X' ⟶ Y'} (h : IsPullback fst f' f g) (hf : Projective f) :
    Projective f' := by
  obtain ⟨n, i, hi, rfl⟩ := hf
  have hsq := projectiveSpaceOverSchemeMap_isPullback n g
  let j : X' ⟶ projectiveSpaceOverScheme n Y' :=
    hsq.lift (fst ≫ i) f' (by rw [Category.assoc, h.w])
  have hj₁ : j ≫ projectiveSpaceOverSchemeMap n g = fst ≫ i := hsq.lift_fst _ _ _
  have hj₂ : j ≫ projectiveSpaceOverSchemeProjection n Y' = f' := hsq.lift_snd _ _ _
  have htop : IsPullback fst j i (projectiveSpaceOverSchemeMap n g) :=
    IsPullback.of_bot (by rwa [hj₂]) hj₁.symm hsq
  have : IsClosedImmersion j := MorphismProperty.of_isPullback (P := @IsClosedImmersion) htop hi
  exact Projective.mk n j hj₂

/-- Restriction maps around `f.app` collapse to `f.app U`. -/
private theorem map_app_map_map {X Y : Scheme.{u}} (f : X ⟶ Y) {U W : Y.Opens}
    (k : op U ⟶ op W) {V : X.Opens} (i : op (f ⁻¹ᵁ W) ⟶ op V) (j : op V ⟶ op (f ⁻¹ᵁ U)) :
    Y.presheaf.map k ≫ (f.app W ≫ X.presheaf.map i) ≫ X.presheaf.map j = f.app U := by
  rw [Category.assoc, f.naturality_assoc, ← Functor.map_comp, ← Functor.map_comp,
    Subsingleton.elim (_ ≫ i ≫ j) (𝟙 _), CategoryTheory.Functor.map_id, Category.comp_id]

/-- The ring map `Γ(Y, U) → Γ(f⁻¹ U, ⊤)` of `f ∣_ U`, followed by the restriction to
`f⁻¹ U ⊆ X`, is `f.app U`. -/
private theorem topIso_inv_morphismRestrict_appTop_map {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) :
    U.topIso.inv ≫ (f ∣_ U).appTop ≫
      X.presheaf.map (eqToHom (Scheme.Opens.ι_image_top (f ⁻¹ᵁ U)).symm).op = f.app U := by
  rw [Scheme.Opens.topIso_inv, morphismRestrict_appTop]
  exact map_app_map_map f _ _ _

/-- Finiteness of the sections of `F` over `f⁻¹ U`, read on the open subscheme `f⁻¹ U`, gives
finiteness of the sections of `f_* F` over `U`. -/
private theorem finite_pushforward_sections {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules)
    (U : Y.Opens) (ρ : Γ(Y, U) ⟶ Γ(f ⁻¹ᵁ U, ⊤)) (hρ : ρ = U.topIso.inv ≫ (f ∣_ U).appTop)
    (h : Module.Finite Γ(Y, U)
      ((ModuleCat.restrictScalars ρ.hom).obj ((F.restrict (f ⁻¹ᵁ U).ι).val.obj (op ⊤)))) :
    Module.Finite Γ(Y, U) Γ((Scheme.Modules.pushforward f).obj F, U) := by
  subst hρ
  have hV := Scheme.Opens.ι_image_top (f ⁻¹ᵁ U)
  let e : Γ(F, (f ⁻¹ᵁ U).ι ''ᵁ ⊤) ≃+ Γ(F, f ⁻¹ᵁ U) :=
    (F.presheaf.mapIso (eqToIso hV.symm).op).addCommGroupIsoToAddEquiv
  refine (CoherentAux.finite_iff_of_ringEquiv_addEquiv
    (N := (ModuleCat.restrictScalars (U.topIso.inv ≫ (f ∣_ U).appTop).hom).obj
      ((F.restrict (f ⁻¹ᵁ U).ι).val.obj (op ⊤)))
    (N' := Γ((Scheme.Modules.pushforward f).obj F, U)) (RingEquiv.refl _) e
    (fun a n => ?_)).1 h
  have key := congr($(topIso_inv_morphismRestrict_appTop_map f U) a)
  change F.presheaf.map (eqToHom hV.symm).op
      (((f ⁻¹ᵁ U).ι.appIso ⊤).inv ((U.topIso.inv ≫ (f ∣_ U).appTop) a) •
        (show Γ(F, (f ⁻¹ᵁ U).ι ''ᵁ ⊤) from n)) =
    f.app U a • F.presheaf.map (eqToHom hV.symm).op n
  rw [Scheme.Modules.map_smul, Scheme.Opens.ι_appIso, Iso.refl_inv]
  exact congrArg (· • _) key

end ProjectivePushforwardCoherent

open ProjectivePushforwardCoherent in
/-- Generalizes **Hartshorne II, Corollary 5.20** to a target that is only locally of finite
type over the field, with no hypothesis on the source: let `k` be a field, `Y` a scheme locally
of finite type over `k` and `f : X ⟶ Y` projective. For every coherent sheaf `F` on `X`,
`f_* F` is coherent on `Y`. -/
theorem isCoherent_pushforward_of_projective_of_locallyOfFiniteType (k : Type u) [Field k]
    {X Y : Scheme.{u}} (pY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType pY] (f : X ⟶ Y)
    (hf : Projective f) (F : X.Modules) (hF : IsCoherent F) :
    IsCoherent ((Scheme.Modules.pushforward f).obj F) := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian pY
  have : IsProper f := hf.isProper
  have : ((Scheme.Modules.pushforward f).obj F).IsQuasicoherent :=
    have : F.IsQuasicoherent := hF.isQuasicoherent
    isQuasicoherent_pushforward_of_qcqs f F
  have hiso := ((quasicoherent_affine_local_tfae ((Scheme.Modules.pushforward f).obj F)).out 0 2).mp
    this
  refine ((coherent_affine_local_tfae _).out 3 0).mp ?_
  intro U
  refine ⟨?_, hiso U⟩
  -- the finitely generated `k`-algebra `Γ(Y, U)`
  have h₁ : RingHom.FiniteType (pY.appLE ⊤ U le_top).hom :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) pY inferInstance
      (⟨⊤, isAffineOpen_top _⟩ : (Spec (.of k)).affineOpens) U le_top
  have hft : RingHom.FiniteType ((Scheme.ΓSpecIso (.of k)).inv ≫ pY.appLE ⊤ U le_top).hom := by
    rw [CommRingCat.hom_comp]
    exact h₁.comp (RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.surjective)
  let _ := ((Scheme.ΓSpecIso (.of k)).inv ≫ pY.appLE ⊤ U le_top).hom.toAlgebra
  have : Algebra.FiniteType k Γ(Y, (U : Y.Opens)) := hft
  -- the restriction of `f` over `U` is projective
  have hU : IsAffineOpen (U : Y.Opens) := U.2
  have hproj : Projective (f ∣_ (U : Y.Opens) ≫ hU.isoSpec.hom) :=
    MorphismProperty.RespectsIso.postcomp _ _ _
      (projective_of_isPullback (isPullback_morphismRestrict f U).flip hf)
  have hF' : IsCoherent (F.restrict (f ⁻¹ᵁ (U : Y.Opens)).ι) :=
    isCoherent_of_iso ((Scheme.Modules.restrictFunctorIsoPullback _).app F).symm
      (isCoherent_pullback _ hF)
  have hfin := moduleFinite_globalSections_of_projective k (A := Γ(Y, (U : Y.Opens)))
    (f ∣_ (U : Y.Opens) ≫ hU.isoSpec.hom) hproj _ hF'
  refine finite_pushforward_sections f F U _ ?_ hfin
  rw [Scheme.Hom.comp_appTop, hU.isoSpec_hom_appTop, Category.assoc, Iso.inv_hom_id_assoc]

/-- **Hartshorne II, Corollary 5.20.** Let `f : X ⟶ Y` be a projective morphism of schemes of
finite type over a field `k`. For every coherent sheaf `F` on `X`, the direct image `f_* F` is
coherent on `Y`.

Only that `Y` is locally of finite type over `k` is used
(`isCoherent_pushforward_of_projective_of_locallyOfFiniteType`); the finite type of `X`, the
quasi-compactness of `Y` over `k` and the compatibility of `f` with the structure morphisms are
kept as in the source. -/
theorem isCoherent_pushforward_of_projective (k : Type u) [Field k] {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (hf : Projective f) (F : X.Modules)
    (hF : IsCoherent F) : IsCoherent ((Scheme.Modules.pushforward f).obj F) :=
  isCoherent_pushforward_of_projective_of_locallyOfFiniteType k (Y ↘ Spec (.of k)) f hf F hF

end Hartshorne

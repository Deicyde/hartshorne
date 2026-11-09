/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.QuasicoherentAbelianClosure
import Hartshorne.Scheme.AffineTildeChangeOfRings

/-!
# Pushforward of quasi-coherent sheaves along quasi-compact quasi-separated morphisms

Hartshorne, *Algebraic Geometry*, II, Proposition 5.8(c) (p. 115).
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicGeometry

namespace Hartshorne

namespace QcqsPushforward

noncomputable section

variable {X Y : Scheme.{u}}

/-- Quasi-coherence is invariant under isomorphism. -/
lemma isQuasicoherent_of_iso {M N : X.Modules} (e : M ≅ N) (hM : M.IsQuasicoherent) :
    N.IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e hM

/-- A restriction map of a module sheaf between equal opens is an isomorphism. -/
lemma isIso_presheaf_map_homOfLE (M : X.Modules) {U V : X.Opens} (h : U ≤ V) (h' : V ≤ U) :
    IsIso (M.presheaf.map (homOfLE h).op) := by
  have : IsIso (homOfLE h) := ⟨⟨homOfLE h', Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
  infer_instance

/-- Pushforward along an isomorphism preserves quasi-coherence. -/
lemma isQuasicoherent_pushforward_of_isIso (e : X ⟶ Y) [IsIso e] (G : X.Modules)
    [G.IsQuasicoherent] : ((Scheme.Modules.pushforward e).obj G).IsQuasicoherent := by
  let u := (Scheme.Modules.restrictAdjunction e).unit.app (G.restrict (inv e))
  have hu : IsIso u := by
    rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
    intro T
    simp only [u, Scheme.Modules.restrictAdjunction_unit_app_app]
    refine isIso_presheaf_map_homOfLE _ _ ?_
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Hom.opensRange_of_isIso]
    simp
  let e₂ : (G.restrict (inv e)).restrict e ≅ G :=
    ((Scheme.Modules.restrictFunctorComp e (inv e)).app G).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr (IsIso.hom_inv_id e)).app G ≪≫
        Scheme.Modules.restrictFunctorId.app G
  exact isQuasicoherent_of_iso (asIso u ≪≫ (Scheme.Modules.pushforward e).mapIso e₂)
    (inferInstanceAs ((G.restrict (inv e)).IsQuasicoherent))

/-- Pushforward along `Spec.map φ` preserves quasi-coherence (Hartshorne II.5.2(d)). -/
lemma isQuasicoherent_pushforward_specMap {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (G : (Spec S).Modules) [G.IsQuasicoherent] :
    ((Scheme.Modules.pushforward (Spec.map φ)).obj G).IsQuasicoherent := by
  have : IsIso G.fromTildeΓ := (isQuasicoherent_iff_isIso_fromTildeΓ G).mp ‹_›
  exact isQuasicoherent_of_iso (((tildePushforwardIso φ).app _).symm ≪≫
    (Scheme.Modules.pushforward (Spec.map φ)).mapIso (@asIso _ _ _ _ G.fromTildeΓ this))
    (inferInstanceAs ((tilde.functor R).obj _).IsQuasicoherent)

/-- Pushforward along a morphism of affine schemes preserves quasi-coherence. -/
lemma isQuasicoherent_pushforward_of_isAffine [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    (G : X.Modules) [G.IsQuasicoherent] :
    ((Scheme.Modules.pushforward f).obj G).IsQuasicoherent := by
  have hf : f = X.isoSpec.hom ≫ Spec.map f.appTop ≫ Y.isoSpec.inv := by
    rw [Scheme.isoSpec_inv_naturality, Iso.hom_inv_id_assoc]
  have h₁ : ((Scheme.Modules.pushforward X.isoSpec.hom).obj G).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_isIso _ G
  have h₂ : ((Scheme.Modules.pushforward (Spec.map f.appTop)).obj
      ((Scheme.Modules.pushforward X.isoSpec.hom).obj G)).IsQuasicoherent :=
    isQuasicoherent_pushforward_specMap _ _
  have h₃ := isQuasicoherent_pushforward_of_isIso Y.isoSpec.inv
    ((Scheme.Modules.pushforward (Spec.map f.appTop)).obj
      ((Scheme.Modules.pushforward X.isoSpec.hom).obj G))
  rw [hf]
  exact isQuasicoherent_of_iso
    ((Scheme.Modules.pushforwardComp (Spec.map f.appTop) Y.isoSpec.inv).app
        ((Scheme.Modules.pushforward X.isoSpec.hom).obj G) ≪≫
      (Scheme.Modules.pushforwardComp X.isoSpec.hom (Spec.map f.appTop ≫ Y.isoSpec.inv)).app G)
    h₃

/-! ### Mayer-Vietoris squares -/

/-- A square of restriction maps of a sheaf of abelian groups along opens `b, c ≤ a` with
`a = b ⊔ c` and `d = b ⊓ c` is a pullback. -/
lemma isPullback_sheaf_map {T : TopCat.{u}} (P : TopCat.Presheaf Ab.{u} T) (hP : P.IsSheaf)
    {a b c d : Opens T}
    (p₁ : op a ⟶ op b) (p₂ : op a ⟶ op c) (p₃ : op b ⟶ op d) (p₄ : op c ⟶ op d)
    (ha : a = b ⊔ c) (hd : d = b ⊓ c) :
    IsPullback (P.map p₁) (P.map p₂) (P.map p₃) (P.map p₄) := by
  let F : TopCat.Sheaf Ab.{u} T := ⟨P, hP⟩
  subst ha hd
  obtain rfl : p₁ = (homOfLE le_sup_left).op := Subsingleton.elim _ _
  obtain rfl : p₂ = (homOfLE le_sup_right).op := Subsingleton.elim _ _
  obtain rfl : p₃ = (homOfLE inf_le_left).op := Subsingleton.elim _ _
  obtain rfl : p₄ = (homOfLE inf_le_right).op := Subsingleton.elim _ _
  exact IsPullback.of_isLimit (TopCat.Sheaf.isLimitPullbackCone F b c)

/-- A commutative square of `𝒪_X`-modules is a pullback if it is one on sections over every
open. -/
lemma isPullback_of_app {W A B Z : X.Modules} {h : W ⟶ A} {k : W ⟶ B} {f : A ⟶ Z} {g : B ⟶ Z}
    (comm : h ≫ f = k ≫ g)
    (H : ∀ T : X.Opens, IsPullback (h.app T) (k.app T) (f.app T) (g.app T)) :
    IsPullback h k f g := by
  refine IsPullback.of_isLimit' ⟨comm⟩ ?_
  apply isLimitOfIsLimitPullbackConeMap (Scheme.Modules.toPresheaf X)
  apply evaluationJointlyReflectsLimits
  intro T
  exact (isLimitMapConePullbackConeEquiv _ _).symm (H T.unop).isLimit

/-- `j_* j⁻¹ M` for the inclusion `j` of an open `U`. -/
abbrev rp (U : X.Opens) : X.Modules ⥤ X.Modules :=
  Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pushforward U.ι

/-- The unit `M ⟶ j_* j⁻¹ M`. -/
abbrev η (U : X.Opens) : 𝟭 X.Modules ⟶ rp U := (Scheme.Modules.restrictAdjunction U.ι).unit

lemma ι_image_preimage (U T : X.Opens) : U.ι ''ᵁ U.ι ⁻¹ᵁ T = U ⊓ T := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]

lemma ι_image_preimage_mono (U : X.Opens) {A B : X.Opens} (h : A ≤ B) :
    U.ι ''ᵁ U.ι ⁻¹ᵁ A ≤ U.ι ''ᵁ U.ι ⁻¹ᵁ B := by
  rw [ι_image_preimage, ι_image_preimage]
  exact inf_le_inf_left _ h

lemma η_app_app (U : X.Opens) (M : X.Modules) (T : X.Opens) :
    ((η U).app M).app T = M.presheaf.map (homOfLE (U.ι.image_preimage_le T)).op :=
  rfl

lemma rp_map_app (U : X.Opens) {M N : X.Modules} (φ : M ⟶ N) (T : X.Opens) :
    ((rp U).map φ).app T = φ.app (U.ι ''ᵁ U.ι ⁻¹ᵁ T) :=
  rfl

lemma rp_obj_presheaf_map (U : X.Opens) (M : X.Modules) {A B : X.Opens} (i : A ⟶ B) :
    ((rp U).obj M).presheaf.map i.op =
      M.presheaf.map (homOfLE (ι_image_preimage_mono U (leOfHom i))).op := by
  change M.presheaf.map (U.ι.opensFunctor.map ((Opens.map U.ι.base).map i)).op = _
  exact congrArg (fun j => M.presheaf.map (Quiver.Hom.op j)) (Subsingleton.elim _ _)

set_option linter.unusedSimpArgs false in
/-- **Mayer-Vietoris.** For opens `S, U` and `H = j_* j⁻¹ G` along `S ⊔ U`, the square
`H → j_* j⁻¹ H` (along `S` and `U`) into `j_* j⁻¹ j_* j⁻¹ H` is a pullback. -/
theorem isPullback_rp (S U : X.Opens) (G : X.Modules) :
    IsPullback ((η S).app ((rp (S ⊔ U)).obj G)) ((η U).app ((rp (S ⊔ U)).obj G))
      ((η U).app ((rp S).obj ((rp (S ⊔ U)).obj G)))
      ((rp U).map ((η S).app ((rp (S ⊔ U)).obj G))) := by
  refine isPullback_of_app ?_ ?_
  · exact (η U).naturality ((η S).app ((rp (S ⊔ U)).obj G))
  intro T
  have ha : (S ⊔ U).ι ''ᵁ (S ⊔ U).ι ⁻¹ᵁ T =
      (S ⊔ U).ι ''ᵁ (S ⊔ U).ι ⁻¹ᵁ (S.ι ''ᵁ S.ι ⁻¹ᵁ T) ⊔
        (S ⊔ U).ι ''ᵁ (S ⊔ U).ι ⁻¹ᵁ (U.ι ''ᵁ U.ι ⁻¹ᵁ T) := by
    simp only [ι_image_preimage]
    rw [inf_eq_right.mpr (inf_le_left.trans le_sup_left),
      inf_eq_right.mpr (inf_le_left.trans le_sup_right), inf_sup_right]
  have hd : (S ⊔ U).ι ''ᵁ (S ⊔ U).ι ⁻¹ᵁ (S.ι ''ᵁ S.ι ⁻¹ᵁ (U.ι ''ᵁ U.ι ⁻¹ᵁ T)) =
      (S ⊔ U).ι ''ᵁ (S ⊔ U).ι ⁻¹ᵁ (S.ι ''ᵁ S.ι ⁻¹ᵁ T) ⊓
        (S ⊔ U).ι ''ᵁ (S ⊔ U).ι ⁻¹ᵁ (U.ι ''ᵁ U.ι ⁻¹ᵁ T) := by
    simp only [ι_image_preimage]
    rw [inf_eq_right.mpr (inf_le_left.trans le_sup_left : S ⊓ (U ⊓ T) ≤ S ⊔ U),
      inf_eq_right.mpr (inf_le_left.trans le_sup_left : S ⊓ T ≤ S ⊔ U),
      inf_eq_right.mpr (inf_le_left.trans le_sup_right : U ⊓ T ≤ S ⊔ U),
      inf_inf_inf_comm, inf_idem, inf_assoc]
  have h₁ : (S ⊔ U).ι ''ᵁ (S ⊔ U).ι ⁻¹ᵁ (S.ι ''ᵁ S.ι ⁻¹ᵁ T) ≤
      (S ⊔ U).ι ''ᵁ (S ⊔ U).ι ⁻¹ᵁ T := ha ▸ le_sup_left
  have h₂ : (S ⊔ U).ι ''ᵁ (S ⊔ U).ι ⁻¹ᵁ (U.ι ''ᵁ U.ι ⁻¹ᵁ T) ≤
      (S ⊔ U).ι ''ᵁ (S ⊔ U).ι ⁻¹ᵁ T := ha ▸ le_sup_right
  have h₃ : (S ⊔ U).ι ''ᵁ (S ⊔ U).ι ⁻¹ᵁ (S.ι ''ᵁ S.ι ⁻¹ᵁ (U.ι ''ᵁ U.ι ⁻¹ᵁ T)) ≤
      (S ⊔ U).ι ''ᵁ (S ⊔ U).ι ⁻¹ᵁ (S.ι ''ᵁ S.ι ⁻¹ᵁ T) := hd ▸ inf_le_left
  have h₄ : (S ⊔ U).ι ''ᵁ (S ⊔ U).ι ⁻¹ᵁ (S.ι ''ᵁ S.ι ⁻¹ᵁ (U.ι ''ᵁ U.ι ⁻¹ᵁ T)) ≤
      (S ⊔ U).ι ''ᵁ (S ⊔ U).ι ⁻¹ᵁ (U.ι ''ᵁ U.ι ⁻¹ᵁ T) := hd ▸ inf_le_right
  have key := isPullback_sheaf_map G.presheaf G.isSheaf
    (homOfLE h₁).op (homOfLE h₂).op (homOfLE h₃).op (homOfLE h₄).op ha hd
  refine key.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;>
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      rfl

end

end QcqsPushforward

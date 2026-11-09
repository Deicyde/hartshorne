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

/-! ### Composites of `j_* j⁻¹` -/

lemma isIso_η_app_app_of_le (U : X.Opens) (M : X.Modules) {T : X.Opens} (hT : T ≤ U) :
    IsIso (((η U).app M).app T) := by
  rw [η_app_app]
  refine isIso_presheaf_map_homOfLE _ _ ?_
  rw [ι_image_preimage]
  exact le_inf hT le_rfl

lemma isIso_η_app_rp (U V : X.Opens) (hVU : V ≤ U) (G : X.Modules) :
    IsIso ((η U).app ((rp V).obj G)) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro T
  rw [η_app_app, rp_obj_presheaf_map]
  refine isIso_presheaf_map_homOfLE _ _ ?_
  simp only [ι_image_preimage]
  exact le_inf inf_le_left (le_inf (inf_le_left.trans hVU) inf_le_right)

lemma isIso_rp_map_rp_map_η (A B : X.Opens) (G : X.Modules) :
    IsIso ((rp A).map ((rp B).map ((η (A ⊓ B)).app G))) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro T
  rw [rp_map_app, rp_map_app]
  refine isIso_η_app_app_of_le _ _ ?_
  simp only [ι_image_preimage]
  exact le_inf (inf_le_right.trans inf_le_left) inf_le_left

/-- `j_* j⁻¹` along `A` after `j_* j⁻¹` along `B` is `j_* j⁻¹` along `A ⊓ B`. -/
def rpCompIso (A B : X.Opens) (G : X.Modules) :
    (rp A).obj ((rp B).obj G) ≅ (rp (A ⊓ B)).obj G :=
  haveI := isIso_rp_map_rp_map_η A B G
  haveI := isIso_η_app_rp B (A ⊓ B) inf_le_right G
  haveI := isIso_η_app_rp A (A ⊓ B) inf_le_left G
  asIso ((rp A).map ((rp B).map ((η (A ⊓ B)).app G))) ≪≫
    (rp A).mapIso (asIso ((η B).app ((rp (A ⊓ B)).obj G))).symm ≪≫
      (asIso ((η A).app ((rp (A ⊓ B)).obj G))).symm

/-- `j_* j⁻¹` along `⊤` is the identity. -/
def rpTopIso (G : X.Modules) : G ≅ (rp ⊤).obj G :=
  haveI : IsIso ((η (⊤ : X.Opens)).app G) := by
    rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
    exact fun T => isIso_η_app_app_of_le _ _ le_top
  asIso ((η ⊤).app G)

lemma isZero_rp_bot (G : X.Modules) : IsZero ((rp (⊥ : X.Opens)).obj G) := by
  rw [IsZero.iff_id_eq_zero]
  ext T : 1
  have hT : (⊥ : X.Opens).ι ''ᵁ (⊥ : X.Opens).ι ⁻¹ᵁ T = ⊥ := by
    rw [ι_image_preimage, bot_inf_eq]
  exact (TopCat.Sheaf.isTerminalOfEqEmpty ⟨G.presheaf, G.isSheaf⟩ hT).hom_ext _ _

/-! ### Quasi-coherence of a pullback -/

lemma isQuasicoherent_of_isPullback {P A B Z : Y.Modules} {fst : P ⟶ A} {snd : P ⟶ B}
    {f : A ⟶ Z} {g : B ⟶ Z} (h : IsPullback fst snd f g) (hA : A.IsQuasicoherent)
    (hB : B.IsQuasicoherent) (hZ : Z.IsQuasicoherent) : P.IsQuasicoherent := by
  have := (SheafOfModules.isQuasicoherent Y.ringCatSheaf).isClosedUnderLimitsOfShape_of_preservesLimitsOfShape_ι
    WalkingCospan
  refine (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_isLimit h.isLimit ?_
  rintro (_ | _ | _)
  · exact hZ
  · exact hA
  · exact hB

/-! ### The affine-target case -/

/-- `PushQC f S`: for every quasi-coherent `G`, the pushforward along `f` of `j_* j⁻¹ G`
(along the inclusion of `S`) is quasi-coherent. -/
def PushQC (f : X ⟶ Y) (S : X.Opens) : Prop :=
  ∀ G : X.Modules, G.IsQuasicoherent →
    ((Scheme.Modules.pushforward f).obj ((rp S).obj G)).IsQuasicoherent

lemma pushQC_of_isAffineOpen [IsAffine Y] (f : X ⟶ Y) {U : X.Opens} (hU : IsAffineOpen U) :
    PushQC f U := by
  intro G hG
  have : IsAffine U := hU
  exact isQuasicoherent_of_iso ((Scheme.Modules.pushforwardComp U.ι f).app _).symm
    (isQuasicoherent_pushforward_of_isAffine (U.ι ≫ f) (G.restrict U.ι))

lemma pushQC_bot (f : X ⟶ Y) : PushQC f ⊥ := fun G _ =>
  isQuasicoherent_of_isZero ((Scheme.Modules.pushforward f).map_isZero (isZero_rp_bot G))

lemma pushQC_congr (f : X ⟶ Y) {S S' : X.Opens} (h : S = S') (hS : PushQC f S) : PushQC f S' :=
  h ▸ hS

lemma pushQC_sup (f : X ⟶ Y) (S U : X.Opens) (hS : PushQC f S) (hU : PushQC f U)
    (hSU : PushQC f (S ⊓ U)) : PushQC f (S ⊔ U) := by
  intro G hG
  have sq := (isPullback_rp S U G).map (Scheme.Modules.pushforward f)
  refine isQuasicoherent_of_isPullback sq ?_ ?_ ?_
  · exact isQuasicoherent_of_iso ((Scheme.Modules.pushforward f).mapIso (rpCompIso _ _ G)).symm
      (pushQC_congr f inf_sup_self.symm hS G hG)
  · exact isQuasicoherent_of_iso ((Scheme.Modules.pushforward f).mapIso (rpCompIso _ _ G)).symm
      (pushQC_congr f (inf_eq_left.mpr le_sup_right).symm hU G hG)
  · refine isQuasicoherent_of_iso ((Scheme.Modules.pushforward f).mapIso
      ((rp U).mapIso (rpCompIso _ _ G) ≪≫ rpCompIso _ _ G)).symm ?_
    refine pushQC_congr f ?_ hSU G hG
    rw [inf_sup_self, inf_comm]

lemma pushQC_iSup_basicOpen [IsAffine Y] (f : X ⟶ Y) {U₀ : X.Opens} (hU₀ : IsAffineOpen U₀)
    {ι : Type*} (t : Finset ι) (g : ι → Γ(X, U₀)) :
    ∀ h : Γ(X, U₀), PushQC f (⨆ i ∈ t, X.basicOpen (g i * h)) := by
  classical
  induction t using Finset.induction_on with
  | empty => intro h; simpa using pushQC_bot f
  | insert i t hit ih =>
    intro h
    rw [Finset.iSup_insert]
    refine pushQC_sup f _ _ (pushQC_of_isAffineOpen f (hU₀.basicOpen _)) (ih h) ?_
    refine pushQC_congr f ?_ (ih (g i * h))
    rw [inf_iSup₂_eq]
    refine iSup_congr fun j => iSup_congr fun _ => ?_
    simp only [Scheme.basicOpen_mul]
    rw [inf_inf_inf_comm, inf_idem]
    ac_rfl

/-- A compact open contained in an affine open satisfies `PushQC`. -/
lemma pushQC_of_isCompact_le [IsAffine Y] (f : X ⟶ Y) {U₀ : X.Opens} (hU₀ : IsAffineOpen U₀)
    {W : X.Opens} (hW : IsCompact (W : Set X)) (hWU : W ≤ U₀) : PushQC f W := by
  classical
  have key : ∀ x : W, ∃ g : Γ(X, U₀), X.basicOpen g ≤ W ∧ (x : X) ∈ X.basicOpen g :=
    fun x => hU₀.exists_basicOpen_le x (hWU x.2)
  choose g hg hxg using key
  obtain ⟨t, ht⟩ := hW.elim_finite_subcover (fun x : W => (X.basicOpen (g x) : Set X))
    (fun x => (X.basicOpen (g x)).isOpen) (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxg _⟩)
  have hWt : W = ⨆ x ∈ t, X.basicOpen (g x * 1) := by
    apply le_antisymm
    · intro y hy
      have := ht hy
      simp only [Set.mem_iUnion] at this
      obtain ⟨i, hi, hyi⟩ := this
      simp only [mul_one, Opens.mem_iSup]
      exact ⟨i, hi, hyi⟩
    · exact iSup₂_le fun x _ => by rw [mul_one]; exact hg x
  rw [hWt]
  exact pushQC_iSup_basicOpen f hU₀ t g 1

/-- On a quasi-separated scheme, every compact open satisfies `PushQC`. -/
lemma pushQC_of_isCompact [IsAffine Y] [QuasiSeparatedSpace X] (f : X ⟶ Y) {S : X.Opens}
    (hS : IsCompact (S : Set X)) : PushQC f S := by
  refine compact_open_induction_on (P := PushQC f) S hS (pushQC_bot f) ?_
  intro S hS U hP
  exact pushQC_sup f S U hP (pushQC_of_isAffineOpen f U.2)
    (pushQC_of_isCompact_le f U.2 (hS.inter_of_isOpen U.2.isCompact S.2 U.1.2) inf_le_right)

/-- **Affine target.** If `X` is quasi-compact and quasi-separated and `Y` is affine, then the
pushforward of a quasi-coherent `𝒪_X`-module along any `f : X ⟶ Y` is quasi-coherent. -/
theorem isQuasicoherent_pushforward_of_isAffine_target [IsAffine Y] [CompactSpace X]
    [QuasiSeparatedSpace X] (f : X ⟶ Y) (G : X.Modules) [G.IsQuasicoherent] :
    ((Scheme.Modules.pushforward f).obj G).IsQuasicoherent :=
  isQuasicoherent_of_iso ((Scheme.Modules.pushforward f).mapIso (rpTopIso G).symm)
    (pushQC_of_isCompact f (by simpa using isCompact_univ) G ‹_›)

end

end QcqsPushforward

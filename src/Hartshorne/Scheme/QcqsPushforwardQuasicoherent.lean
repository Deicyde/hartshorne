/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.QuasicoherentAbelianClosure
import Hartshorne.Scheme.AffineTildeChangeOfRings

/-!
# Pushforward of quasi-coherent sheaves along quasi-compact quasi-separated morphisms

Hartshorne, *Algebraic Geometry*, II, Proposition 5.8(c) (p. 115): if `X` is Noetherian, or `f`
is quasi-compact and separated, then `f_*` of a quasi-coherent sheaf is quasi-coherent
(`Hartshorne.isQuasicoherent_pushforward`). We prove it for every quasi-compact quasi-separated
`f` (`Hartshorne.isQuasicoherent_pushforward_of_qcqs`).

## Proof

Quasi-coherence is local on `Y`, and the restriction of `f_* F` to an open `V ⊆ Y` is the
pushforward along `f⁻¹ V ⟶ V` of `F|_{f⁻¹ V}` (`pushforwardRestrictIso`), so we may assume `Y`
affine, `X` quasi-compact and quasi-separated. For an open `S ⊆ X` write `R_S = j_* j⁻¹`
(`rp S`). Pushforward along a morphism of affine schemes preserves quasi-coherence
(Proposition II.5.2(d), `tildePushforwardIso`), which gives `f_* R_U F` for affine `U`. For
opens `S, U` the square `R_{S ⊔ U} F → R_S, R_U → R_U R_S` is a pullback (the sheaf condition
for the cover `{S, U}`, `isPullback_rp`), and `R_A R_B ≅ R_{A ⊓ B}` (`rpCompIso`); since `f_*`
preserves pullbacks and quasi-coherent modules are closed under finite limits (a consequence of
Proposition 5.7),
`f_* R_S F` quasi-coherent for `S`, `U` and `S ⊓ U` gives it for `S ⊔ U`. Induction over finite
unions of basic opens handles compact opens inside an affine open, and induction over finite
unions of affine opens (intersections being compact, as `X` is quasi-separated) handles every
compact open, in particular `X` itself (`R_X F ≅ F`). This is the finite-cover kernel argument of
the book, organized two opens at a time.
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
    · simp only [Iso.refl_hom]
      exact (Category.id_comp _).symm

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
  have := (SheafOfModules.isQuasicoherent
    Y.ringCatSheaf).isClosedUnderLimitsOfShape_of_preservesLimitsOfShape_ι WalkingCospan
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

/-! ### Restricting the target -/

/-- **Restricting a pushforward to an open of the target.** For `f : X ⟶ Y`, an open `V` of `Y`
and an `𝒪_X`-module `F`, the restriction of `f_* F` to `V` is the pushforward along
`f ∣_ V : f⁻¹ V ⟶ V` of the restriction of `F` to `f⁻¹ V`. -/
def pushforwardRestrictIso (f : X ⟶ Y) (V : Y.Opens) (F : X.Modules) :
    ((Scheme.Modules.pushforward f).obj F).restrict V.ι ≅
      (Scheme.Modules.pushforward (f ∣_ V)).obj (F.restrict (f ⁻¹ᵁ V).ι) :=
  let e : (Scheme.Modules.pushforward f).obj ((rp (f ⁻¹ᵁ V)).obj F) ≅
      (Scheme.Modules.pushforward V.ι).obj
        ((Scheme.Modules.pushforward (f ∣_ V)).obj (F.restrict (f ⁻¹ᵁ V).ι)) :=
    (Scheme.Modules.pushforwardComp (f ⁻¹ᵁ V).ι f).app _ ≪≫
      (Scheme.Modules.pushforwardCongr (morphismRestrict_ι f V).symm).app _ ≪≫
      ((Scheme.Modules.pushforwardComp (f ∣_ V) V.ι).app _).symm
  let φ := (Scheme.Modules.pushforward f).map ((η (f ⁻¹ᵁ V)).app F) ≫ e.hom
  let ψ := ((Scheme.Modules.restrictAdjunction V.ι).homEquiv _ _).symm φ
  haveI : IsIso ψ := by
    rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
    intro W
    simp only [ψ, Adjunction.homEquiv_counit, Scheme.Modules.Hom.comp_app]
    have h1 : IsIso (((Scheme.Modules.restrictFunctor V.ι).map φ).app W) := by
      change IsIso (φ.app (V.ι ''ᵁ W))
      simp only [φ, Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app]
      have := isIso_η_app_app_of_le (f ⁻¹ᵁ V) F
        (T := f ⁻¹ᵁ (V.ι ''ᵁ W)) (f.preimage_mono (Scheme.Opens.ι_image_le V W))
      have h2 : IsIso (e.hom.app (V.ι ''ᵁ W)) := inferInstance
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ this h2
    infer_instance
  asIso ψ

end

end QcqsPushforward

open QcqsPushforward

variable {X Y : Scheme.{u}}

/-- **Pushforward along a quasi-compact quasi-separated morphism.** If `f : X ⟶ Y` is
quasi-compact and quasi-separated, then `f_*` sends quasi-coherent `𝒪_X`-modules to
quasi-coherent `𝒪_Y`-modules. This supplements Hartshorne II, Proposition 5.8(c), whose two
hypotheses (`X` Noetherian; `f` quasi-compact and separated) both imply it. -/
theorem isQuasicoherent_pushforward_of_qcqs (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (G : X.Modules) [G.IsQuasicoherent] :
    ((Scheme.Modules.pushforward f).obj G).IsQuasicoherent := by
  have htfae := (quasicoherent_affine_local_tfae ((Scheme.Modules.pushforward f).obj G)).out 1 0
  refine htfae.mp ⟨Y.affineOpens, id, iSup_affineOpens_eq_top Y, fun V => ?_⟩
  have : IsAffine V := V.2
  have : CompactSpace (f ⁻¹ᵁ (V : Y.Opens)) :=
    isCompact_iff_compactSpace.mp
      (QuasiCompact.isCompact_preimage (f := f) _ (V : Y.Opens).2 V.2.isCompact)
  have hVqs : IsQuasiSeparated ((V : Y.Opens) : Set Y) :=
    (isQuasiSeparated_iff_quasiSeparatedSpace _ (V : Y.Opens).2).mpr
      (quasiSeparatedSpace_of_isAffine V)
  have : QuasiSeparatedSpace (f ⁻¹ᵁ (V : Y.Opens)) :=
    (isQuasiSeparated_iff_quasiSeparatedSpace _ (f ⁻¹ᵁ (V : Y.Opens)).2).mp
      (f.isQuasiSeparated_preimage hVqs)
  have h₁ : (((Scheme.Modules.pushforward f).obj G).restrict (V : Y.Opens).ι).IsQuasicoherent :=
    isQuasicoherent_of_iso (pushforwardRestrictIso f V G).symm
      (isQuasicoherent_pushforward_of_isAffine_target _ _)
  let _ : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
  have h₂ : (((Scheme.Modules.pushforward f).obj G).restrict V.2.fromSpec).IsQuasicoherent :=
    isQuasicoherent_of_iso
      (((Scheme.Modules.restrictFunctorComp V.2.isoSpec.inv (V : Y.Opens).ι).app
          ((Scheme.Modules.pushforward f).obj G)).symm ≪≫
        (Scheme.Modules.restrictFunctorCongr V.2.isoSpec_inv_ι).app
          ((Scheme.Modules.pushforward f).obj G))
      (Scheme.Modules.isQuasicoherent_restrictFunctor V.2.isoSpec.inv
        (((Scheme.Modules.pushforward f).obj G).restrict (V : Y.Opens).ι))
  have h₃ : IsIso (((Scheme.Modules.pushforward f).obj G).restrict V.2.fromSpec).fromTildeΓ :=
    (isQuasicoherent_iff_isIso_fromTildeΓ _).mp h₂
  exact isIso_fromTildeΓ_iff.mp h₃

/-- **Hartshorne II, Proposition 5.8(c).** Let `f : X ⟶ Y` be a morphism of schemes, and assume
that `X` is Noetherian, or that `f` is quasi-compact and separated. Then `f_*` sends
quasi-coherent `𝒪_X`-modules to quasi-coherent `𝒪_Y`-modules. -/
theorem isQuasicoherent_pushforward (f : X ⟶ Y)
    (hf : IsNoetherian X ∨ (QuasiCompact f ∧ IsSeparated f))
    (G : X.Modules) [G.IsQuasicoherent] :
    ((Scheme.Modules.pushforward f).obj G).IsQuasicoherent := by
  rcases hf with hX | ⟨hqc, hsep⟩
  · have : QuasiSeparated f := QuasiSeparated.of_quasiSeparatedSpace f
    exact isQuasicoherent_pushforward_of_qcqs f G
  · exact isQuasicoherent_pushforward_of_qcqs f G

end Hartshorne

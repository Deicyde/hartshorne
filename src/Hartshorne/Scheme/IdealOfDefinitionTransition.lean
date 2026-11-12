/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.CoherentFormalModuleReduction
import Hartshorne.Scheme.QcqsPushforwardQuasicoherent
import Hartshorne.Scheme.SheafCechOneLift

/-!
# Transition maps between the thickenings of a Noetherian formal scheme

Let `X` be a Noetherian formal scheme with ideal of definition `J`, and write
`Xₙ = (X, 𝒪_X / J ^ (n + 1))`.

* `Hartshorne.IdealSubsheaf.quotientMap`: for ideal subsheaves `K ≤ J`, the map
  `R / K ⟶ R / J` of quotient sheaves of rings, compatible with the projections
  (`IdealSubsheaf.quotientπ_quotientMap`).
* `Hartshorne.IsIdealOfDefinition.quotientSchemeMap`: for ideals of definition `K ≤ J`, the morphism
  of schemes `(X, 𝒪_X / J) ⟶ (X, 𝒪_X / K)`, the identity on spaces.
* `Hartshorne.IsIdealOfDefinition.surjective_powQuotientMap`: for a coherent `𝒪_X`-module `F` with
  `X_(n+1)` affine, the transition map `Γ(X, F / J ^ (n + 2) F) ⟶ Γ(X, F / J ^ (n + 1) F)` is
  surjective. On `X_(n+1)`, `F / J ^ (n + 1) F` is the pushforward of the coherent `𝒪_{Xₙ}`-module
  `Fₙ` along `Xₙ ⟶ X_(n+1)`, hence quasi-coherent (Proposition 5.8(c)); the kernel of
  `F_(n+1) ⟶ F / J ^ (n + 1) F` is then quasi-coherent, and Proposition 5.6 on `X_(n+1)` gives the
  surjectivity.
-/

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry

namespace Hartshorne

universe u

namespace IdealSubsheaf

variable {T : TopCat.{u}} {R : TopCat.Sheaf CommRingCat.{u} T} {J K : IdealSubsheaf R}

/-- For `K ≤ J`, the map of presheaves `R(V) ⧸ K(V) → R(V) ⧸ J(V)`. -/
def quotientPresheafMap (hKJ : K ≤ J) :
    idealQuotientPresheaf R K.ideal K.ideal_le_comap ⟶
      idealQuotientPresheaf R J.ideal J.ideal_le_comap where
  app V := CommRingCat.ofHom (Ideal.Quotient.factor (le_iff.mp hKJ V.unop))
  naturality V W i := by
    ext x
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl

/-- For ideal subsheaves `K ≤ J`, the map `R / K ⟶ R / J` of quotient sheaves of rings. -/
def quotientMap (hKJ : K ≤ J) : K.quotient ⟶ J.quotient :=
  (presheafToSheaf (Opens.grothendieckTopology T) CommRingCat.{u}).map (quotientPresheafMap hKJ)

@[reassoc (attr := simp)]
lemma quotientπ_quotientMap (hKJ : K ≤ J) : K.quotientπ ≫ quotientMap hKJ = J.quotientπ := by
  have : K.quotientPresheafπ ≫ quotientPresheafMap hKJ = J.quotientPresheafπ := by
    ext V s
    rfl
  exact (Category.assoc _ _ _).trans (congrArg ((sheafificationIso R).hom ≫ ·)
    ((Functor.map_comp _ _ _).symm.trans (congrArg _ this)))

lemma quotientπ_quotientMap_app (hKJ : K ≤ J) (V : Opens T) (s : R.presheaf.obj (op V)) :
    (quotientMap hKJ).hom.app (op V) (K.quotientπ.hom.app (op V) s) =
      J.quotientπ.hom.app (op V) s := by
  rw [← quotientπ_quotientMap hKJ]
  rfl

end IdealSubsheaf

namespace IsIdealOfDefinition

section SchemeMap

variable {X : NoetherianFormalScheme.{u}} {J K : IdealSubsheaf X.toLocallyRingedSpace.sheaf}
  (hJ : IsIdealOfDefinition X J) (hK : IsIdealOfDefinition X K) (hKJ : K ≤ J)

/-- For ideals of definition `K ≤ J`, the morphism of ringed spaces `(X, 𝒪_X / J) ⟶ (X, 𝒪_X / K)`:
the identity on spaces and `𝒪_X / K ⟶ 𝒪_X / J` on sheaves. -/
def quotientSchemePresheafedSpaceMap :
    hJ.quotientScheme.toPresheafedSpace ⟶ hK.quotientScheme.toPresheafedSpace where
  base := 𝟙 X.toLocallyRingedSpace.toTopCat
  c := (IdealSubsheaf.quotientMap hKJ).hom

/-- The stalk maps of `(X, 𝒪_X / J) ⟶ (X, 𝒪_X / K)` are surjective. -/
lemma surjective_stalkMap_quotientSchemePresheafedSpaceMap (x : X.toLocallyRingedSpace) :
    Function.Surjective ((quotientSchemePresheafedSpaceMap hJ hK hKJ).stalkMap x) := by
  intro b
  obtain ⟨V, hxV, t, rfl⟩ := J.quotient.presheaf.exists_germ_eq b
  obtain ⟨V', hV'V, ⟨s, hs⟩, hxV'⟩ := (TopCat.Presheaf.isLocallySurjective_iff _).mp
    J.isLocallySurjective_quotientπ V t x hxV
  refine ⟨K.quotient.presheaf.germ V' x hxV' (K.quotientπ.hom.app (op V') s), ?_⟩
  refine (PresheafedSpace.stalkMap_germ_apply (quotientSchemePresheafedSpaceMap hJ hK hKJ) V' x
    hxV' _).trans ?_
  refine (congrArg (J.quotient.presheaf.germ V' x hxV')
    (IdealSubsheaf.quotientπ_quotientMap_app hKJ V' s)).trans ?_
  exact (congrArg (J.quotient.presheaf.germ V' x hxV') hs).trans
    (J.quotient.presheaf.germ_res_apply (homOfLE hV'V) x hxV' t)

/-- **The morphism between thickenings.** For ideals of definition `K ≤ J`, the morphism of
schemes `(X, 𝒪_X / J) ⟶ (X, 𝒪_X / K)`, the identity on spaces and the projection
`𝒪_X / K ⟶ 𝒪_X / J` on structure sheaves. -/
def quotientSchemeMap : hJ.quotientScheme ⟶ hK.quotientScheme :=
  ⟨⟨quotientSchemePresheafedSpaceMap hJ hK hKJ, fun x =>
    IsLocalHom.of_surjective _ (surjective_stalkMap_quotientSchemePresheafedSpaceMap hJ hK hKJ x)⟩⟩

/-- Pushing a module on `(X, 𝒪_X / J)` forward to `(X, 𝒪_X / K)` and then to `X` is pushing it
forward to `X`: both have the same sections, and `𝒪_X` acts through
`𝒪_X ⟶ 𝒪_X / K ⟶ 𝒪_X / J`. -/
def quotientPushforwardSchemeMapIso (G : hJ.quotientScheme.Modules) :
    hK.quotientPushforward.obj ((Scheme.Modules.pushforward (quotientSchemeMap hJ hK hKJ)).obj G) ≅
      hJ.quotientPushforward.obj G where
  hom := ⟨PresheafOfModules.homMk (𝟙 G.val.presheaf) (fun V r m =>
    congrArg (fun a => (show hJ.quotientScheme.ringCatSheaf.obj.obj V from a) •
      (show G.val.obj V from m)) (IdealSubsheaf.quotientπ_quotientMap_app hKJ V.unop r))⟩
  inv := ⟨PresheafOfModules.homMk (𝟙 G.val.presheaf) (fun V r m =>
    (congrArg (fun a => (show hJ.quotientScheme.ringCatSheaf.obj.obj V from a) •
      (show G.val.obj V from m)) (IdealSubsheaf.quotientπ_quotientMap_app hKJ V.unop r)).symm)⟩
  hom_inv_id := rfl
  inv_hom_id := rfl

end SchemeMap

section Reduction

variable {X : NoetherianFormalScheme.{u}} {J : IdealSubsheaf X.toLocallyRingedSpace.sheaf}
  (h : IsIdealOfDefinition X J)
  (F : SheafOfModules.{u} (structureRingCatSheaf X.toLocallyRingedSpace))

omit h in
/-- `F / J ^ (n + 1) F` is killed by `J ^ (n + 2)`. -/
lemma annihilates_powQuotient_succ (n : ℕ) : (J ^ (n + 1 + 1)).Annihilates (J.powQuotient F n) := by
  intro V
  have h1 := IdealSubsheaf.annihilates_cokernel_smulι (J ^ (n + 1)) F V
  refine eq_bot_iff.mpr ((Submodule.smul_mono_left ?_).trans h1.le)
  exact IdealSubsheaf.le_iff.mp (J.pow_le_pow_right (Nat.le_succ (n + 1))) V

/-- **Surjectivity of the reduction transition maps.** Let `F` be a coherent module on a Noetherian
formal scheme with ideal of definition `J`, and suppose `X_(n+1) = (X, 𝒪_X / J ^ (n + 2))` is
affine. Then `Γ(X, F / J ^ (n + 2) F) ⟶ Γ(X, F / J ^ (n + 1) F)` is surjective. On `X_(n+1)`, the
module `F / J ^ (n + 1) F` is the pushforward of the coherent `𝒪_{Xₙ}`-module `Fₙ` along the
morphism `Xₙ ⟶ X_(n+1)`, so it is quasi-coherent (Proposition 5.8(c)); the kernel of the
epimorphism `F_(n+1) ⟶ F / J ^ (n + 1) F` is then quasi-coherent, and global sections on the
affine scheme `X_(n+1)` are exact (Proposition 5.6). -/
theorem surjective_powQuotientMap
    {F : SheafOfModules.{u} (structureRingCatSheaf X.toLocallyRingedSpace)}
    (hF : IsCoherentFormalModule F) (n : ℕ) [IsAffine (h.pow_succ (n + 1)).quotientScheme] :
    Function.Surjective ((sheafOfModulesAbMap (J.powQuotientMap F n)).app (op ⊤)) := by
  let h0 := h.pow_succ n
  let h1 := h.pow_succ (n + 1)
  have hle : J ^ (n + 1 + 1) ≤ J ^ (n + 1) := J.pow_le_pow_right (Nat.le_succ _)
  let k := quotientSchemeMap h0 h1 hle
  let M := h1.quotientModule (annihilates_powQuotient_succ F n)
  let ι := h1.quotientPushforwardQuotientModuleIso (annihilates_powQuotient_succ F n)
  have hcoh := (h.reconstruction hF).1
  have : (h.reduction F n).IsQuasicoherent := (hcoh n).isQuasicoherent
  have : (h.reduction F (n + 1)).IsQuasicoherent := (hcoh (n + 1)).isQuasicoherent
  -- `M` is the pushforward of `Fₙ` along `k`, hence quasi-coherent
  have : M.IsQuasicoherent := by
    have := h.isIso_toReduction F n
    let e : h1.quotientPushforward.obj ((Scheme.Modules.pushforward k).obj (h.reduction F n)) ≅
        h1.quotientPushforward.obj M :=
      quotientPushforwardSchemeMapIso h0 h1 hle _ ≪≫ (asIso (h.toReduction F n)).symm ≪≫ ι.symm
    exact QcqsPushforward.isQuasicoherent_of_iso
      ((Functor.FullyFaithful.ofFullyFaithful _).preimageIso e)
      (isQuasicoherent_pushforward k (Or.inl inferInstance) _)
  -- the epimorphism `F_(n+1) ⟶ M`
  have := h.isIso_toReduction F (n + 1)
  let g : h1.quotientPushforward.obj (h.reduction F (n + 1)) ⟶ h1.quotientPushforward.obj M :=
    (asIso (h.toReduction F (n + 1))).inv ≫ J.powQuotientMap F n ≫ ι.inv
  let φ := h1.quotientPushforward.preimage g
  have : Epi (J.powQuotientπ F n) := inferInstanceAs (Epi (J.powQuotientπ
    (show SheafOfModules (ringCatSheafOf X.toLocallyRingedSpace.sheaf) from F) n))
  have : Epi (J.powQuotientMap F n) := epi_of_epi_fac (J.powQuotientπ_powQuotientMap F n)
  have : Epi g := by
    have e1 : Epi (asIso (h.toReduction F (n + 1))).inv :=
      @IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv _)
    have e3 : Epi ι.inv := @IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv _)
    exact @epi_comp _ _ _ _ _ _ e1 _ (@epi_comp _ _ _ _ _ _ this _ e3)
  have : Epi φ := h1.quotientPushforward.epi_of_epi_map (by
    rw [Functor.map_preimage]
    infer_instance)
  let S := ShortComplex.mk (kernel.ι φ) φ (kernel.condition φ)
  have hS : S.ShortExact := { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel φ) }
  have : S.X₁.IsQuasicoherent := isQuasicoherent_kernel φ
  have hsurj : Function.Surjective ((sheafOfModulesAbMap (h1.quotientPushforward.map φ)).app
      (op ⊤)) := by
    have h2 := (ModuleCat.epi_iff_surjective _).mp (affine_globalSections_shortExact S hS).epi_g
    exact h2
  intro y
  obtain ⟨z, hz⟩ := hsurj y
  refine ⟨(sheafOfModulesAbMap (asIso (h.toReduction F (n + 1))).inv).app (op ⊤) z, ?_⟩
  have hg := congrArg (fun f => (sheafOfModulesAbMap f).app (op ⊤) z)
    (Functor.map_preimage h1.quotientPushforward g)
  exact hg.symm.trans hz

end Reduction

end IsIdealOfDefinition

end Hartshorne

/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.TildeInjectiveFlasque
import Hartshorne.Scheme.QcqsPushforwardQuasicoherent
import Hartshorne.Scheme.AffineGlobalSectionsExact
import Hartshorne.Scheme.AffineTildeLocalization
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Hartshorne.Scheme.Differentials.LocallyFreeSectionsExtend

/-!
# Quasi-coherent flasque envelopes

Hartshorne, *Algebraic Geometry*, III, Corollary 3.6 (p. 215).

On a Noetherian scheme `X`, every quasi-coherent `𝒪_X`-module `F` embeds into a flasque
quasi-coherent `𝒪_X`-module (`Hartshorne.exists_mono_isFlasque_isQuasicoherent`).

## Proof

Cover `X` by finitely many affine opens `fᵢ : Spec Aᵢ ⟶ X`. Then `F|_{Spec Aᵢ} ≅ M̃ᵢ` with
`Mᵢ = Γ(Spec Aᵢ, F)`; embed `Mᵢ` into an injective `Aᵢ`-module `Iᵢ`. The sheaf `Ĩᵢ` is flasque
(Proposition III.3.4, `tilde_isFlasque`), so `G = ⨁ᵢ fᵢ_* Ĩᵢ` is flasque (pushforwards and finite
direct sums of flasque sheaves are flasque) and quasi-coherent (`fᵢ` is quasi-compact and
quasi-separated). The maps `F ⟶ fᵢ_* Ĩᵢ` adjoint to `F|_{Spec Aᵢ} ≅ M̃ᵢ ↪ Ĩᵢ` are jointly
injective on sections, because a section of `F` vanishing on each `fᵢ(Spec Aᵢ)` vanishes.
-/

universe u

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry

namespace Hartshorne

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

variable {X : Scheme.{u}}

/-- The pushforward of an `𝒪_X`-module with flasque underlying sheaf is flasque. -/
theorem isFlasque_pushforward {Y : Scheme.{u}} (f : X ⟶ Y) (G : X.Modules)
    [TopCat.Presheaf.IsFlasque G.presheaf] :
    TopCat.Presheaf.IsFlasque ((Scheme.Modules.pushforward f).obj G).presheaf where
  epi i := TopCat.Presheaf.IsFlasque.epi (F := G.presheaf) ((Opens.map f.base).op.map i)

/-- A finite direct sum of `𝒪_X`-modules with flasque underlying sheaves is flasque. -/
theorem isFlasque_biproduct {ι : Type} [Fintype ι] (H : ι → X.Modules)
    (hH : ∀ j, TopCat.Presheaf.IsFlasque (H j).presheaf) :
    TopCat.Presheaf.IsFlasque (⨁ H).presheaf where
  epi {U V} i := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro s
    choose t ht using fun j => (AddCommGrpCat.epi_iff_surjective _).1 ((hH j).epi i)
      ((biproduct.π H j).app V.unop s)
    refine ⟨∑ j, (biproduct.ι H j).app U.unop (t j), ?_⟩
    have hnat (j : ι) (y : Γ(H j, U.unop)) :
        (⨁ H).presheaf.map i ((biproduct.ι H j).app U.unop y) =
          (biproduct.ι H j).app V.unop ((H j).presheaf.map i y) :=
      (ConcreteCategory.congr_hom ((biproduct.ι H j).mapPresheaf.naturality i) y).symm
    rw [map_sum]
    simp_rw [hnat, ht]
    have := Scheme.Modules.sum_app_apply Finset.univ
      (fun j => biproduct.π H j ≫ biproduct.ι H j) V.unop s
    have htot : (∑ j, biproduct.π H j ≫ biproduct.ι H j) = 𝟙 (⨁ H) := biproduct.total
    rw [htot] at this
    exact this.symm

namespace FlasqueEnvelope

variable (F : X.Modules) (V : X.affineOpens)

/-- The `Γ(X, V)`-module of sections of `F` over the affine open `V`. -/
noncomputable abbrev chartModule : ModuleCat.{u} Γ(X, (V : X.Opens)) :=
  (modulesSpecToSheaf.obj (specRestriction F V)).presheaf.obj (op ⊤)

/-- An injective `Γ(X, V)`-module containing the sections of `F` over `V`. -/
noncomputable abbrev chartInjective : ModuleCat.{u} Γ(X, (V : X.Opens)) :=
  Injective.under (chartModule F V)

/-- The pushforward to `X` of the sheaf associated to `chartInjective F V`. -/
noncomputable abbrev chartEnvelope : X.Modules :=
  (Scheme.Modules.pushforward V.2.fromSpec).obj (tilde (chartInjective F V))

variable [F.IsQuasicoherent]

/-- The embedding `F|_V ≅ Γ(V, F)~ ⟶ I~` on `Spec Γ(X, V)`. -/
noncomputable def chartMap : specRestriction F V ⟶ tilde (chartInjective F V) :=
  letI : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
  haveI : IsIso (specRestriction F V).fromTildeΓ :=
    (isQuasicoherent_iff_isIso_fromTildeΓ _).mp inferInstance
  inv (specRestriction F V).fromTildeΓ ≫ tilde.map (Injective.ι (chartModule F V))

instance : Mono (chartMap F V) := by
  let : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
  have : IsIso (specRestriction F V).fromTildeΓ :=
    (isQuasicoherent_iff_isIso_fromTildeΓ _).mp inferInstance
  have := affineTilde_map_mono (Injective.ι (chartModule F V))
  unfold chartMap
  infer_instance

/-- The map `F ⟶ f_* I~` adjoint to `chartMap`, for `f : Spec Γ(X, V) ⟶ X`. -/
noncomputable def toChartEnvelope : F ⟶ chartEnvelope F V :=
  letI : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
  (Scheme.Modules.restrictAdjunction V.2.fromSpec).homEquiv F _ (chartMap F V)

lemma toChartEnvelope_app (U : X.Opens) (s : Γ(F, U)) :
    letI : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
    (toChartEnvelope F V).app U s = (chartMap F V).app (V.2.fromSpec ⁻¹ᵁ U)
      (F.presheaf.map (homOfLE (V.2.fromSpec.image_preimage_le U)).op s) := by
  let : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
  unfold toChartEnvelope
  rw [Adjunction.homEquiv_unit]
  rfl

end FlasqueEnvelope

open FlasqueEnvelope in

/-- **Hartshorne III, Corollary 3.6.** On a Noetherian scheme, every quasi-coherent
`𝒪_X`-module `F` admits a monomorphism `F ⟶ G` into a flasque quasi-coherent `𝒪_X`-module `G`. -/
theorem exists_mono_isFlasque_isQuasicoherent [IsNoetherian X] (F : X.Modules)
    [F.IsQuasicoherent] :
    ∃ (G : X.Modules) (ι : F ⟶ G), Mono ι ∧ TopCat.Presheaf.IsFlasque G.presheaf ∧
      G.IsQuasicoherent := by
  classical
  obtain ⟨t, ht⟩ := (NoetherianSpace.isCompact (Set.univ : Set X)).elim_finite_subcover
    (fun V : X.affineOpens => ((V : X.Opens) : Set X)) (fun V => V.1.isOpen)
    fun x _ => by
      have hx : x ∈ (⨆ V : X.affineOpens, (V : X.Opens)) := by
        rw [iSup_affineOpens_eq_top]
        trivial
      obtain ⟨V, hxV⟩ := Opens.mem_iSup.1 hx
      exact Set.mem_iUnion.2 ⟨V, hxV⟩
  let e := t.equivFin
  let Vf : Fin t.card → X.affineOpens := fun i => (e.symm i).1
  let H : Fin t.card → X.Modules := fun i => chartEnvelope F (Vf i)
  let φ : F ⟶ ⨁ H := biproduct.lift fun i => toChartEnvelope F (Vf i)
  have hinj (U : X.Opens) : Function.Injective (φ.app U) := by
    intro s s' h
    rw [← sub_eq_zero]
    have hd : φ.app U (s - s') = 0 := by rw [map_sub, h, sub_self]
    refine TopCat.Presheaf.section_ext ⟨F.presheaf, F.isSheaf⟩ U (s - s') 0 fun x hx => ?_
    obtain ⟨V₀, hV₀, hxV₀⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    let k := e ⟨V₀, hV₀⟩
    let V := Vf k
    have hxV : x ∈ (V : X.Opens) := by
      have : V = V₀ := by simp [V, Vf, k]
      rw [this]
      exact hxV₀
    let : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
    have hW := V.2.fromSpec.image_preimage_le U
    have hxW : x ∈ V.2.fromSpec ''ᵁ (V.2.fromSpec ⁻¹ᵁ U) := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, V.2.opensRange_fromSpec]
      exact ⟨hxV, hx⟩
    have h1 : (toChartEnvelope F V).app U (s - s') = 0 := by
      have := congrArg ((biproduct.π H k).app U) hd
      rw [map_zero] at this
      rw [← this]
      change _ = (φ ≫ biproduct.π H k).app U (s - s')
      rw [biproduct.lift_π]
    rw [toChartEnvelope_app] at h1
    have h2 : F.presheaf.map (homOfLE hW).op (s - s') = 0 :=
      modules_app_injective (chartMap F V) (V.2.fromSpec ⁻¹ᵁ U) (h1.trans (map_zero _).symm)
    change F.presheaf.germ U x hx (s - s') = F.presheaf.germ U x hx 0
    rw [← TopCat.Presheaf.germ_res_apply F.presheaf (homOfLE hW) x hxW (s - s'), h2, map_zero,
      map_zero]
  refine ⟨⨁ H, φ, (SheafOfModules.forget _).mono_of_mono_map
    (PresheafOfModules.mono_of_injective fun U => hinj U.unop), ?_, ?_⟩
  · refine isFlasque_biproduct H fun i => ?_
    have := IsLocallyNoetherian.component_noetherian (Vf i)
    have : Injective (ModuleCat.of Γ(X, (Vf i : X.Opens)) (chartInjective F (Vf i))) :=
      inferInstanceAs (Injective (Injective.under (chartModule F (Vf i))))
    have : Module.Injective Γ(X, (Vf i : X.Opens)) (chartInjective F (Vf i)) :=
      Module.injective_module_of_injective_object _ _
    have := tilde_isFlasque (chartInjective F (Vf i))
    exact isFlasque_pushforward _ _
  · have hH : ∀ i, (H i).IsQuasicoherent := fun i =>
      isQuasicoherent_pushforward_of_qcqs (Vf i).2.fromSpec _
    have := isQuasicoherent_isClosedUnderFiniteProducts (X := X)
    exact ObjectProperty.prop_of_isLimit_fan (C := SheafOfModules X.ringCatSheaf) _
      (biproduct.isLimit H) hH

end Hartshorne

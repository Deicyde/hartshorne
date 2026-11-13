/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.RingedSpace.SheafExtRestrictIterated

/-!
# Sheaf Hom and sheaf Ext under a homeomorphism

Let `H : B ≅ A` be a homeomorphism of topological spaces, `𝒪_A` and `𝒪_B` sheaves of commutative
rings on `A` and `B`, identified along `H` by morphisms of ring sheaves `φ` and `ψ`. Pushforward
of modules along the induced equivalence of the sites of opens is an equivalence of categories
`τ : 𝒪_B-modules ≌ 𝒪_A-modules` (`Hartshorne.Ringed.Transport.moduleEquiv`). It commutes with
sheaf Hom, `τ(ℋom_B(F, G)) ≅ ℋom_A(τF, τG)` naturally in `G`
(`Hartshorne.Ringed.Transport.homTransportIso`), and hence with sheaf Ext,
`τ(ℰxtⁿ_B(F, G)) ≅ ℰxtⁿ_A(τF, τG)` (`Hartshorne.Ringed.Transport.sheafExtTransportIso`).

## Proof

On sections over an open `W` of `A`, both sides are morphisms of module sheaves over the opens
contained in `W` and in its image `W'` in `B`; these sites are identified by the homeomorphism
(`CategoryTheory.Over.postEquiv`), compatibly with the ring sheaves, which identifies the two
module categories. Sheaf Ext then commutes with `τ`, an exact functor preserving injectives, by
`Hartshorne.RightDerivedComp.rightDerivedCompIso`.
-/

universe u

open CategoryTheory Opposite TopologicalSpace Limits

namespace Hartshorne

namespace Ringed

namespace Transport

section Sites

variable {A B : TopCat.{u}} (H : B ≅ A)

/-- Preimage along a homeomorphism is cocontinuous for the topologies of open covers. -/
lemma map_isCocontinuous :
    (Opens.map H.hom).IsCocontinuous (Opens.grothendieckTopology A)
      (Opens.grothendieckTopology B) where
  cover_lift {W} S hS := by
    intro x hx
    have hx' : H.inv x ∈ (Opens.map H.hom).obj W := by
      change H.hom (H.inv x) ∈ W
      rwa [← ConcreteCategory.comp_apply, H.inv_hom_id, TopCat.id_app]
    obtain ⟨U, f, hf, hxU⟩ := hS (H.inv x) hx'
    have hle : (Opens.map H.hom).obj ((Opens.map H.inv).obj U) ≤ U := by
      intro b hb
      change H.inv (H.hom b) ∈ U at hb
      rwa [← ConcreteCategory.comp_apply, H.hom_inv_id, TopCat.id_app] at hb
    refine ⟨(Opens.map H.inv).obj U, homOfLE ?_, ?_, hxU⟩
    · intro y hy
      have := leOfHom f hy
      change H.hom (H.inv y) ∈ W at this
      rwa [← ConcreteCategory.comp_apply, H.inv_hom_id, TopCat.id_app] at this
    · exact S.downward_closed hf (homOfLE hle)

/-- The equivalence of the sites of opens induced by a homeomorphism `B ≅ A`. -/
noncomputable abbrev opensEquiv : Opens A ≌ Opens B := Opens.mapMapIso H

instance : (opensEquiv H).functor.IsCocontinuous (Opens.grothendieckTopology A)
    (Opens.grothendieckTopology B) := map_isCocontinuous H

instance : (opensEquiv H).inverse.IsCocontinuous (Opens.grothendieckTopology B)
    (Opens.grothendieckTopology A) := map_isCocontinuous H.symm

instance : (opensEquiv H).functor.IsContinuous (Opens.grothendieckTopology A)
    (Opens.grothendieckTopology B) :=
  inferInstanceAs ((Opens.map H.hom).IsContinuous _ _)

instance : (opensEquiv H).inverse.IsContinuous (Opens.grothendieckTopology B)
    (Opens.grothendieckTopology A) :=
  inferInstanceAs ((Opens.map H.inv).IsContinuous _ _)

variable (W : Opens A)

/-- The equivalence between the opens contained in `W` and in its preimage. -/
noncomputable abbrev overOpensEquiv : Over W ≌ Over ((opensEquiv H).functor.obj W) :=
  Over.postEquiv W (opensEquiv H)

instance : (overOpensEquiv H W).functor.IsCocontinuous
    ((Opens.grothendieckTopology A).over W)
    ((Opens.grothendieckTopology B).over ((opensEquiv H).functor.obj W)) :=
  inferInstanceAs ((Over.post _).IsCocontinuous _ _)

instance : (overOpensEquiv H W).inverse.IsCocontinuous
    ((Opens.grothendieckTopology B).over ((opensEquiv H).functor.obj W))
    ((Opens.grothendieckTopology A).over W) :=
  CategoryTheory.isCocontinuous_comp _ _ _ ((Opens.grothendieckTopology A).over _)

instance : (overOpensEquiv H W).functor.IsDenseSubsite
    ((Opens.grothendieckTopology A).over W)
    ((Opens.grothendieckTopology B).over ((opensEquiv H).functor.obj W)) :=
  Equivalence.isDenseSubsite_functor_of_isCocontinuous _ _ _

instance : (overOpensEquiv H W).inverse.IsDenseSubsite
    ((Opens.grothendieckTopology B).over ((opensEquiv H).functor.obj W))
    ((Opens.grothendieckTopology A).over W) :=
  Equivalence.isDenseSubsite_inverse_of_isCocontinuous _ _ _

end Sites

section Modules

variable {A B : TopCat.{u}} (H : B ≅ A)

/-- An identification of sheaves of commutative rings `𝒪_A` and `𝒪_B` along a homeomorphism
`H : B ≅ A`: morphisms of ring sheaves in both directions over the induced equivalence of sites,
compatible with its unit and counit. -/
structure RingTransport (S : Sheaf (Opens.grothendieckTopology A) CommRingCat.{u})
    (T : Sheaf (Opens.grothendieckTopology B) CommRingCat.{u}) where
  /-- The morphism `𝒪_A ⟶ τ 𝒪_B`. -/
  φ : ringCatSheafOf S ⟶ ((opensEquiv H).functor.sheafPushforwardContinuous RingCat.{u}
    (Opens.grothendieckTopology A) (Opens.grothendieckTopology B)).obj (ringCatSheafOf T)
  /-- The morphism `𝒪_B ⟶ τ⁻¹ 𝒪_A`. -/
  ψ : ringCatSheafOf T ⟶ ((opensEquiv H).inverse.sheafPushforwardContinuous RingCat.{u}
    (Opens.grothendieckTopology B) (Opens.grothendieckTopology A)).obj (ringCatSheafOf S)
  /-- Compatibility with the counit. -/
  H₁ : Functor.whiskerRight (NatTrans.op (opensEquiv H).counit) (ringCatSheafOf T).obj =
    ψ.hom ≫ (opensEquiv H).inverse.op.whiskerLeft φ.hom
  /-- Compatibility with the unit. -/
  H₂ : φ.hom ≫ (opensEquiv H).functor.op.whiskerLeft ψ.hom ≫
    Functor.whiskerRight (NatTrans.op (opensEquiv H).unit) (ringCatSheafOf S).obj =
      𝟙 (ringCatSheafOf S).obj

variable {H} {S : Sheaf (Opens.grothendieckTopology A) CommRingCat.{u}}
  {T : Sheaf (Opens.grothendieckTopology B) CommRingCat.{u}} (ρ : RingTransport H S T)

/-- The equivalence `𝒪_B-modules ≌ 𝒪_A-modules` given by pushforward along the homeomorphism. -/
noncomputable abbrev moduleEquiv :
    SheafOfModules.{u} (ringCatSheafOf T) ≌ SheafOfModules.{u} (ringCatSheafOf S) :=
  SheafOfModules.pushforwardPushforwardEquivalence (opensEquiv H) ρ.φ ρ.ψ ρ.H₁ ρ.H₂

/-- Pushforward of modules along the homeomorphism, `τ : 𝒪_B-modules ⥤ 𝒪_A-modules`. -/
noncomputable abbrev transport :
    SheafOfModules.{u} (ringCatSheafOf T) ⥤ SheafOfModules.{u} (ringCatSheafOf S) :=
  (moduleEquiv ρ).functor

variable (W : Opens A)

/-- The identification of the restricted ring sheaves over `W` and over its preimage. -/
noncomputable def overφ : (ringCatSheafOf S).over W ⟶
    ((overOpensEquiv H W).functor.sheafPushforwardContinuous RingCat.{u}
      ((Opens.grothendieckTopology A).over W)
      ((Opens.grothendieckTopology B).over ((opensEquiv H).functor.obj W))).obj
        ((ringCatSheafOf T).over ((opensEquiv H).functor.obj W)) :=
  ⟨Functor.whiskerLeft (Over.forget W).op ρ.φ.hom⟩

/-- The inverse identification of the restricted ring sheaves. -/
noncomputable def overψ : (ringCatSheafOf T).over ((opensEquiv H).functor.obj W) ⟶
    ((overOpensEquiv H W).inverse.sheafPushforwardContinuous RingCat.{u}
      ((Opens.grothendieckTopology B).over ((opensEquiv H).functor.obj W))
      ((Opens.grothendieckTopology A).over W)).obj ((ringCatSheafOf S).over W) :=
  ⟨Functor.whiskerLeft (Over.forget _).op ρ.ψ.hom⟩

/-- Module sheaves over the opens contained in the preimage of `W` are module sheaves over the opens
contained in `W`. -/
noncomputable def overModuleEquiv :
    SheafOfModules.{u} ((ringCatSheafOf T).over ((opensEquiv H).functor.obj W)) ≌
      SheafOfModules.{u} ((ringCatSheafOf S).over W) :=
  SheafOfModules.pushforwardPushforwardEquivalence (overOpensEquiv H W) (overφ ρ W) (overψ ρ W)
    (by
      ext B' : 2
      exact NatTrans.congr_app ρ.H₁ (op B'.unop.left))
    (by
      ext A' : 2
      exact NatTrans.congr_app ρ.H₂ (op A'.unop.left))

end Modules

section Hom

variable {A B : TopCat.{u}} {H : B ≅ A} {S : Sheaf (Opens.grothendieckTopology A) CommRingCat.{u}}
  {T : Sheaf (Opens.grothendieckTopology B) CommRingCat.{u}} (ρ : RingTransport H S T)

/-- On sections over an open `W` of `A`: a morphism `F|_{W'} ⟶ G|_{W'}` over the opens of `B`
contained in the preimage `W'` of `W`, regarded over the opens of `A` contained in `W`. -/
noncomputable def homTransportApp (F G : SheafOfModules.{u} (ringCatSheafOf T)) (W : Opens A) :
    (F.over ((opensEquiv H).functor.obj W) ⟶ G.over ((opensEquiv H).functor.obj W)) →
      (((transport ρ).obj F).over W ⟶ ((transport ρ).obj G).over W) :=
  fun σ => (overModuleEquiv ρ W).functor.map σ

lemma homTransportApp_app (F G : SheafOfModules.{u} (ringCatSheafOf T)) (W : Opens A)
    (σ : F.over ((opensEquiv H).functor.obj W) ⟶ G.over ((opensEquiv H).functor.obj W))
    (A' : (Over W)ᵒᵖ) (x : F.val.obj (op ((opensEquiv H).functor.obj A'.unop.left))) :
    (homTransportApp ρ F G W σ).val.app A' x =
      σ.val.app (op ((Over.post (X := W) (opensEquiv H).functor).obj A'.unop)) x := rfl

lemma homTransportApp_bijective (F G : SheafOfModules.{u} (ringCatSheafOf T)) (W : Opens A) :
    Function.Bijective (homTransportApp ρ F G W) :=
  (overModuleEquiv ρ W).fullyFaithfulFunctor.map_bijective _ _

/-- The morphism `τ(ℋom_B(F, G)) ⟶ ℋom_A(τF, τG)`. -/
noncomputable def homTransport (F G : SheafOfModules.{u} (ringCatSheafOf T)) :
    (transport ρ).obj (moduleSheafHom F G) ⟶
      moduleSheafHom ((transport ρ).obj F) ((transport ρ).obj G) where
  val := PresheafOfModules.homMk
    { app W := AddCommGrpCat.ofHom
        { toFun := homTransportApp ρ F G W.unop
          map_zero' := by
            apply SheafOfModules.hom_ext
            ext A' x
            rfl
          map_add' σ τ := by
            apply SheafOfModules.hom_ext
            ext A' x
            rfl }
      naturality W W' i := by
        ext σ
        apply SheafOfModules.hom_ext
        ext A' x
        rfl }
    (fun W r σ => by
      apply SheafOfModules.hom_ext
      ext A' x
      refine (moduleSheafHomOver_smul_app F G _ (ρ.φ.hom.app W r) σ
          (op ((Over.post (X := W.unop) (opensEquiv H).functor).obj A'.unop)) x).trans
        (Eq.trans ?_ (moduleSheafHomOver_smul_app _ _ W.unop r
          (homTransportApp ρ F G W.unop σ) A' x).symm)
      have hn := (ConcreteCategory.congr_hom (ρ.φ.hom.naturality A'.unop.hom.op) r).symm
      dsimp only
      erw [hn]
      rfl)

/-- On sections, `Hartshorne.Ringed.Transport.homTransport` is
`Hartshorne.Ringed.Transport.homTransportApp`. -/
lemma homTransport_app_apply (F G : SheafOfModules.{u} (ringCatSheafOf T)) (W : (Opens A)ᵒᵖ)
    (σ : F.over ((opensEquiv H).functor.obj W.unop) ⟶ G.over ((opensEquiv H).functor.obj W.unop)) :
    (homTransport ρ F G).val.app W σ = homTransportApp ρ F G W.unop σ := rfl

lemma isIso_homTransport (F G : SheafOfModules.{u} (ringCatSheafOf T)) :
    IsIso (homTransport ρ F G) := by
  refine ModuleGluing.isIso_of_bijective _ (fun W => ?_)
  have h : ⇑((homTransport ρ F G).val.app W) = homTransportApp ρ F G W.unop :=
    funext (homTransport_app_apply ρ F G W)
  rw [h]
  exact homTransportApp_bijective ρ F G W.unop

lemma homTransport_naturality (F : SheafOfModules.{u} (ringCatSheafOf T))
    {G G' : SheafOfModules.{u} (ringCatSheafOf T)} (g : G ⟶ G') :
    (transport ρ).map ((moduleSheafHomFunctor F).map g) ≫ homTransport ρ F G' =
      homTransport ρ F G ≫ (moduleSheafHomFunctor ((transport ρ).obj F)).map
        ((transport ρ).map g) := by
  apply SheafOfModules.hom_ext
  ext W σ : 3
  apply SheafOfModules.hom_ext
  ext A' x
  rfl

/-- **Sheaf Hom commutes with transport along a homeomorphism**:
`τ(ℋom_B(F, -)) ≅ ℋom_A(τF, τ(-))`. -/
noncomputable def homTransportIso (F : SheafOfModules.{u} (ringCatSheafOf T)) :
    moduleSheafHomFunctor F ⋙ transport ρ ≅
      transport ρ ⋙ moduleSheafHomFunctor ((transport ρ).obj F) :=
  NatIso.ofComponents (fun G => @asIso _ _ _ _ (homTransport ρ F G) (isIso_homTransport ρ F G))
    (fun g => homTransport_naturality ρ F g)

end Hom

section Ext

variable {A B : TopCat.{u}} {H : B ≅ A} {S : Sheaf (Opens.grothendieckTopology A) CommRingCat.{u}}
  {T : Sheaf (Opens.grothendieckTopology B) CommRingCat.{u}} (ρ : RingTransport H S T)

attribute [local instance 2000] Abelian.toPreadditive

instance : (transport ρ).Additive := Functor.additive_of_preserves_binary_products _

/-- Transport preserves injective objects. -/
lemma injective_transport_obj (J : SheafOfModules.{u} (ringCatSheafOf T)) (hJ : Injective J) :
    Injective ((transport ρ).obj J) :=
  (Equivalence.map_injective_iff (moduleEquiv ρ) J).2 hJ

/-- **Sheaf Ext commutes with transport along a homeomorphism**:
`τ(ℰxtⁿ_B(F, G)) ≅ ℰxtⁿ_A(τF, τG)`. -/
noncomputable def sheafExtTransportIso (F G : SheafOfModules.{u} (ringCatSheafOf T)) (n : ℕ) :
    (transport ρ).obj ((sheafExt F n).obj G) ≅
      (sheafExt ((transport ρ).obj F) n).obj ((transport ρ).obj G) :=
  RightDerivedComp.rightDerivedCompIsoOf (Φ := transport ρ) (H := moduleSheafHomFunctor F)
    (H' := moduleSheafHomFunctor ((transport ρ).obj F)) (injective_transport_obj ρ)
    (homTransportIso ρ F) n (sheafExt F n) (sheafExt_eq F n).symm
    (sheafExt ((transport ρ).obj F) n) (sheafExt_eq _ n).symm G

end Ext

end Transport

end Ringed

end Hartshorne

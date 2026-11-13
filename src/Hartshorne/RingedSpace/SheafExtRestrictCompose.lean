/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.RingedSpace.SheafExtTransport

/-!
# Restricting sheaf Ext twice

Let `(X, 𝒪_X)` be a ringed space, `U` an open subset, `V'` an open subset of the subspace `U`, and
`V` the corresponding open subset of `X`. Restricting from `X` to `U` and then to `V'` is
restriction to `V` followed by the homeomorphism between the subspaces `V` of `X` and `V'` of `U`
(`Hartshorne.Ringed.RestrictCompose.restrictCompIso`). The isomorphisms
`ℰxtⁿ_X(F, G)|_U ≅ ℰxtⁿ_U(F|_U, G|_U)` of Hartshorne III.6, Proposition 6.2, are compatible with
this identification (`Hartshorne.Ringed.sheafExtRestrictIso_restrict_restrict`): the isomorphism
for `V' ⊆ U` composed with the restriction to `V'` of the one for `U ⊆ X` is the transport along the
homeomorphism of the one for `V ⊆ X`, up to the identifications of `F` and `G`.

## Proof

All the isomorphisms are of the form `Φ(RⁿH(G)) ≅ RⁿH'(Φ(G))` for exact functors `Φ` preserving
injectives (`Hartshorne.RightDerivedComp.rightDerivedCompIso`), and two such composites agree as
soon as the underlying identifications of sheaf Hom agree
(`Hartshorne.RightDerivedComp.rightDerivedCompIso_comp_naturality`). For sheaf Hom this is a
computation on sections: both sides send a morphism `σ : F|_W ⟶ G|_W` to the morphism given on
sections by `σ` itself.
-/

universe u

open CategoryTheory Opposite TopologicalSpace Limits

namespace Hartshorne

namespace Ringed

namespace RestrictCompose

open SheafExtRestrict Transport

variable {X : TopCat.{u}} (U : Opens X) (V' : Opens ((Opens.toTopCat X).obj U))

lemma mem_U (b : (Opens.toTopCat X).obj ((incl U).obj V')) : b.1 ∈ U := by
  obtain ⟨y, -, hy⟩ := b.2
  exact hy ▸ y.2

lemma mem_V' (b : (Opens.toTopCat X).obj ((incl U).obj V')) :
    (⟨b.1, mem_U U V' b⟩ : (Opens.toTopCat X).obj U) ∈ V' := by
  obtain ⟨y, hy, hyb⟩ := b.2
  have : y = ⟨b.1, mem_U U V' b⟩ := Subtype.ext hyb
  exact this ▸ hy

/-- The homeomorphism between the subspace `V` of `X` and the subspace `V'` of `U`. -/
def homeo : (Opens.toTopCat X).obj ((incl U).obj V') ≅
    (Opens.toTopCat ((Opens.toTopCat X).obj U)).obj V' where
  hom := TopCat.ofHom ⟨fun b => ⟨⟨b.1, mem_U U V' b⟩, mem_V' U V' b⟩,
    by fun_prop⟩
  inv := TopCat.ofHom ⟨fun (a : (Opens.toTopCat ((Opens.toTopCat X).obj U)).obj V') =>
      (⟨a.1.1, ⟨a.1, a.2, rfl⟩⟩ : (Opens.toTopCat X).obj ((incl U).obj V')),
    by fun_prop⟩
  hom_inv_id := by ext; rfl
  inv_hom_id := by ext; rfl

/-- The open subset of `X` corresponding to an open of the subspace `V'` of `U`. -/
abbrev jA (W : Opens ((Opens.toTopCat ((Opens.toTopCat X).obj U)).obj V')) : Opens X :=
  U.isOpenEmbedding.functor.obj (V'.isOpenEmbedding.functor.obj W)

/-- The open subset of `X` corresponding to an open of the subspace `V` of `X`. -/
abbrev jB (W : Opens ((Opens.toTopCat X).obj ((incl U).obj V'))) : Opens X :=
  ((incl U).obj V').isOpenEmbedding.functor.obj W

lemma jB_le_jA (W : Opens ((Opens.toTopCat ((Opens.toTopCat X).obj U)).obj V')) :
    jB U V' ((opensEquiv (homeo U V')).functor.obj W) ≤ jA U V' W := by
  rintro x ⟨b, hb, rfl⟩
  exact ⟨_, ⟨_, hb, rfl⟩, rfl⟩

lemma jA_le_jB (W : Opens ((Opens.toTopCat ((Opens.toTopCat X).obj U)).obj V')) :
    jA U V' W ≤ jB U V' ((opensEquiv (homeo U V')).functor.obj W) := by
  rintro x ⟨_, ⟨a, ha, rfl⟩, rfl⟩
  exact ⟨(homeo U V').inv a, ha, rfl⟩

lemma jA_le_jB' (W : Opens ((Opens.toTopCat X).obj ((incl U).obj V'))) :
    jA U V' ((opensEquiv (homeo U V')).inverse.obj W) ≤ jB U V' W := by
  rintro x ⟨_, ⟨a, ha, rfl⟩, rfl⟩
  exact ⟨_, ha, rfl⟩

variable (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})

/-- The identification of the restricted structure sheaves of `V'` (via `U`) and of `V`. -/
noncomputable def ringTransport : RingTransport (homeo U V')
    (restrictRingSheaf (restrictRingSheaf R U) V') (restrictRingSheaf R ((incl U).obj V')) where
  φ := ⟨{ app W := (ringCatSheafOf R).obj.map (homOfLE (jB_le_jA U V' W.unop)).op
          naturality W W' f := by
            show (ringCatSheafOf R).obj.map _ ≫ (ringCatSheafOf R).obj.map _ =
              (ringCatSheafOf R).obj.map _ ≫ (ringCatSheafOf R).obj.map _
            rw [← Functor.map_comp, ← Functor.map_comp]
            rfl }⟩
  ψ := ⟨{ app W := (ringCatSheafOf R).obj.map (homOfLE (jA_le_jB' U V' W.unop)).op
          naturality W W' f := by
            show (ringCatSheafOf R).obj.map _ ≫ (ringCatSheafOf R).obj.map _ =
              (ringCatSheafOf R).obj.map _ ≫ (ringCatSheafOf R).obj.map _
            rw [← Functor.map_comp, ← Functor.map_comp]
            rfl }⟩
  H₁ := by
    ext W : 2
    show (ringCatSheafOf R).obj.map _ = (ringCatSheafOf R).obj.map _ ≫
      (ringCatSheafOf R).obj.map _
    rw [← Functor.map_comp]
    rfl
  H₂ := by
    ext W : 2
    show (ringCatSheafOf R).obj.map _ ≫ (ringCatSheafOf R).obj.map _ ≫
      (ringCatSheafOf R).obj.map _ = 𝟙 _
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact (ringCatSheafOf R).obj.map_id _

/-- The two inclusions of the opens of `V'` into the opens of `X` agree. -/
noncomputable def inclIso : (opensEquiv (homeo U V')).functor ⋙
      ((incl U).obj V').isOpenEmbedding.functor ≅
    V'.isOpenEmbedding.functor ⋙ U.isOpenEmbedding.functor :=
  NatIso.ofComponents (fun W => ⟨homOfLE (jB_le_jA U V' W), homOfLE (jA_le_jB U V' W), rfl, rfl⟩)
    (fun _ => rfl)

instance : (V'.isOpenEmbedding.functor ⋙ U.isOpenEmbedding.functor).IsContinuous
    (Opens.grothendieckTopology ((Opens.toTopCat ((Opens.toTopCat X).obj U)).obj V'))
    (Opens.grothendieckTopology X) :=
  Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology ((Opens.toTopCat X).obj U)) _

instance : ((opensEquiv (homeo U V')).functor ⋙
      ((incl U).obj V').isOpenEmbedding.functor).IsContinuous
    (Opens.grothendieckTopology ((Opens.toTopCat ((Opens.toTopCat X).obj U)).obj V'))
    (Opens.grothendieckTopology X) :=
  Functor.isContinuous_comp _ _ _
    (Opens.grothendieckTopology ((Opens.toTopCat X).obj ((incl U).obj V'))) _

/-- The ring map of the twice restricted modules. -/
noncomputable abbrev φA : ringCatSheafOf (restrictRingSheaf (restrictRingSheaf R U) V') ⟶
    ((V'.isOpenEmbedding.functor ⋙ U.isOpenEmbedding.functor).sheafPushforwardContinuous
      RingCat.{u} _ _).obj (ringCatSheafOf R) :=
  restrictedRingHom V' (ringCatSheafOf (restrictRingSheaf R U)) ≫
    (V'.isOpenEmbedding.functor.sheafPushforwardContinuous RingCat.{u} _ _).map
      (restrictedRingHom U (ringCatSheafOf R))

/-- The ring map of the transported restricted modules. -/
noncomputable abbrev φB : ringCatSheafOf (restrictRingSheaf (restrictRingSheaf R U) V') ⟶
    (((opensEquiv (homeo U V')).functor ⋙ ((incl U).obj V').isOpenEmbedding.functor
      ).sheafPushforwardContinuous RingCat.{u} _ _).obj (ringCatSheafOf R) :=
  (ringTransport U V' R).φ ≫ ((opensEquiv (homeo U V')).functor.sheafPushforwardContinuous
    RingCat.{u} _ _).map (restrictedRingHom ((incl U).obj V') (ringCatSheafOf R))

lemma φA_comp : φA U V' R ≫ (Functor.sheafPushforwardContinuousNatTrans (inclIso U V').hom
    RingCat.{u} _ _).app (ringCatSheafOf R) = φB U V' R := by
  ext W : 3
  show (𝟙 _ ≫ 𝟙 _) ≫ (ringCatSheafOf R).obj.map _ = (ringCatSheafOf R).obj.map _ ≫ 𝟙 _
  rw [Category.id_comp, Category.id_comp, Category.comp_id]
  rfl

/-- The pushforwards along the two inclusions agree. -/
noncomputable def restrictCompIso' :
    SheafOfModules.pushforward.{u} (φA U V' R) ≅ SheafOfModules.pushforward.{u} (φB U V' R) :=
  SheafOfModules.pushforwardCongr₂ (φA U V' R) (inclIso U V') (φA_comp U V' R)

/-- **Restricting twice is restricting once, up to the homeomorphism**:
`(F|_U)|_{V'} ≅ τ(F|_V)`, naturally in `F`. -/
noncomputable def restrictCompIso :
    moduleRestrict U ⋙ moduleRestrict (R := restrictRingSheaf R U) V' ≅
      moduleRestrict ((incl U).obj V') ⋙ transport (ringTransport U V' R) :=
  SheafOfModules.pushforwardComp _ _ ≪≫ restrictCompIso' U V' R ≪≫
    (SheafOfModules.pushforwardComp _ _).symm

lemma restrictCompIso_hom_app_val_app (M : SheafOfModules.{u} (ringCatSheafOf R))
    (W : (Opens ((Opens.toTopCat ((Opens.toTopCat X).obj U)).obj V'))ᵒᵖ) (x) :
    ((restrictCompIso U V' R).hom.app M).val.app W x =
      M.val.map (homOfLE (jB_le_jA U V' W.unop)).op x := rfl

end RestrictCompose

end Ringed

end Hartshorne

namespace Hartshorne

namespace Ringed

open SheafExtRestrict Transport RestrictCompose

variable {X : TopCat.{u}} (U : Opens X) (V' : Opens ((Opens.toTopCat X).obj U))
  (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})

attribute [local instance 2000] Abelian.toPreadditive

lemma homRestrict_restrict_restrict (F Y : SheafOfModules.{u} (ringCatSheafOf R)) :
    (moduleRestrict (R := restrictRingSheaf R U) V').map ((homRestrictIso U F).hom.app Y) ≫
      (homRestrictIso V' ((moduleRestrict U).obj F)).hom.app ((moduleRestrict U).obj Y) ≫
        (moduleSheafHomFunctor _).map ((restrictCompIso U V' R).hom.app Y) =
    (restrictCompIso U V' R).hom.app (moduleSheafHom F Y) ≫
      (transport (ringTransport U V' R)).map ((homRestrictIso ((incl U).obj V') F).hom.app Y) ≫
        (homTransportIso (ringTransport U V' R) _).hom.app
          ((moduleRestrict ((incl U).obj V')).obj Y) ≫
          (moduleSheafHomPrecomp ((restrictCompIso U V' R).hom.app F)).app _ := by
  apply SheafOfModules.hom_ext
  ext W σ : 3
  apply SheafOfModules.hom_ext
  ext A' x
  let L : Over ((incl U).obj ((incl V').obj W.unop)) :=
    (Over.post (incl U)).obj ((Over.post (incl V')).obj A'.unop)
  let R' : Over ((incl U).obj ((incl V').obj W.unop)) :=
    Over.mk (homOfLE ((jB_le_jA U V' A'.unop.left).trans (leOfHom L.hom)))
  exact (PresheafOfModules.naturality_apply σ.val
    (Over.homMk (U := R') (V := L) (homOfLE (jB_le_jA U V' A'.unop.left))
      (Subsingleton.elim _ _)).op x).symm

lemma _root_.Hartshorne.Ringed.sheafExtPrecomp_eq_rightDerived {Y : TopCat.{u}}
    {S : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}}
    {F' F : SheafOfModules.{u} (ringCatSheafOf S)} (f : F' ⟶ F)
    (G : SheafOfModules.{u} (ringCatSheafOf S)) (n : ℕ) :
    sheafExtPrecomp f G n = (NatTrans.rightDerived (moduleSheafHomPrecomp f) n).app G := by
  simp only [sheafExtPrecomp, SheafExtContravariant.extMap]
  rfl

lemma sheafExtTransportIso_eq_rightDerivedCompIso {A B : TopCat.{u}} {H : B ≅ A}
    {S : Sheaf (Opens.grothendieckTopology A) CommRingCat.{u}}
    {T : Sheaf (Opens.grothendieckTopology B) CommRingCat.{u}} (ρ : RingTransport H S T)
    (F G : SheafOfModules.{u} (ringCatSheafOf T)) (n : ℕ) :
    sheafExtTransportIso ρ F G n = RightDerivedComp.rightDerivedCompIso (Φ := transport ρ)
      (H := moduleSheafHomFunctor F) (H' := moduleSheafHomFunctor ((transport ρ).obj F))
      (injective_transport_obj ρ) (homTransportIso ρ F) G n :=
  rfl

-- The kernel compares `sheafExt` with the right derived functor it is defined as, inside
-- `Functor.map`; this needs more than the default budget.
set_option maxHeartbeats 1000000 in
/-- **Sheaf Ext restricted twice** (supplementing Hartshorne III.6, Proposition 6.2). For opens
`V' ⊆ U` of `X`, with `V` the open of `X` corresponding to `V'`, the isomorphism
`ℰxtⁿ_X(F, G)|_U ≅ ℰxtⁿ_U(F|_U, G|_U)` restricted to `V'`, followed by the isomorphism for `V' ⊆ U`,
is the transport along the homeomorphism `V ≅ V'` of the isomorphism for `V ⊆ X`, up to the
identifications `(F|_U)|_{V'} ≅ τ(F|_V)` and `(G|_U)|_{V'} ≅ τ(G|_V)`. -/
theorem sheafExtRestrictIso_restrict_restrict (F G : SheafOfModules.{u} (ringCatSheafOf R))
    (n : ℕ) :
    (moduleRestrict (R := restrictRingSheaf R U) V').map (sheafExtRestrictIso U F G n).hom ≫
      (sheafExtRestrictIso V' ((moduleRestrict U).obj F) ((moduleRestrict U).obj G) n).hom ≫
        (sheafExt _ n).map ((restrictCompIso U V' R).hom.app G) =
    (restrictCompIso U V' R).hom.app _ ≫
      (transport (ringTransport U V' R)).map (sheafExtRestrictIso ((incl U).obj V') F G n).hom ≫
        (sheafExtTransportIso (ringTransport U V' R) _ _ n).hom ≫
          sheafExtPrecomp ((restrictCompIso U V' R).hom.app F) _ n := by
  rw [sheafExtPrecomp_eq_rightDerived, sheafExtRestrictIso_eq_rightDerivedCompIso,
    sheafExtRestrictIso_eq_rightDerivedCompIso, sheafExtRestrictIso_eq_rightDerivedCompIso,
    sheafExtTransportIso_eq_rightDerivedCompIso]
  exact RightDerivedComp.rightDerivedCompIso_comp_naturality (homRestrictIso U F)
    (homRestrictIso V' _) (homRestrictIso _ F) (homTransportIso _ _) (restrictCompIso U V' R)
    (moduleSheafHomPrecomp _) (fun I _ => injective_moduleSheafRestrict_obj U _ I)
    (fun I _ => injective_moduleSheafRestrict_obj V' _ I)
    (fun I _ => injective_moduleSheafRestrict_obj _ _ I) (injective_transport_obj _)
    (homRestrict_restrict_restrict U V' R F) G n

end Ringed

end Hartshorne

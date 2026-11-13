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

## Implementation note

The kernel compares two terms that agree only up to unfolding, such as `ℰxtⁿ(F, -)` and the right
derived functor it is defined as, by evaluating them, and evaluating `ℰxt` objects is very costly.
The proofs therefore go through private lemmas stated for abstract categories, bifunctors and
derived-functor families, with every isomorphism a variable given by an equation; instantiated
with `ℰxt`, their conclusions are syntactically the statements, and the equations hold by `rfl`.
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

namespace RightDerivedComp

open Ringed.SheafExtContravariant

variable {C D₁ D₂ E : Type*} [Category C] [Category D₁] [Category D₂] [Category E] [Abelian C]
  [Abelian D₁] [Abelian D₂] [Abelian E] {Φ₁ : C ⥤ D₁} {Φ₂ : D₁ ⥤ E} {Ψ₁ : C ⥤ D₂} {Ψ₂ : D₂ ⥤ E}
  [Φ₁.Additive] [Φ₂.Additive] [Ψ₁.Additive] [Ψ₂.Additive]
  [PreservesFiniteLimits Φ₁] [PreservesFiniteColimits Φ₁] [PreservesFiniteLimits Φ₂]
  [PreservesFiniteColimits Φ₂] [PreservesFiniteLimits Ψ₁] [PreservesFiniteColimits Ψ₁]
  [PreservesFiniteLimits Ψ₂] [PreservesFiniteColimits Ψ₂]
  [HasInjectiveResolutions C] [HasInjectiveResolutions D₁] [HasInjectiveResolutions D₂]
  [HasInjectiveResolutions E]
  {BC : Cᵒᵖ ⥤ C ⥤ C} {BD₁ : D₁ᵒᵖ ⥤ D₁ ⥤ D₁} {BD₂ : D₂ᵒᵖ ⥤ D₂ ⥤ D₂} {BE : Eᵒᵖ ⥤ E ⥤ E}
  [∀ M, (BC.obj M).Additive] [∀ M, (BD₁.obj M).Additive] [∀ M, (BD₂.obj M).Additive]
  [∀ M, (BE.obj M).Additive]

/-- `rightDerivedCompIso_comp_naturality` with every piece abstracted: the derived functors are
families `EC, ED₁, ED₂, EE` equal to those of the bifunctors, and the comparison isomorphisms and
the map induced by `c` are variables equal to `rightDerivedCompIsoOf` and `extMap`. Instantiated
with `ℰxt`, the conclusion is syntactically the statement about `ℰxt`, so the kernel never compares
`ℰxt` objects with right derived functor objects (which would make it evaluate them). -/
private theorem comp_naturality_of_eq
    {EC : C → ℕ → C ⥤ C} (hEC : ∀ M n, (BC.obj (op M)).rightDerived n = EC M n)
    {ED₁ : D₁ → ℕ → D₁ ⥤ D₁} (hED₁ : ∀ M n, (BD₁.obj (op M)).rightDerived n = ED₁ M n)
    {ED₂ : D₂ → ℕ → D₂ ⥤ D₂} (hED₂ : ∀ M n, (BD₂.obj (op M)).rightDerived n = ED₂ M n)
    {EE : E → ℕ → E ⥤ E} (hEE : ∀ M n, (BE.obj (op M)).rightDerived n = EE M n)
    (e₁ : ∀ M, BC.obj (op M) ⋙ Φ₁ ≅ Φ₁ ⋙ BD₁.obj (op (Φ₁.obj M)))
    (e₂ : ∀ M, BD₁.obj (op M) ⋙ Φ₂ ≅ Φ₂ ⋙ BE.obj (op (Φ₂.obj M)))
    (f₁ : ∀ M, BC.obj (op M) ⋙ Ψ₁ ≅ Ψ₁ ⋙ BD₂.obj (op (Ψ₁.obj M)))
    (f₂ : ∀ M, BD₂.obj (op M) ⋙ Ψ₂ ≅ Ψ₂ ⋙ BE.obj (op (Ψ₂.obj M)))
    (c : Φ₁ ⋙ Φ₂ ≅ Ψ₁ ⋙ Ψ₂)
    (hΦ₁ : ∀ I : C, Injective I → Injective (Φ₁.obj I))
    (hΦ₂ : ∀ I : D₁, Injective I → Injective (Φ₂.obj I))
    (hΨ₁ : ∀ I : C, Injective I → Injective (Ψ₁.obj I))
    (hΨ₂ : ∀ I : D₂, Injective I → Injective (Ψ₂.obj I)) (F G : C) (n : ℕ)
    (hθ : ∀ Y, Φ₂.map ((e₁ F).hom.app Y) ≫ (e₂ (Φ₁.obj F)).hom.app (Φ₁.obj Y) ≫
        (BE.obj (op (Φ₂.obj (Φ₁.obj F)))).map (c.hom.app Y) =
      c.hom.app ((BC.obj (op F)).obj Y) ≫ Ψ₂.map ((f₁ F).hom.app Y) ≫
        (f₂ (Ψ₁.obj F)).hom.app (Ψ₁.obj Y) ≫ (BE.map (c.hom.app F).op).app (Ψ₂.obj (Ψ₁.obj Y)))
    (i₁ : Φ₁.obj ((EC F n).obj G) ≅ (ED₁ (Φ₁.obj F) n).obj (Φ₁.obj G))
    (hi₁ : i₁ = rightDerivedCompIsoOf hΦ₁ (e₁ F) n (EC F n) (hEC F n) (ED₁ (Φ₁.obj F) n)
      (hED₁ _ n) G)
    (i₂ : Φ₂.obj ((ED₁ (Φ₁.obj F) n).obj (Φ₁.obj G)) ≅
      (EE (Φ₂.obj (Φ₁.obj F)) n).obj (Φ₂.obj (Φ₁.obj G)))
    (hi₂ : i₂ = rightDerivedCompIsoOf hΦ₂ (e₂ (Φ₁.obj F)) n (ED₁ (Φ₁.obj F) n) (hED₁ _ n)
      (EE (Φ₂.obj (Φ₁.obj F)) n) (hEE _ n) (Φ₁.obj G))
    (j₁ : Ψ₁.obj ((EC F n).obj G) ≅ (ED₂ (Ψ₁.obj F) n).obj (Ψ₁.obj G))
    (hj₁ : j₁ = rightDerivedCompIsoOf hΨ₁ (f₁ F) n (EC F n) (hEC F n) (ED₂ (Ψ₁.obj F) n)
      (hED₂ _ n) G)
    (j₂ : Ψ₂.obj ((ED₂ (Ψ₁.obj F) n).obj (Ψ₁.obj G)) ≅
      (EE (Ψ₂.obj (Ψ₁.obj F)) n).obj (Ψ₂.obj (Ψ₁.obj G)))
    (hj₂ : j₂ = rightDerivedCompIsoOf hΨ₂ (f₂ (Ψ₁.obj F)) n (ED₂ (Ψ₁.obj F) n) (hED₂ _ n)
      (EE (Ψ₂.obj (Ψ₁.obj F)) n) (hEE _ n) (Ψ₁.obj G))
    (t : (EE ((Ψ₁ ⋙ Ψ₂).obj F) n).obj (Ψ₂.obj (Ψ₁.obj G)) ⟶
      (EE ((Φ₁ ⋙ Φ₂).obj F) n).obj (Ψ₂.obj (Ψ₁.obj G)))
    (ht : t = extMap BE EE hEE (c.hom.app F) (Ψ₂.obj (Ψ₁.obj G)) n) :
    Φ₂.map i₁.hom ≫ i₂.hom ≫ (EE _ n).map (c.hom.app G) =
      c.hom.app _ ≫ Ψ₂.map j₁.hom ≫ j₂.hom ≫ t := by
  subst hi₁ hi₂ hj₁ hj₂ ht
  obtain rfl : EC = fun M n => (BC.obj (op M)).rightDerived n := funext₂ fun M n => (hEC M n).symm
  obtain rfl : ED₁ = fun M n => (BD₁.obj (op M)).rightDerived n :=
    funext₂ fun M n => (hED₁ M n).symm
  obtain rfl : ED₂ = fun M n => (BD₂.obj (op M)).rightDerived n :=
    funext₂ fun M n => (hED₂ M n).symm
  obtain rfl : EE = fun M n => (BE.obj (op M)).rightDerived n := funext₂ fun M n => (hEE M n).symm
  have hx : extMap BE (fun M n => (BE.obj (op M)).rightDerived n) hEE (c.hom.app F)
      (Ψ₂.obj (Ψ₁.obj G)) n = (NatTrans.rightDerived (BE.map (c.hom.app F).op) n).app _ := by
    simp [extMap]
  rw [hx]
  exact rightDerivedCompIso_comp_naturality (e₁ F) (e₂ (Φ₁.obj F)) (f₁ F) (f₂ (Ψ₁.obj F)) c
    (BE.map (c.hom.app F).op) hΦ₁ hΦ₂ hΨ₁ hΨ₂ hθ G n

/-- `rightDerivedCompIsoOf` for functors `E`, `E'` equal to the right derived functors is
`rightDerivedCompIso`, up to the types. -/
private theorem rightDerivedCompIsoOf_heq {C D : Type*} [Category C] [Category D] [Abelian C]
    [Abelian D] {Φ : C ⥤ D} [Φ.Additive] [Φ.PreservesHomology]
    (hΦ : ∀ I : C, Injective I → Injective (Φ.obj I)) [HasInjectiveResolutions C]
    [HasInjectiveResolutions D] {H : C ⥤ C} [H.Additive] {H' : D ⥤ D} [H'.Additive]
    (e : H ⋙ Φ ≅ Φ ⋙ H') (n : ℕ) (E : C ⥤ C) (hE : H.rightDerived n = E) (E' : D ⥤ D)
    (hE' : H'.rightDerived n = E') (G : C) :
    HEq (rightDerivedCompIsoOf hΦ e n E hE E' hE' G) (rightDerivedCompIso hΦ e G n) := by
  subst hE hE'
  rfl

/-- `extMap` for functors `E` equal to the right derived functors of `B(M, -)`, with each `B(M, -)`
equal to `K M`, is the morphism of right derived functors induced by `B(f, -)`, up to the types. -/
private theorem extMap_heq {C : Type*} [Category C] [Abelian C] [HasInjectiveResolutions C]
    (B : Cᵒᵖ ⥤ C ⥤ C) [∀ M, (B.obj M).Additive] (K : C → C ⥤ C) [∀ M, (K M).Additive]
    (hB : ∀ M, B.obj (op M) = K M) (E : C → ℕ → C ⥤ C)
    (hE : ∀ M n, (B.obj (op M)).rightDerived n = E M n) {F' F : C} (f : F' ⟶ F)
    (θ : K F ⟶ K F') (hθ : HEq (B.map f.op) θ) (G : C) (n : ℕ)
    (t : (E F n).obj G ⟶ (E F' n).obj G) (ht : t = extMap B E hE f G n) :
    HEq t ((NatTrans.rightDerived θ n).app G) := by
  subst ht
  obtain rfl : K = fun M => B.obj (op M) := funext fun M => (hB M).symm
  obtain rfl : E = fun M n => (B.obj (op M)).rightDerived n := funext₂ fun M n => (hE M n).symm
  obtain rfl := eq_of_heq hθ
  simp only [extMap, eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

end RightDerivedComp

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
    sheafExtPrecomp f G n = (NatTrans.rightDerived (moduleSheafHomPrecomp f) n).app G :=
  eq_of_heq (RightDerivedComp.extMap_heq (moduleSheafHomBifunctor S) moduleSheafHomFunctor
    (fun _ => rfl) sheafExt (fun M n => (sheafExt_eq M n).symm) f (moduleSheafHomPrecomp f)
    HEq.rfl G n (sheafExtPrecomp f G n) rfl)

lemma sheafExtTransportIso_eq_rightDerivedCompIso {A B : TopCat.{u}} {H : B ≅ A}
    {S : Sheaf (Opens.grothendieckTopology A) CommRingCat.{u}}
    {T : Sheaf (Opens.grothendieckTopology B) CommRingCat.{u}} (ρ : RingTransport H S T)
    (F G : SheafOfModules.{u} (ringCatSheafOf T)) (n : ℕ) :
    sheafExtTransportIso ρ F G n = RightDerivedComp.rightDerivedCompIso (Φ := transport ρ)
      (H := moduleSheafHomFunctor F) (H' := moduleSheafHomFunctor ((transport ρ).obj F))
      (injective_transport_obj ρ) (homTransportIso ρ F) G n :=
  eq_of_heq (RightDerivedComp.rightDerivedCompIsoOf_heq (injective_transport_obj ρ)
    (homTransportIso ρ F) n (sheafExt F n) (sheafExt_eq F n).symm (sheafExt _ n)
    (sheafExt_eq _ n).symm G)

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
  refine RightDerivedComp.comp_naturality_of_eq (BC := moduleSheafHomBifunctor R)
    (BD₁ := moduleSheafHomBifunctor (restrictRingSheaf R U))
    (BD₂ := moduleSheafHomBifunctor (restrictRingSheaf R ((incl U).obj V')))
    (BE := moduleSheafHomBifunctor (restrictRingSheaf (restrictRingSheaf R U) V'))
    (EC := sheafExt) (ED₁ := sheafExt) (ED₂ := sheafExt) (EE := sheafExt)
    (fun M n => (sheafExt_eq M n).symm) (fun M n => (sheafExt_eq M n).symm)
    (fun M n => (sheafExt_eq M n).symm) (fun M n => (sheafExt_eq M n).symm)
    (homRestrictIso U) (homRestrictIso V') (homRestrictIso ((incl U).obj V'))
    (homTransportIso (ringTransport U V' R)) (restrictCompIso U V' R)
    (fun I _ => injective_moduleSheafRestrict_obj U (ringCatSheafOf R) I)
    (fun I _ => injective_moduleSheafRestrict_obj V' _ I)
    (fun I _ => injective_moduleSheafRestrict_obj ((incl U).obj V') (ringCatSheafOf R) I)
    (injective_transport_obj (ringTransport U V' R)) F G n ?_
    (sheafExtRestrictIso U F G n) rfl
    (sheafExtRestrictIso V' ((moduleRestrict U).obj F) ((moduleRestrict U).obj G) n) rfl
    (sheafExtRestrictIso ((incl U).obj V') F G n) rfl
    (sheafExtTransportIso (ringTransport U V' R) _ _ n) rfl
    (sheafExtPrecomp ((restrictCompIso U V' R).hom.app F) _ n) rfl
  exact homRestrict_restrict_restrict U V' R F

end Ringed

end Hartshorne

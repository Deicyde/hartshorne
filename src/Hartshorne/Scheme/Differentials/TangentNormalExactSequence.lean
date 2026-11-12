/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.RingedSpace.ModuleSheafDualExact
import Hartshorne.Scheme.Differentials.NormalConormalSheaves
import Hartshorne.Scheme.PicardPullback

/-!
# The tangent-normal exact sequence

Hartshorne, *Algebraic Geometry*, II.8, the exact sequence of tangent and normal sheaves (p. 182).

For a nonsingular closed subvariety `Y` of a nonsingular variety `X`, dualizing the conormal
sequence `0 ⟶ J/J² ⟶ Ω_X ⊗ 𝒪_Y ⟶ Ω_Y ⟶ 0` (Theorem II.8.17) gives a short exact sequence
`0 ⟶ T_Y ⟶ T_X|_Y ⟶ N_{Y/X} ⟶ 0`.

* `Hartshorne.pullbackDualIso`: for a morphism of schemes `f : X ⟶ Y` and an `𝒪_Y`-module `E`
  locally free of finite rank, the canonical map `f^*(E^∨) ⟶ (f^*E)^∨`
  (`Hartshorne.pullbackDualMap`, adjoint to the pairing `f^*E ⊗ f^*(E^∨) ≅ f^*(E ⊗ E^∨) ⟶ 𝒪_X`)
  is an isomorphism (`Hartshorne.pullbackDualMap_isIso`). Near every point it sends the pullback
  of the dual of a frame of `E` to the dual of the pullback frame. The input is that pullback
  commutes with tensor products of locally free sheaves of finite rank
  (`Hartshorne.pullbackTensorMap_isIso_of_isLocallyFreeOfRank`).
* `Hartshorne.tangentNormal_shortExact`: the dual of the conormal sequence,
  `0 ⟶ T_Y ⟶ (i^* Ω_{X/k})^∨ ⟶ N_{Y/X} ⟶ 0`. The conormal sequence is short exact by
  Theorem II.8.17 and `Ω_{Y/k}` is locally free of finite rank by Theorem II.8.15, so its dual is
  short exact (`Hartshorne.Ringed.dualShortComplex_shortExact`).
* `Hartshorne.exists_tangentNormal_shortExact`: the tangent-normal sequence
  `0 ⟶ T_Y ⟶ i^* T_X ⟶ N_{Y/X} ⟶ 0`, where `T_X|_Y = i^* T_X` is identified with
  `(i^* Ω_{X/k})^∨` by `Hartshorne.pullbackDualIso`.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace Hartshorne

namespace Ringed

section Frames

open TopologicalSpace Opposite

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

set_option hygiene false in
/-- `𝒪_X`-modules. -/
local notation "𝓜" => SheafOfModules.{u} (ringCatSheafOf R)

/-- Sections of the structure sheaf over an open. -/
local notation3 "𝒪(" U ")" => R.obj.obj (Opposite.op U)

/-- Sections of a module sheaf over an open, as an abelian group. -/
local notation3 "Γ(" M ", " U ")" => (PresheafOfModules.presheaf (SheafOfModules.val M)).obj
  (Opposite.op U)

/-- **Frames of a tensor product.** If `a` is a frame of `A` over `W` and `b` a frame of `B` over
`W`, then the sections `a i ⊗ b k` form a frame of `A ⊗ B` over `W`. -/
lemma IsLocalFrame.tensor_prod {ι κ : Type*} [Fintype ι] [Fintype κ] {A B : 𝓜}
    {W : Opens X} {a : ι → Γ(A, W)} {b : κ → Γ(B, W)} (ha : IsLocalFrame A W a)
    (hb : IsLocalFrame B W b) :
    IsLocalFrame (moduleSheafTensor A B) W
      (fun p : ι × κ => (moduleSheafTensorBilinear A B).app (Opposite.op W) (a p.1) (b p.2)) := by
  classical
  intro V hV
  let c : (ι × κ → 𝒪(V)) ≃ (κ → ι → 𝒪(V)) :=
    { toFun := fun r k i => r (i, k), invFun := fun s p => s p.2 p.1,
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  have key : ⇑(localFrameMap (moduleSheafTensor A B)
      (fun p : ι × κ => (moduleSheafTensorBilinear A B).app (Opposite.op W) (a p.1) (b p.2)) hV) =
      tensorFrameMap A b hV ∘ (fun s k => localFrameMap A a hV (s k)) ∘ c := by
    funext r
    refine (localFrameMap_apply _ _ _ _).trans ?_
    simp only [Function.comp_apply, tensorFrameMap, localFrameMap_apply]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    refine Eq.trans ?_ (LinearMap.map_sum₂ ((moduleSheafTensorBilinear A B).app _) _ _ _).symm
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Eq.trans ?_ (LinearMap.map_smul₂ ((moduleSheafTensorBilinear A B).app _) _ _ _).symm
    congr 1
    exact (moduleSheafTensorBilinear A B).naturality _ _ _
  rw [key]
  exact (hb.tensorFrameMap_bijective (F := A) hV).comp
    ((Function.Bijective.piMap fun _ => ha V hV).comp c.bijective)

lemma modules_map_refl (A : 𝓜) {U : Opens X} (x : Γ(A, U)) :
    A.val.presheaf.map (homOfLE (le_refl U)).op x = x := by
  rw [show (homOfLE (le_refl U)) = 𝟙 U from rfl, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- The evaluation pairing `E ⊗ E^∨ ⟶ 𝒪_X`, `e ⊗ σ ↦ σ(e)`. -/
noncomputable def moduleSheafDualPairing (E : 𝓜) :
    @Quiver.Hom 𝓜 _ (moduleSheafTensor E (moduleSheafDual E)) (structureModule R) :=
  (moduleSheafTensorHomAdjunction E (moduleSheafDual E) (structureModule R)).symm (𝟙 _)

lemma moduleSheafDualPairing_tmul (E : 𝓜) {U : Opens X} (e : Γ(E, U))
    (σ : Γ(moduleSheafDual E, U)) :
    sectionsMap (moduleSheafDualPairing E) U
        ((moduleSheafTensorBilinear E (moduleSheafDual E)).app (op U) e σ) =
      moduleSheafHomEval σ (le_refl U) e := by
  have h := moduleSheafTensorHomAdjunction_app_eval (moduleSheafDualPairing E) U σ (le_refl U) e
  rw [moduleSheafDualPairing, Equiv.apply_symm_apply, modules_map_refl] at h
  exact h.symm

end Frames

end Ringed

section PullbackDual

open TopologicalSpace Opposite

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Pullback commutes with tensor products of locally free sheaves of finite rank.** This
generalizes `Hartshorne.pullbackTensorMap_isIso` from invertible sheaves, by the same argument. -/
theorem pullbackTensorMap_isIso_of_isLocallyFreeOfRank {L M : Y.Modules} {r s : ℕ}
    (hL : Ringed.IsLocallyFreeOfRank (R := Y.sheaf) L r)
    (hM : Ringed.IsLocallyFreeOfRank (R := Y.sheaf) M s) : IsIso (pullbackTensorMap f L M) := by
  classical
  refine Ringed.modules_isIso_of_locally_bijective (R := X.sheaf) _ fun x => ?_
  obtain ⟨U₁, l, hx₁, hl⟩ := Ringed.exists_isLocalFrame_of_isLocallyFreeOfRank hL (f.base x)
  obtain ⟨U₂, m, hx₂, hm⟩ := Ringed.exists_isLocalFrame_of_isLocallyFreeOfRank hM (f.base x)
  have hl' := hl.restrictLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)
  have hm' := hm.restrictLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)
  have hsrc := Ringed.IsLocalFrame.pullback (φ := f.toRingCatSheafHom) (hl'.tensor_prod hm')
  have htgt := (Ringed.IsLocalFrame.pullback (φ := f.toRingCatSheafHom) hl').tensor_prod
    (Ringed.IsLocalFrame.pullback (φ := f.toRingCatSheafHom) hm')
  exact ⟨f ⁻¹ᵁ (U₁ ⊓ U₂), ⟨hx₁, hx₂⟩, fun V hV =>
    Ringed.IsLocalFrame.app_bijective_of_map _ hsrc htgt
      (fun _ => pullbackTensorMap_app_unit _ _) hV⟩

/-- The pushforward of module sheaves along a morphism of schemes is a right adjoint. -/
lemma pushforward_isRightAdjoint :
    (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint

attribute [local instance] pushforward_isRightAdjoint

/-- The pairing `f^*E ⊗ f^*(E^∨) ≅ f^*(E ⊗ E^∨) ⟶ f^*𝒪_Y ≅ 𝒪_X`, for `E` locally free of finite
rank. -/
noncomputable def pullbackDualPairing (E : Y.Modules) {r : ℕ}
    (hE : Ringed.IsLocallyFreeOfRank (R := Y.sheaf) E r) :
    moduleSheafTensor ((Scheme.Modules.pullback f).obj E)
        ((Scheme.Modules.pullback f).obj (Ringed.moduleSheafDual (R := Y.sheaf) E)) ⟶
      SheafOfModules.unit X.ringCatSheaf :=
  (@asIso X.Modules _ _ _ (pullbackTensorMap f E (Ringed.moduleSheafDual (R := Y.sheaf) E))
      (pullbackTensorMap_isIso_of_isLocallyFreeOfRank f hE
        (Ringed.IsLocallyFreeOfRank.moduleSheafDual hE))).inv ≫
    (Scheme.Modules.pullback f).map (Ringed.moduleSheafDualPairing (R := Y.sheaf) E) ≫
    SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom

/-- The canonical comparison map `f^*(E^∨) ⟶ (f^*E)^∨` for a locally free `E` of finite rank:
adjoint, under the tensor–Hom adjunction, to `Hartshorne.pullbackDualPairing`. -/
noncomputable def pullbackDualMap (E : Y.Modules) {r : ℕ}
    (hE : Ringed.IsLocallyFreeOfRank (R := Y.sheaf) E r) :
    (Scheme.Modules.pullback f).obj (Ringed.moduleSheafDual (R := Y.sheaf) E) ⟶
      Ringed.moduleSheafDual (R := X.sheaf) ((Scheme.Modules.pullback f).obj E) :=
  Ringed.moduleSheafTensorHomAdjunction (R := X.sheaf) _ _ _ (pullbackDualPairing f E hE)

/-- Sections of a module sheaf over an open, as an abelian group. -/
local notation3 "Γₘ(" M ", " U ")" => (PresheafOfModules.presheaf (SheafOfModules.val M)).obj
  (Opposite.op U)

lemma pullback_map_etaSec {A B : Y.Modules} (g : A ⟶ B) {U : Y.Opens} (x : Γₘ(A, U)) :
    Ringed.sectionsMap (R := X.sheaf) ((Scheme.Modules.pullback f).map g) (f ⁻¹ᵁ U)
        (Ringed.etaSec (φ := f.toRingCatSheafHom) x) =
      Ringed.etaSec (φ := f.toRingCatSheafHom) (Ringed.sectionsMap (R := Y.sheaf) g U x) :=
  (ConcreteCategory.congr_hom (congrArg (fun φ => Ringed.sectionsMap (R := Y.sheaf) φ U)
    ((SheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom).unit.naturality g)) x).symm

lemma pullbackObjUnitToUnit_etaSec {U : Y.Opens}
    (a : Γₘ(SheafOfModules.unit Y.ringCatSheaf, U)) :
    Ringed.sectionsMap (R := X.sheaf)
        (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) (f ⁻¹ᵁ U)
        (Ringed.etaSec (φ := f.toRingCatSheafHom) a) =
      Ringed.phiApp f.toRingCatSheafHom U a := by
  have h : Ringed.pullbackUnit f.toRingCatSheafHom (SheafOfModules.unit _) ≫
      (SheafOfModules.pushforward f.toRingCatSheafHom).map
        (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
    ((SheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom).homEquiv_unit
      _ _ _).symm.trans
      (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _)
  exact ConcreteCategory.congr_hom (congrArg (fun φ => Ringed.sectionsMap (R := Y.sheaf) φ U) h) a

lemma pullbackTensorMap_inv_etaSec {L M : Y.Modules} (hiso : IsIso (pullbackTensorMap f L M))
    {U : Y.Opens} (l : Γₘ(L, U)) (m : Γₘ(M, U)) :
    Ringed.sectionsMap (R := X.sheaf) (@asIso X.Modules _ _ _ (pullbackTensorMap f L M) hiso).inv
        (f ⁻¹ᵁ U)
        ((moduleSheafTensorBilinear ((Scheme.Modules.pullback f).obj L)
          ((Scheme.Modules.pullback f).obj M)).app (op (f ⁻¹ᵁ U))
          (Ringed.etaSec (φ := f.toRingCatSheafHom) l)
          (Ringed.etaSec (φ := f.toRingCatSheafHom) m)) =
      Ringed.etaSec (φ := f.toRingCatSheafHom) (E := moduleSheafTensor L M)
        ((moduleSheafTensorBilinear L M).app (op U) l m) := by
  have h := pullbackTensorMap_app_unit (f := f) l m
  have h2 := ConcreteCategory.congr_hom (congrArg (fun φ => Ringed.sectionsMap (R := X.sheaf) φ
    (f ⁻¹ᵁ U)) (@asIso X.Modules _ _ _ (pullbackTensorMap f L M) hiso).hom_inv_id)
    (Ringed.etaSec (φ := f.toRingCatSheafHom) (E := moduleSheafTensor L M)
      ((moduleSheafTensorBilinear L M).app (op U) l m))
  exact (congrArg (fun y => Ringed.sectionsMap (R := X.sheaf)
    (@asIso X.Modules _ _ _ (pullbackTensorMap f L M) hiso).inv (f ⁻¹ᵁ U) y) h.symm).trans h2

lemma pullbackDualPairing_etaSec (E : Y.Modules) {r : ℕ}
    (hE : Ringed.IsLocallyFreeOfRank (R := Y.sheaf) E r) {U : Y.Opens} (e : Γₘ(E, U))
    (σ : Γₘ(Ringed.moduleSheafDual (R := Y.sheaf) E, U)) :
    Ringed.sectionsMap (R := X.sheaf) (pullbackDualPairing f E hE) (f ⁻¹ᵁ U)
        ((moduleSheafTensorBilinear _ _).app (op (f ⁻¹ᵁ U))
          (Ringed.etaSec (φ := f.toRingCatSheafHom) e)
          (Ringed.etaSec (φ := f.toRingCatSheafHom) σ)) =
      Ringed.phiApp f.toRingCatSheafHom U (Ringed.moduleSheafHomEval σ (le_refl U) e) := by
  have hiso := pullbackTensorMap_isIso_of_isLocallyFreeOfRank f hE
    (Ringed.IsLocallyFreeOfRank.moduleSheafDual hE)
  have h1 := pullbackTensorMap_inv_etaSec f hiso e σ
  have h2 := pullback_map_etaSec f (Ringed.moduleSheafDualPairing (R := Y.sheaf) E)
    ((moduleSheafTensorBilinear E (Ringed.moduleSheafDual (R := Y.sheaf) E)).app (op U) e σ)
  have h3 := Ringed.moduleSheafDualPairing_tmul (R := Y.sheaf) E e σ
  have h4 := pullbackObjUnitToUnit_etaSec f (Ringed.moduleSheafHomEval σ (le_refl U) e)
  exact (congrArg (fun y => Ringed.sectionsMap (R := X.sheaf)
      (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) (f ⁻¹ᵁ U)
      (Ringed.sectionsMap (R := X.sheaf)
        ((Scheme.Modules.pullback f).map (Ringed.moduleSheafDualPairing (R := Y.sheaf) E))
        (f ⁻¹ᵁ U) y)) h1).trans
    ((congrArg (fun y => Ringed.sectionsMap (R := X.sheaf)
      (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) (f ⁻¹ᵁ U) y) h2).trans
    ((congrArg (fun y => Ringed.sectionsMap (R := X.sheaf)
      (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) (f ⁻¹ᵁ U)
      (Ringed.etaSec (φ := f.toRingCatSheafHom) y)) h3).trans h4))

private lemma ringHom_pi_single {ι A B : Type*} [DecidableEq ι] [Semiring A] [Semiring B]
    (φ : A →+* B) (i j : ι) :
    φ ((Pi.single i 1 : ι → A) j) = (Pi.single i 1 : ι → B) j := by
  by_cases hij : j = i
  · subst hij
    simp
  · simp [Pi.single_eq_of_ne hij]

/-- **Pullback commutes with duals of locally free sheaves of finite rank.** For a morphism of
schemes `f : X ⟶ Y` and an `𝒪_Y`-module `E` locally free of rank `r`, the comparison map
`f^*(E^∨) ⟶ (f^*E)^∨` is an isomorphism: near every point, it sends the pullback of the dual of a
frame of `E` to the dual of the pullback frame. -/
theorem pullbackDualMap_isIso (E : Y.Modules) {r : ℕ}
    (hE : Ringed.IsLocallyFreeOfRank (R := Y.sheaf) E r) : IsIso (pullbackDualMap f E hE) := by
  classical
  refine Ringed.modules_isIso_of_locally_bijective (R := X.sheaf) _ fun x => ?_
  obtain ⟨U, e, hx, he⟩ := Ringed.exists_isLocalFrame_of_isLocallyFreeOfRank hE (f.base x)
  have hsrc := Ringed.IsLocalFrame.pullback (φ := f.toRingCatSheafHom) he.dual
  have hpe := Ringed.IsLocalFrame.pullback (φ := f.toRingCatSheafHom) he
  refine ⟨f ⁻¹ᵁ U, hx, fun V hV =>
    Ringed.IsLocalFrame.app_bijective_of_map _ hsrc hpe.dual (fun i => ?_) hV⟩
  refine hpe.hom_ext (le_refl _) ?_
  have hR := hpe.localFrameEval_dualLocalFrame (le_refl _) i
  erw [Ringed.modules_map_refl] at hR
  erw [hR]
  funext j
  have hY := he.localFrameEval_dualLocalFrame (le_refl U) i
  erw [Ringed.modules_map_refl] at hY
  have hj := congrFun hY j
  erw [Ringed.localFrameEval_apply, Ringed.modules_map_refl] at hj
  erw [Ringed.localFrameEval_apply, pullbackDualMap,
    Ringed.moduleSheafTensorHomAdjunction_app_eval, Ringed.modules_map_refl,
    Ringed.modules_map_refl, pullbackDualPairing_etaSec, hj]
  exact ringHom_pi_single (Ringed.phiApp f.toRingCatSheafHom U) i j

/-- **Pullback commutes with duals of locally free sheaves of finite rank:** the canonical
isomorphism `f^*(E^∨) ≅ (f^*E)^∨`. -/
noncomputable def pullbackDualIso (E : Y.Modules) {r : ℕ}
    (hE : Ringed.IsLocallyFreeOfRank (R := Y.sheaf) E r) :
    (Scheme.Modules.pullback f).obj (Ringed.moduleSheafDual (R := Y.sheaf) E) ≅
      Ringed.moduleSheafDual (R := X.sheaf) ((Scheme.Modules.pullback f).obj E) :=
  @asIso X.Modules _ _ _ (pullbackDualMap f E hE) (pullbackDualMap_isIso f E hE)

end PullbackDual

section TangentNormal

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (p : X ⟶ Spec (.of k))
  (i : Y ⟶ X) [IsClosedImmersion i]

/-- The map `T_Y ⟶ (i^* Ω_{X/k})^∨` dual to the map `i^* Ω_{X/k} ⟶ Ω_{Y/k}` of the conormal
sequence. -/
noncomputable def tangentToPullbackDual :
    tangentSheaf (i ≫ p) ⟶
      Ringed.moduleSheafDual (R := Y.sheaf) ((Scheme.Modules.pullback i).obj
        (Scheme.relativeDifferentials p)) :=
  (Ringed.moduleSheafHomPrecomp (R := Y.sheaf) (Scheme.pullbackRelativeDifferentialsToComp i p)).app
    (Ringed.structureModule Y.sheaf)

/-- The map `(i^* Ω_{X/k})^∨ ⟶ N_{Y/X}` dual to the map `N^*_{Y/X} ⟶ i^* Ω_{X/k}` of the
conormal sequence, with `N^*_{Y/X}` identified with `i^* J`
(`Hartshorne.immersionConormalSheafIso`). -/
noncomputable def pullbackDualToNormal :
    Ringed.moduleSheafDual (R := Y.sheaf) ((Scheme.Modules.pullback i).obj
        (Scheme.relativeDifferentials p)) ⟶ normalSheaf i :=
  (Ringed.moduleSheafHomPrecomp (R := Y.sheaf) (ClosedConormal.conormalToPullback i p)).app
      (Ringed.structureModule Y.sheaf) ≫
    (Ringed.moduleSheafHomPrecomp (R := Y.sheaf) (immersionConormalSheafIso i).hom).app
      (Ringed.structureModule Y.sheaf)

lemma tangentToPullbackDual_comp_pullbackDualToNormal :
    tangentToPullbackDual p i ≫ pullbackDualToNormal p i = 0 := by
  have h := Ringed.moduleSheafHomPrecomp_g_comp_f (R := Y.sheaf)
    (S := ShortComplex.mk (ClosedConormal.conormalToPullback i p)
      (Scheme.pullbackRelativeDifferentialsToComp i p)
      (ClosedConormal.conormalToPullback_comp i p)) (Ringed.structureModule Y.sheaf)
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h).trans zero_comp)

/-- The codimension of a nonempty closed subscheme of an integral scheme of finite type over a
field is finite. -/
private theorem exists_codim_range_eq (hp : FiniteType p) [IsIntegral X] [Nonempty Y] :
    ∃ r : ℕ, codim (Set.range i.base) = r := by
  obtain ⟨y⟩ := ‹Nonempty Y›
  have := hp.1
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have hcod := codim_eq_iInf_ringKrullDim_stalk p hp
    (Set.range_nonempty_iff_nonempty.mpr ⟨y⟩) i.isClosedEmbedding.isClosed_range
  have hle : (codim (Set.range i.base) : WithBot ℕ∞) ≤
      ringKrullDim (X.presheaf.stalk (i.base y)) :=
    hcod ▸ iInf_le (fun P : Set.range i.base ↦ ringKrullDim (X.presheaf.stalk P.1))
      ⟨i.base y, y, rfl⟩
  have hne : codim (Set.range i.base) ≠ ⊤ := by
    intro htop
    rw [htop, WithBot.coe_top] at hle
    exact (lt_of_le_of_lt hle ringKrullDim_lt_top).false
  exact ⟨(codim (Set.range i.base)).toNat, (ENat.natCast_toNat hne).symm⟩

/-- **Hartshorne II.8 (p. 182), the tangent-normal sequence.** Let `X` be a nonsingular variety
over an algebraically closed field `k` and `i : Y ⟶ X` a nonsingular irreducible closed
subscheme. Dualizing the conormal sequence `0 ⟶ N^*_{Y/X} ⟶ i^* Ω_{X/k} ⟶ Ω_{Y/k} ⟶ 0`
(Theorem II.8.17) gives the short exact sequence `0 ⟶ T_Y ⟶ (i^* Ω_{X/k})^∨ ⟶ N_{Y/X} ⟶ 0`,
whose middle term is identified with Hartshorne's `T_X|_Y` by `Hartshorne.pullbackDualIso`. As in
the formalization of Theorem II.8.17, `X` is irreducible, regular and of finite type over `k`, and
`Y` is irreducible and regular; separatedness is not used. -/
theorem tangentNormal_shortExact [IsAlgClosed k] (hp : FiniteType p) [IrreducibleSpace X]
    (hX : X.IsRegular) [IrreducibleSpace Y] (hY : Y.IsRegular) :
    (ShortComplex.mk (tangentToPullbackDual p i) (pullbackDualToNormal p i)
      (tangentToPullbackDual_comp_pullbackDualToNormal p i)).ShortExact := by
  have : IsIntegral X := isIntegral_of_isRegular hX
  have : IsIntegral Y := isIntegral_of_isRegular hY
  have := hp.1
  have := hp.2
  have hp' : FiniteType (i ≫ p) := ⟨inferInstance, inferInstance⟩
  obtain ⟨r, hr⟩ := exists_codim_range_eq p i hp
  obtain ⟨n, hn, -⟩ := exists_topologicalKrullDim_eq_trdeg (i ≫ p) hp'
  -- the conormal sequence is short exact (Theorem II.8.17)
  have hS := (NonsingularConormal.nonsingular_closedImmersion_conormal p i hp hX hY r hr).1
  -- `Ω_{Y/k}` is locally free of rank `dim Y` (Theorem II.8.15)
  have hΩ := (isRegular_iff_relativeDifferentials_isLocallyFreeOfRank (i ≫ p) hp' n hn).mp hY
  rw [Scheme.Modules.isLocallyFreeOfRank_iff_ringed] at hΩ
  have hdual := Ringed.dualShortComplex_shortExact hS hΩ.isFiniteLocallyFree
  refine ShortComplex.shortExact_of_iso ?_ hdual
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    (((Ringed.moduleSheafHomBifunctor Y.sheaf).mapIso (immersionConormalSheafIso i).op).app
      (Ringed.structureModule Y.sheaf))
    (by exact (Category.id_comp _).trans (Category.comp_id _).symm)
    (by exact Category.id_comp _)

/-- **Hartshorne II.8 (p. 182), the tangent-normal sequence `0 ⟶ T_Y ⟶ T_X|_Y ⟶ N_{Y/X} ⟶ 0`.**
Let `X` be a nonsingular variety over an algebraically closed field `k` and `i : Y ⟶ X` a
nonsingular irreducible closed subscheme. Then there is a short exact sequence
`0 ⟶ T_Y ⟶ i^* T_X ⟶ N_{Y/X} ⟶ 0`. It is the dual of the conormal sequence
(`Hartshorne.tangentNormal_shortExact`), with `(i^* Ω_{X/k})^∨` identified with `i^* T_X` because
pullback commutes with duals of locally free sheaves of finite rank
(`Hartshorne.pullbackDualIso`). As in the formalization of Theorem II.8.17, `X` is irreducible,
regular and of finite type over `k`, and `Y` is irreducible and regular; separatedness is not
used. -/
theorem exists_tangentNormal_shortExact [IsAlgClosed k] (hp : FiniteType p) [IrreducibleSpace X]
    (hX : X.IsRegular) [IrreducibleSpace Y] (hY : Y.IsRegular) :
    ∃ (a : tangentSheaf (i ≫ p) ⟶ (Scheme.Modules.pullback i).obj (tangentSheaf p))
      (b : (Scheme.Modules.pullback i).obj (tangentSheaf p) ⟶ normalSheaf i) (w : a ≫ b = 0),
      (ShortComplex.mk a b w).ShortExact := by
  have : IsIntegral X := isIntegral_of_isRegular hX
  obtain ⟨n, hn, -⟩ := exists_topologicalKrullDim_eq_trdeg p hp
  have hΩ := (isRegular_iff_relativeDifferentials_isLocallyFreeOfRank p hp n hn).mp hX
  rw [Scheme.Modules.isLocallyFreeOfRank_iff_ringed] at hΩ
  let e := pullbackDualIso i (Scheme.relativeDifferentials p) hΩ
  have hS := tangentNormal_shortExact p i hp hX hY
  refine ⟨tangentToPullbackDual p i ≫ e.inv, e.hom ≫ pullbackDualToNormal p i, ?_, ?_⟩
  · exact (Category.assoc _ _ _).trans ((congrArg (tangentToPullbackDual p i ≫ ·)
      (Iso.inv_hom_id_assoc e _)).trans (tangentToPullbackDual_comp_pullbackDualToNormal p i))
  · refine ShortComplex.shortExact_of_iso ?_ hS
    exact ShortComplex.isoMk (Iso.refl _) e.symm (Iso.refl _)
      (by exact (Category.id_comp _))
      (by exact (Iso.inv_hom_id_assoc e _).trans (Category.comp_id _).symm)

/-- **Hartshorne II.8 (p. 182), the tangent-normal sequence `0 ⟶ T_Y ⟶ T_X|_Y ⟶ N_{Y/X} ⟶ 0`**,
with explicit maps: the dual of the conormal sequence (`Hartshorne.tangentNormal_shortExact`),
with `(i^* Ω_{X/k})^∨` identified with `i^* T_X` by `Hartshorne.pullbackDualIso`. The hypothesis
that `Ω_{X/k}` is locally free of finite rank follows from the others (Theorem II.8.15). -/
theorem tangentNormal_shortExact_pullback [IsAlgClosed k] (hp : FiniteType p)
    [IrreducibleSpace X] (hX : X.IsRegular) [IrreducibleSpace Y] (hY : Y.IsRegular) {n : ℕ}
    (hΩ : Ringed.IsLocallyFreeOfRank (R := X.sheaf) (Scheme.relativeDifferentials p) n) :
    (ShortComplex.mk (tangentToPullbackDual p i ≫ (pullbackDualIso i _ hΩ).inv)
      ((pullbackDualIso i _ hΩ).hom ≫ pullbackDualToNormal p i)
      ((Category.assoc _ _ _).trans ((congrArg (tangentToPullbackDual p i ≫ ·)
        (Iso.inv_hom_id_assoc _ _)).trans
          (tangentToPullbackDual_comp_pullbackDualToNormal p i)))).ShortExact := by
  refine ShortComplex.shortExact_of_iso ?_ (tangentNormal_shortExact p i hp hX hY)
  exact ShortComplex.isoMk (Iso.refl _) (pullbackDualIso i _ hΩ).symm (Iso.refl _)
    (by exact (Category.id_comp _))
    (by exact (Iso.inv_hom_id_assoc _ _).trans (Category.comp_id _).symm)

end TangentNormal

end Hartshorne

/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.RingedSpace.PicardGroup
import Hartshorne.Scheme.FiniteLocallyFreeProjectionFormula
import Hartshorne.Scheme.LocallyFreeRinged

/-!
# Pullback on Picard groups

Hartshorne, *Algebraic Geometry*, II, Exercise 6.8(a).

Let `f : X ⟶ Y` be a morphism of schemes and `f^* = Scheme.Modules.pullback f` the pullback of
module sheaves. We prove:

* `isInvertible_pullback` (and its scheme form `Scheme.Modules.IsInvertible.pullback`): `f^*`
  sends invertible sheaves to invertible sheaves;
* `pullbackTensorIso`: for invertible `L` and `M` on `Y`, the canonical map
  `f^*(L ⊗ M) ⟶ f^*L ⊗ f^*M` (`pullbackTensorMap`, adjoint to `l ⊗ m ↦ η(l) ⊗ η(m)`) is an
  isomorphism;
* `Ringed.Pic.pullback f : Pic Y →* Pic X`, the induced group homomorphism, with
  `Ringed.Pic.pullback_id` and `Ringed.Pic.pullback_comp` (functoriality);
* the compatibility with duals and with the structure sheaf: `f^*(L^∨) ≅ (f^*L)^∨` for invertible
  `L` (`nonempty_pullback_dual_iso`) and `f^*𝒪_Y ≅ 𝒪_X`
  (`nonempty_pullback_structureModule_iso`).

## Proof

Everything is local and uses frames (`IsLocalFrame`). An invertible module has frames of size one
near every point, and the pullback of a frame `e` of `E` over `U` is the frame `η(e)` of `f^*E`
over `f⁻¹U` (`IsLocalFrame.pullback`). If `a` is a frame of `A` and `b` a one-element frame of `B`
over `W`, then `a ⊗ b` is a frame of `A ⊗ B` over `W` (`IsLocalFrame.tensor`). The comparison map
sends the frame `η(l ⊗ m)` of `f^*(L ⊗ M)` to the frame `η(l) ⊗ η(m)` of `f^*L ⊗ f^*M`, so it is
bijective on all sections over opens inside `f⁻¹U`, hence an isomorphism. The compatibility with
duals and with `𝒪` then follows formally, since a monoid homomorphism between groups preserves
inverses and the identity.
-/

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Limits
open scoped TensorProduct

namespace Hartshorne

section Frames

variable {X : Scheme.{u}}

/-- A morphism of `𝒪_X`-modules carrying a frame over `W` to a frame over `W` is bijective on
sections over every open inside `W`. -/
lemma IsLocalFrame.app_bijective_of_map {ι : Type*} [Fintype ι] {A B : X.Modules} (φ : A ⟶ B)
    {W : X.Opens} {a : ι → Γ(A, W)} {b : ι → Γ(B, W)} (ha : IsLocalFrame A W a)
    (hb : IsLocalFrame B W b) (hφ : ∀ i, φ.app W (a i) = b i) {V : X.Opens} (hV : V ≤ W) :
    Function.Bijective (φ.app V) := by
  have key : ⇑(φ.app V) ∘ ⇑(localFrameMap A a hV) = ⇑(localFrameMap B b hV) := by
    funext r
    rw [Function.comp_apply, localFrameMap_apply, localFrameMap_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Scheme.Modules.Hom.app_smul, ← hφ i]
    congr 1
    exact (ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE hV).op) (a i))
  have h := hb V hV
  rw [← key] at h
  exact (Function.Bijective.of_comp_iff _ (ha V hV)).mp h

/-- **Frames of a tensor product.** If `a` is a frame of `A` over `W` and `b` is a one-element
frame of `B` over `W`, then the sections `a i ⊗ b` form a frame of `A ⊗ B` over `W`. -/
lemma IsLocalFrame.tensor {ι κ : Type*} [Fintype ι] [Fintype κ] [Unique κ] {A B : X.Modules}
    {W : X.Opens} {a : ι → Γ(A, W)} {b : κ → Γ(B, W)} (ha : IsLocalFrame A W a)
    (hb : IsLocalFrame B W b) :
    IsLocalFrame (moduleSheafTensor A B) W
      (fun i => (moduleSheafTensorBilinear A B).app (op W) (a i) (b default)) := by
  classical
  intro V hV
  have key : ⇑(localFrameMap (moduleSheafTensor A B)
      (fun i => (moduleSheafTensorBilinear A B).app (op W) (a i) (b default)) hV) =
      tensorFrameMap A b hV ∘ (Equiv.funUnique κ Γ(A, V)).symm ∘
        ⇑(localFrameMap A a hV) := by
    funext r
    refine (localFrameMap_apply _ _ _ _).trans ?_
    refine Eq.trans ?_ (Fintype.sum_unique _).symm
    refine Eq.trans ?_ (LinearMap.map_sum₂ ((moduleSheafTensorBilinear A B).app (op V)) _ _ _).symm
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Eq.trans ?_ (LinearMap.map_smul₂ ((moduleSheafTensorBilinear A B).app (op V)) _ _ _).symm
    congr 1
    exact (moduleSheafTensorBilinear A B).naturality _ _ _
  rw [key]
  exact (hb.tensorFrameMap_bijective (F := A) hV).comp
    ((Equiv.funUnique κ Γ(A, V)).symm.bijective.comp (ha V hV))

end Frames

section PullbackTensor

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Pullback of an invertible sheaf is invertible.** For a morphism of schemes `f : X ⟶ Y` and
an invertible `𝒪_Y`-module `L`, the `𝒪_X`-module `f^*L` is invertible. -/
theorem isInvertible_pullback {L : Y.Modules} (hL : Ringed.IsInvertible (R := Y.sheaf) L) :
    Ringed.IsInvertible (R := X.sheaf) ((Scheme.Modules.pullback f).obj L) := by
  classical
  refine Ringed.isLocallyFreeOfRank_of_isLocalFrame fun x => ?_
  obtain ⟨U, e, hx, he⟩ := Ringed.exists_isLocalFrame_of_isLocallyFreeOfRank hL (f.base x)
  exact ⟨f ⁻¹ᵁ U, _, hx, IsLocalFrame.pullback f (show IsLocalFrame L U e from he)⟩

/-- The morphism `L ⊗ M ⟶ f_*(f^*L ⊗ f^*M)`, `l ⊗ m ↦ η(l) ⊗ η(m)`, adjoint to the comparison
map `pullbackTensorMap`. -/
noncomputable def pullbackTensorMapAdj (L M : Y.Modules) :
    @Quiver.Hom Y.Modules _ (moduleSheafTensor L M) ((Scheme.Modules.pushforward f).obj
      (moduleSheafTensor ((Scheme.Modules.pullback f).obj L)
        ((Scheme.Modules.pullback f).obj M))) :=
  modulesTensorMap (pullbackUnit f L) (𝟙 M) ≫
    projectionFormulaMap f ((Scheme.Modules.pullback f).obj L) M

/-- The canonical comparison map `f^*(L ⊗ M) ⟶ f^*L ⊗ f^*M`, adjoint to
`l ⊗ m ↦ η(l) ⊗ η(m)`. -/
noncomputable def pullbackTensorMap (L M : Y.Modules) :
    (Scheme.Modules.pullback f).obj (moduleSheafTensor L M) ⟶
      moduleSheafTensor ((Scheme.Modules.pullback f).obj L) ((Scheme.Modules.pullback f).obj M) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm (pullbackTensorMapAdj f L M)

variable {f} in
lemma pullbackTensorMap_app_unit {L M : Y.Modules} {U : Y.Opens} (l : Γ(L, U)) (m : Γ(M, U)) :
    (pullbackTensorMap f L M).app (f ⁻¹ᵁ U)
        ((pullbackUnit f (moduleSheafTensor L M)).app U
          ((moduleSheafTensorBilinear L M).app (op U) l m)) =
      (moduleSheafTensorBilinear ((Scheme.Modules.pullback f).obj L)
        ((Scheme.Modules.pullback f).obj M)).app (op (f ⁻¹ᵁ U))
          ((pullbackUnit f L).app U l) ((pullbackUnit f M).app U m) := by
  have h : pullbackUnit f (moduleSheafTensor L M) ≫
      (Scheme.Modules.pushforward f).map (pullbackTensorMap f L M) = pullbackTensorMapAdj f L M :=
    ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_unit _ _ _).symm.trans
      (Equiv.apply_symm_apply _ _)
  have h1 : (pullbackTensorMap f L M).app (f ⁻¹ᵁ U)
      ((pullbackUnit f (moduleSheafTensor L M)).app U
        ((moduleSheafTensorBilinear L M).app (op U) l m)) =
      (pullbackTensorMapAdj f L M).app U ((moduleSheafTensorBilinear L M).app (op U) l m) :=
    ConcreteCategory.congr_hom (congrArg (fun φ => Scheme.Modules.Hom.app φ U) h)
      ((moduleSheafTensorBilinear L M).app (op U) l m)
  have h3 := modulesTensorMap_tmul (pullbackUnit f L) (𝟙 M) l m
  have h4 := projectionFormulaMap_tmul (f := f) (F := (Scheme.Modules.pullback f).obj L) (E := M)
    ((pullbackUnit f L).app U l) m
  exact h1.trans ((congrArg (fun t => (projectionFormulaMap f
    ((Scheme.Modules.pullback f).obj L) M).app U t) h3).trans h4)

/-- **Pullback commutes with tensor products of invertible sheaves.** For invertible
`𝒪_Y`-modules `L` and `M`, the comparison map `f^*(L ⊗ M) ⟶ f^*L ⊗ f^*M` is an isomorphism. -/
theorem pullbackTensorMap_isIso {L M : Y.Modules} (hL : Ringed.IsInvertible (R := Y.sheaf) L)
    (hM : Ringed.IsInvertible (R := Y.sheaf) M) : IsIso (pullbackTensorMap f L M) := by
  classical
  refine modules_isIso_of_locally_bijective _ fun x => ?_
  obtain ⟨U₁, l, hx₁, hl⟩ := Ringed.exists_isLocalFrame_of_isLocallyFreeOfRank hL (f.base x)
  obtain ⟨U₂, m, hx₂, hm⟩ := Ringed.exists_isLocalFrame_of_isLocallyFreeOfRank hM (f.base x)
  have hl' : IsLocalFrame L (U₁ ⊓ U₂) _ := hl.restrictLE inf_le_left
  have hm' : IsLocalFrame M (U₁ ⊓ U₂) _ := hm.restrictLE inf_le_right
  have hsrc := (hl'.tensor hm').pullback f
  have htgt := (hl'.pullback f).tensor (hm'.pullback f)
  exact ⟨f ⁻¹ᵁ (U₁ ⊓ U₂), ⟨hx₁, hx₂⟩, fun V hV =>
    IsLocalFrame.app_bijective_of_map _ hsrc htgt (fun _ => pullbackTensorMap_app_unit _ _) hV⟩

/-- **Pullback and tensor products.** For invertible `𝒪_Y`-modules `L` and `M`, the canonical
isomorphism `f^*(L ⊗ M) ≅ f^*L ⊗ f^*M`. -/
noncomputable def pullbackTensorIso {L M : Y.Modules} (hL : Ringed.IsInvertible (R := Y.sheaf) L)
    (hM : Ringed.IsInvertible (R := Y.sheaf) M) :
    (Scheme.Modules.pullback f).obj (moduleSheafTensor L M) ≅
      moduleSheafTensor ((Scheme.Modules.pullback f).obj L) ((Scheme.Modules.pullback f).obj M) :=
  haveI := pullbackTensorMap_isIso f hL hM
  asIso (pullbackTensorMap f L M)

end PullbackTensor

namespace Ringed.Pic

variable {X Y Z : Scheme.{u}}

/-- The group structure on the Picard group `Pic X` of a scheme, that is, of the ringed space
`(X, 𝒪_X)`; this makes the instance of the ringed-space Picard group available for `X.sheaf`. -/
noncomputable instance instCommGroupScheme (X : Scheme.{u}) : CommGroup (Pic X.sheaf) :=
  instCommGroup

/-- **Hartshorne II, Exercise 6.8(a): pullback on Picard groups.** A morphism of schemes
`f : X ⟶ Y` induces the group homomorphism `f^* : Pic Y ⟶ Pic X`, `[L] ↦ [f^*L]`. -/
noncomputable def pullback (f : X ⟶ Y) : Pic Y.sheaf →* Pic X.sheaf :=
  MonoidHom.mk'
    (Quotient.lift (s := invertibleModulesSetoid Y.sheaf)
      (fun L => mk (R := X.sheaf) ((Scheme.Modules.pullback f).obj L.1)
        (isInvertible_pullback f L.2))
      (fun _ _ ⟨α⟩ => (mk_eq_mk_iff _ _).mpr ⟨(Scheme.Modules.pullback f).mapIso α⟩))
    (fun a b => by
      obtain ⟨L, hL, rfl⟩ := mk_surjective a
      obtain ⟨M, hM, rfl⟩ := mk_surjective b
      exact (mk_eq_mk_iff _ _).mpr ⟨pullbackTensorIso f hL hM⟩)

/-- `f^*` sends the class of an invertible sheaf `L` to the class of `f^*L`. -/
lemma pullback_mk (f : X ⟶ Y) {L : Y.Modules} (hL : IsInvertible (R := Y.sheaf) L) :
    pullback f (mk L hL) = mk (R := X.sheaf) ((Scheme.Modules.pullback f).obj L)
      (isInvertible_pullback f hL) :=
  rfl

/-- **Functoriality: identities.** Pullback along the identity is the identity of `Pic X`. -/
theorem pullback_id : pullback (𝟙 X) = MonoidHom.id (Pic X.sheaf) := by
  ext c
  obtain ⟨L, hL, rfl⟩ := mk_surjective c
  exact (mk_eq_mk_iff _ _).mpr ⟨(Scheme.Modules.pullbackId X).app L⟩

/-- **Functoriality: composition.** `(f ≫ g)^* = f^* ∘ g^*` on Picard groups. -/
theorem pullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback (f ≫ g) = (pullback f).comp (pullback g) := by
  ext c
  obtain ⟨L, hL, rfl⟩ := mk_surjective c
  exact (mk_eq_mk_iff _ _).mpr ⟨((Scheme.Modules.pullbackComp f g).app L).symm⟩

end Ringed.Pic

section Compatibilities

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Pullback and duals.** For an invertible `𝒪_Y`-module `L`, `f^*(L^∨) ≅ (f^*L)^∨`. -/
theorem nonempty_pullback_dual_iso {L : Y.Modules} (hL : Ringed.IsInvertible (R := Y.sheaf) L) :
    Nonempty ((Scheme.Modules.pullback f).obj (Ringed.moduleSheafDual (R := Y.sheaf) L) ≅
      Ringed.moduleSheafDual (R := X.sheaf) ((Scheme.Modules.pullback f).obj L)) :=
  (Ringed.Pic.mk_eq_mk_iff (isInvertible_pullback f (Ringed.isInvertible_moduleSheafDual hL))
    (Ringed.isInvertible_moduleSheafDual (isInvertible_pullback f hL))).mp
    (map_inv (Ringed.Pic.pullback f) (Ringed.Pic.mk L hL))

/-- **Pullback of the structure sheaf.** `f^*𝒪_Y ≅ 𝒪_X`. -/
theorem nonempty_pullback_structureModule_iso :
    Nonempty ((Scheme.Modules.pullback f).obj (Ringed.structureModule Y.sheaf) ≅
      Ringed.structureModule X.sheaf) :=
  (Ringed.Pic.mk_eq_mk_iff (isInvertible_pullback f Ringed.structureModule_isInvertible)
    Ringed.structureModule_isInvertible).mp (map_one (Ringed.Pic.pullback f))

end Compatibilities

end Hartshorne

namespace AlgebraicGeometry.Scheme.Modules

/-- **Pullback of an invertible sheaf is invertible** (scheme form). For a morphism of schemes
`f : X ⟶ Y` and an invertible `𝒪_Y`-module `L`, the `𝒪_X`-module `f^*L` is invertible. -/
theorem IsInvertible.pullback {X Y : Scheme.{u}} (f : X ⟶ Y) {L : Y.Modules}
    (hL : L.IsInvertible) : ((Scheme.Modules.pullback f).obj L).IsInvertible :=
  (isInvertible_iff_ringed _).mpr
    (Hartshorne.isInvertible_pullback f ((isInvertible_iff_ringed L).mp hL))

end AlgebraicGeometry.Scheme.Modules

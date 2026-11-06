/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.FiniteLocallyFreeTensorInjective

/-!
# The Picard group

Hartshorne, *Algebraic Geometry*, II, Proposition 6.12 and the definition of `Pic X` (p. 143).

Let `X` be a scheme (the setting of the module-sheaf tensor product, sheaf `ℋom` and the
invertibility predicate this file builds on). We prove:

* **Proposition 6.12.** If `L` and `M` are invertible `𝒪_X`-modules, so is `L ⊗ M`
  (`isInvertible_moduleSheafTensor`); and for invertible `L` the evaluation map
  `L ⊗ L^∨ ⟶ 𝒪_X`, `l ⊗ ψ ↦ ψ(l)` (`moduleSheafDualEval`), is an isomorphism
  (`moduleSheafDualEval_isIso`, `moduleSheafDualEvalIso`). The dual `L^∨ = ℋom(L, 𝒪_X)` of an
  invertible sheaf is invertible (`isInvertible_moduleSheafDual`), and so is `𝒪_X`
  (`structureModule_isInvertible`).
* **The Picard group.** `Scheme.Pic X` is the type of isomorphism classes of invertible
  `𝒪_X`-modules; it is a commutative group with multiplication induced by `⊗`
  (`Scheme.Pic.mk_mul_mk`), identity the class of `𝒪_X` (`Scheme.Pic.one_eq_mk`) and inverse the
  class of the dual (`Scheme.Pic.inv_mk`).

A group of isomorphism classes needs no coherence data, only the existence of isomorphisms
`(L ⊗ M) ⊗ N ≅ L ⊗ (M ⊗ N)` (`moduleSheafTensorAssoc`), `𝒪_X ⊗ F ≅ F` (`moduleSheafUnitTensor`),
`E ⊗ F ≅ F ⊗ E` (`moduleSheafTensorComm`), and the compatibility of `⊗` and of duals with
isomorphisms (`moduleSheafTensorIsoOfIso`, `moduleSheafDualIsoOfIso`). These all come from the
universal property of the tensor product. For associativity, morphisms out of `(A ⊗ B) ⊗ C` are
built from trilinear maps on sections (`ModuleSheafTrilinear.tensorDesc`) by currying the last
variable into `ℋom(C, H)`, and are determined by their values on elementary tensors
(`moduleSheafTensor_assoc_hom_ext`).

The local statements use local frames (`IsLocalFrame`): a frame of `E` over `U` indexed by `I`
makes `E|_U` free on `I` (`nonempty_restrict_iso_free_of_isLocalFrame`), so a module with frames of
size `r` around every point is locally free of rank `r` (`isLocallyFreeOfRank_of_isLocalFrame`).
Frames of `A` and `G` give a frame of `ℋom(A, G)` (`IsLocalFrame.homFrame`), and for invertible `L`
there is a global isomorphism `L ⊗ M ≅ ℋom(L^∨, M)` (`tensorIsoHomDual`, from the double-dual and
dual-tensor isomorphisms), which gives the invertibility of `L ⊗ M`. The evaluation map is an
isomorphism because on every open inside a rank-one frame the presheaf-level pairing
`L(V) ⊗ L^∨(V) → 𝒪_X(V)` is bijective, and sheafification does not change stalks.
-/

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Limits
open scoped TensorProduct

namespace Hartshorne

variable {X : Scheme.{u}}

section Helpers

private lemma pic_map_map (A : X.Modules) {U V W : X.Opens} (i : V ≤ U) (j : W ≤ V)
    (x : Γ(A, U)) :
    A.presheaf.map (homOfLE j).op (A.presheaf.map (homOfLE i).op x) =
      A.presheaf.map (homOfLE (j.trans i)).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

private lemma pic_map_id (A : X.Modules) {U : X.Opens} (x : Γ(A, U)) :
    A.presheaf.map (homOfLE (le_refl U)).op x = x := by
  rw [show (homOfLE (le_refl U)) = 𝟙 U from rfl, op_id, CategoryTheory.Functor.map_id]
  rfl

private lemma pic_ring_map_id {U : X.Opens} (r : Γ(X, U)) :
    X.presheaf.map (homOfLE (le_refl U)).op r = r := by
  rw [show (homOfLE (le_refl U)) = 𝟙 U from rfl, op_id, CategoryTheory.Functor.map_id]
  rfl

private lemma pic_hom_naturality {A B : X.Modules} (φ : A ⟶ B) {U V : X.Opens} (h : V ≤ U)
    (x : Γ(A, U)) :
    φ.app V (A.presheaf.map (homOfLE h).op x) = B.presheaf.map (homOfLE h).op (φ.app U x) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE h).op) x

end Helpers

section TensorIsos

/-- The morphism out of a tensor product attached to a bilinear map sends `e ⊗ f` to `β(e, f)`. -/
lemma moduleSheafTensorHomEquiv_symm_tmul {E F H : X.Modules} (β : ModuleSheafBilinear E F H)
    {U : X.Opens} (e : Γ(E, U)) (f : Γ(F, U)) :
    Scheme.Modules.Hom.app ((moduleSheafTensorHomEquiv E F H).symm β) U
        ((moduleSheafTensorBilinear E F).app (op U) e f) = β.app (op U) e f := by
  have := congrArg (fun γ : ModuleSheafBilinear _ _ _ => γ.app (op U) e f)
    ((moduleSheafTensorHomEquiv_apply ((moduleSheafTensorHomEquiv E F H).symm β)).symm.trans
      (Equiv.apply_symm_apply (moduleSheafTensorHomEquiv _ _ _) β))
  exact this

/-- Tensor products of isomorphic modules are isomorphic. -/
noncomputable def moduleSheafTensorIsoOfIso {E E' F F' : X.Modules} (α : E ≅ E') (β : F ≅ F') :
    @Iso X.Modules _ (moduleSheafTensor E F) (moduleSheafTensor E' F') where
  hom := modulesTensorMap α.hom β.hom
  inv := modulesTensorMap α.inv β.inv
  hom_inv_id := by
    rw [← modulesTensorMap_comp, α.hom_inv_id, β.hom_inv_id, modulesTensorMap_id]
    rfl
  inv_hom_id := by
    rw [← modulesTensorMap_comp, α.inv_hom_id, β.inv_hom_id, modulesTensorMap_id]
    rfl

/-- The bilinear map `(e, f) ↦ f ⊗ e`. -/
noncomputable def tensorFlipBilinear (E F : X.Modules) :
    ModuleSheafBilinear E F (moduleSheafTensor F E) where
  app U := ((moduleSheafTensorBilinear F E).app U).flip
  naturality i e f := (moduleSheafTensorBilinear F E).naturality i f e

/-- The symmetry map `E ⊗ F ⟶ F ⊗ E`, `e ⊗ f ↦ f ⊗ e`. -/
noncomputable def moduleSheafTensorFlip (E F : X.Modules) :
    @Quiver.Hom X.Modules _ (moduleSheafTensor E F) (moduleSheafTensor F E) :=
  (moduleSheafTensorHomEquiv _ _ _).symm (tensorFlipBilinear E F)

/-- The symmetry map sends `e ⊗ f` to `f ⊗ e`. -/
lemma moduleSheafTensorFlip_tmul (E F : X.Modules) {U : X.Opens} (e : Γ(E, U)) (f : Γ(F, U)) :
    (moduleSheafTensorFlip E F).app U ((moduleSheafTensorBilinear E F).app (op U) e f) =
      (moduleSheafTensorBilinear F E).app (op U) f e :=
  moduleSheafTensorHomEquiv_symm_tmul _ e f

/-- **Commutativity of the tensor product:** `E ⊗ F ≅ F ⊗ E`. -/
noncomputable def moduleSheafTensorComm (E F : X.Modules) :
    @Iso X.Modules _ (moduleSheafTensor E F) (moduleSheafTensor F E) where
  hom := moduleSheafTensorFlip E F
  inv := moduleSheafTensorFlip F E
  hom_inv_id := by
    refine modulesTensor_hom_ext fun U e f => ?_
    change (moduleSheafTensorFlip F E).app U ((moduleSheafTensorFlip E F).app U _) = _
    rw [moduleSheafTensorFlip_tmul, moduleSheafTensorFlip_tmul]
    rfl
  inv_hom_id := by
    refine modulesTensor_hom_ext fun U e f => ?_
    change (moduleSheafTensorFlip E F).app U ((moduleSheafTensorFlip F E).app U _) = _
    rw [moduleSheafTensorFlip_tmul, moduleSheafTensorFlip_tmul]
    rfl

/-- The bilinear map `(r, f) ↦ r f` from `𝒪_X × F` to `F`. -/
noncomputable def unitSMulBilinear (F : X.Modules) :
    ModuleSheafBilinear (structureModule X) F F where
  app U := LinearMap.lsmul Γ(X, U.unop) Γ(F, U.unop)
  naturality i r f := Scheme.Modules.map_smul F i.unop r f

/-- The map `F ⟶ 𝒪_X ⊗ F`, `f ↦ 1 ⊗ f`. -/
noncomputable def unitTensorInv (F : X.Modules) :
    F ⟶ moduleSheafTensor (structureModule X) F :=
  modulesHomMk (fun U => ((moduleSheafTensorBilinear (structureModule X) F).app (op U))
      (show Γ(structureModule X, U) from (1 : Γ(X, U))))
    (fun U V i f => by
      change (moduleSheafTensorBilinear (structureModule X) F).app (op V)
          (show Γ(structureModule X, V) from (1 : Γ(X, V))) (F.presheaf.map (homOfLE i).op f) =
        (moduleSheafTensor (structureModule X) F).val.map (homOfLE i).op
          ((moduleSheafTensorBilinear (structureModule X) F).app (op U)
            (show Γ(structureModule X, U) from (1 : Γ(X, U))) f)
      refine Eq.trans ?_ ((moduleSheafTensorBilinear (structureModule X) F).naturality
        (homOfLE i).op _ f).symm
      congr 1
      exact congrArg _ (map_one (X.presheaf.map (homOfLE i).op).hom).symm)

/-- **The structure sheaf is a unit for the tensor product:** `𝒪_X ⊗ F ≅ F`. -/
noncomputable def moduleSheafUnitTensor (F : X.Modules) :
    @Iso X.Modules _ (moduleSheafTensor (structureModule X) F) F where
  hom := (moduleSheafTensorHomEquiv _ _ _).symm (unitSMulBilinear F)
  inv := unitTensorInv F
  hom_inv_id := by
    refine modulesTensor_hom_ext fun U r f => ?_
    change (unitTensorInv F).app U (Scheme.Modules.Hom.app ((moduleSheafTensorHomEquiv _ _ _).symm
      (unitSMulBilinear F)) U _) = _
    rw [moduleSheafTensorHomEquiv_symm_tmul]
    change (moduleSheafTensorBilinear (structureModule X) F).app (op U)
        (show Γ(structureModule X, U) from (1 : Γ(X, U))) ((show Γ(X, U) from r) • f) = _
    erw [LinearMap.map_smul, ← LinearMap.map_smul₂]
    exact congrArg (fun a => (moduleSheafTensorBilinear (structureModule X) F).app (op U) a f)
      (mul_one (show Γ(X, U) from r))
  inv_hom_id := by
    refine Scheme.Modules.hom_ext _ _ fun U => ?_
    ext f
    change Scheme.Modules.Hom.app ((moduleSheafTensorHomEquiv _ _ _).symm (unitSMulBilinear F)) U
      ((moduleSheafTensorBilinear (structureModule X) F).app (op U)
        (show Γ(structureModule X, U) from (1 : Γ(X, U))) f) = f
    rw [moduleSheafTensorHomEquiv_symm_tmul]
    exact one_smul _ f

end TensorIsos

section Frames

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- A frame over `U` restricts to a frame over any smaller open. -/
lemma IsLocalFrame.restrictLE {A : X.Modules} {U V : X.Opens} {e : ι → Γ(A, U)}
    (hA : IsLocalFrame A U e) (hVU : V ≤ U) :
    IsLocalFrame A V (fun i => A.presheaf.map (homOfLE hVU).op (e i)) := by
  intro W hW
  have key : ⇑(localFrameMap A (fun i => A.presheaf.map (homOfLE hVU).op (e i)) hW) =
      ⇑(localFrameMap A e (hW.trans hVU)) := by
    funext a
    rw [localFrameMap_apply, localFrameMap_apply]
    simp_rw [pic_map_map]
  rw [key]
  exact hA W _

/-- A frame reindexed along an equivalence of index types. -/
lemma IsLocalFrame.reindex {A : X.Modules} {U : X.Opens} {e : ι → Γ(A, U)}
    (hA : IsLocalFrame A U e) (σ : κ ≃ ι) : IsLocalFrame A U (e ∘ σ) := by
  intro V h
  have key : ⇑(localFrameMap A (e ∘ σ) h) =
      ⇑(localFrameMap A e h) ∘ ⇑(σ.arrowCongr (Equiv.refl Γ(X, V))) := by
    funext a
    rw [Function.comp_apply, localFrameMap_apply, localFrameMap_apply]
    exact Fintype.sum_equiv σ _ _ (fun k => by simp)
  rw [key]
  exact (hA V h).comp (σ.arrowCongr (Equiv.refl Γ(X, V))).bijective

/-- A module locally free of rank `r` has frames indexed by `Fin r` near every point. -/
lemma exists_isLocalFrame_of_isLocallyFreeOfRank {E : X.Modules} {r : ℕ}
    (hE : E.IsLocallyFreeOfRank r) (x : X) :
    ∃ (U : X.Opens) (e : ULift.{u} (Fin r) → Γ(E, U)), x ∈ U ∧ IsLocalFrame E U e := by
  obtain ⟨U, hxU, ⟨α⟩⟩ := hE x
  exact ⟨U, _, hxU,
    ((free_isLocalFrame (Y := U.toScheme) (I := ULift.{u} (Fin r))).of_iso α.symm).of_restrict⟩

/-- The morphism `𝒪_X ⟶ A`, `r ↦ r s`, attached to a global section `s` of `A`. -/
noncomputable def unitHomOfSection {A : X.Modules} (s : Γ(A, ⊤)) : structureModule X ⟶ A :=
  modulesHomMk
    (fun V => LinearMap.toSpanSingleton Γ(X, V) Γ(A, V) (A.presheaf.map (homOfLE le_top).op s))
    (fun U V i r => by
      change X.presheaf.map (homOfLE i).op r • A.presheaf.map (homOfLE le_top).op s =
        A.presheaf.map (homOfLE i).op ((show Γ(X, U) from r) • A.presheaf.map (homOfLE le_top).op s)
      rw [Scheme.Modules.map_smul, pic_map_map])

/-- The morphism `unitHomOfSection s` sends `1` to `s`. -/
lemma unitHomOfSection_app_one {A : X.Modules} (s : Γ(A, ⊤)) :
    (unitHomOfSection s).app ⊤ (show Γ(structureModule X, ⊤) from (1 : Γ(X, ⊤))) = s := by
  change (1 : Γ(X, ⊤)) • A.presheaf.map (homOfLE le_top).op s = s
  rw [one_smul]
  exact pic_map_id A s

/-- The morphism `𝒪_X^{⊕ I} ⟶ A` sending the `i`-th basis vector to `s i`. -/
noncomputable def freeDescOfSections {I : Type u} {A : X.Modules} (s : I → Γ(A, ⊤)) :
    freeModule X I ⟶ A :=
  Cofan.IsColimit.desc (SheafOfModules.isColimitFreeCofan I) fun i => unitHomOfSection (s i)

/-- The morphism `freeDescOfSections s` sends the `i`-th basis vector to `s i`. -/
lemma freeDescOfSections_app {I : Type u} {A : X.Modules} (s : I → Γ(A, ⊤)) (i : I) :
    (freeDescOfSections s).app ⊤ ((freeIncl (Y := X) i).app ⊤ (1 : Γ(X, ⊤))) = s i := by
  have h : freeIncl (Y := X) i ≫ freeDescOfSections s = unitHomOfSection (s i) :=
    Cofan.IsColimit.fac (SheafOfModules.isColimitFreeCofan I) _ i
  have := congrArg (fun φ : structureModule X ⟶ A =>
    φ.app ⊤ (show Γ(structureModule X, ⊤) from (1 : Γ(X, ⊤)))) h
  exact this.trans (unitHomOfSection_app_one _)

/-- A morphism sending a frame over `⊤` to a frame over `⊤` is an isomorphism. -/
lemma isIso_of_isLocalFrame_top {A B : X.Modules} (φ : B ⟶ A) {b : ι → Γ(B, ⊤)}
    {a : ι → Γ(A, ⊤)} (hB : IsLocalFrame B ⊤ b) (hA : IsLocalFrame A ⊤ a)
    (hφ : ∀ i, φ.app ⊤ (b i) = a i) : IsIso φ :=
  modules_isIso_of_locally_bijective φ fun _ => ⟨⊤, by simp, fun V _ => by
    have key : ⇑(φ.app V) ∘ ⇑(localFrameMap B b (le_top : V ≤ ⊤)) =
        ⇑(localFrameMap A a (le_top : V ≤ ⊤)) := by
      funext c
      rw [Function.comp_apply, localFrameMap_apply, localFrameMap_apply, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Scheme.Modules.Hom.app_smul, pic_hom_naturality, hφ]
    have h2 := hA V le_top
    rw [← key] at h2
    exact (Function.Bijective.of_comp_iff _ (hB V le_top)).mp h2⟩

private lemma pic_restrict_localFrameMap_eq (E : X.Modules) (U : X.Opens) (W : U.toScheme.Opens)
    (e : ι → Γ(E.restrict U.ι, ⊤)) (a : ι → Γ(X, U.ι ''ᵁ W)) :
    (Scheme.Modules.restrictAppIso U.ι E W).hom
        (localFrameMap (E.restrict U.ι) e (le_top : W ≤ ⊤) (fun i => (U.ι.appIso W).hom (a i))) =
      localFrameMap E (fun i => E.presheaf.map (homOfLE U.ι_image_top.ge).op
        ((Scheme.Modules.restrictAppIso U.ι E ⊤).hom (e i))) (U.ι_image_le W) a := by
  rw [localFrameMap_apply, localFrameMap_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Scheme.Modules.smul_restrictAppIso_hom_apply, Scheme.Modules.map_restrictAppIso_hom_apply,
    pic_map_map, Iso.hom_inv_id_apply]

/-- A frame of `E` over `U` gives a frame of the restriction `E|_U` over all of `U`. -/
lemma IsLocalFrame.toRestrict {E : X.Modules} {U : X.Opens} {e : ι → Γ(E, U)}
    (h : IsLocalFrame E U e) :
    IsLocalFrame (E.restrict U.ι) ⊤ (fun i => (Scheme.Modules.restrictAppIso U.ι E ⊤).inv
      (E.presheaf.map (homOfLE U.ι_image_top.le).op (e i))) := by
  intro W _
  have hfam : (fun i => E.presheaf.map (homOfLE U.ι_image_top.ge).op
      ((Scheme.Modules.restrictAppIso U.ι E ⊤).hom ((Scheme.Modules.restrictAppIso U.ι E ⊤).inv
        (E.presheaf.map (homOfLE U.ι_image_top.le).op (e i))))) = e := by
    funext i
    rw [Iso.inv_hom_id_apply, pic_map_map]
    exact pic_map_id E (e i)
  have key : ⇑(Scheme.Modules.restrictAppIso U.ι E W).hom ∘
      ⇑(localFrameMap (E.restrict U.ι) (fun i => (Scheme.Modules.restrictAppIso U.ι E ⊤).inv
        (E.presheaf.map (homOfLE U.ι_image_top.le).op (e i))) (le_top : W ≤ ⊤)) ∘
      (fun a : ι → Γ(X, U.ι ''ᵁ W) => fun i => (U.ι.appIso W).hom (a i)) =
      ⇑(localFrameMap E e (U.ι_image_le W)) := by
    funext a
    exact (pic_restrict_localFrameMap_eq E U W _ a).trans
      (congrArg (fun f => localFrameMap E f (U.ι_image_le W) a) hfam)
  have h1 := h _ (U.ι_image_le W)
  rw [← key] at h1
  have h2 := (Function.Bijective.of_comp_iff' (ConcreteCategory.bijective_of_isIso _) _).mp h1
  exact (Function.Bijective.of_comp_iff _
    (ConcreteCategory.bijective_of_isIso (U.ι.appIso W).hom).comp_left).mp h2

/-- A frame of `E` over `U` indexed by `I` makes `E|_U` free on `I`. -/
lemma nonempty_restrict_iso_free_of_isLocalFrame {I : Type u} [Fintype I] [DecidableEq I]
    {E : X.Modules} {U : X.Opens} {e : I → Γ(E, U)} (h : IsLocalFrame E U e) :
    Nonempty (E.restrict U.ι ≅ SheafOfModules.free I) := by
  let φ : freeModule U.toScheme I ⟶ E.restrict U.ι :=
    freeDescOfSections (fun i => (Scheme.Modules.restrictAppIso U.ι E ⊤).inv
      (E.presheaf.map (homOfLE U.ι_image_top.le).op (e i)))
  have : IsIso φ := isIso_of_isLocalFrame_top φ free_isLocalFrame h.toRestrict
    (freeDescOfSections_app _)
  exact ⟨(asIso φ).symm⟩

/-- A module with frames indexed by `Fin r` near every point is locally free of rank `r`. -/
lemma isLocallyFreeOfRank_of_isLocalFrame {E : X.Modules} {r : ℕ}
    (h : ∀ x : X, ∃ (U : X.Opens) (e : ULift.{u} (Fin r) → Γ(E, U)), x ∈ U ∧ IsLocalFrame E U e) :
    E.IsLocallyFreeOfRank r := fun x => by
  obtain ⟨U, e, hx, he⟩ := h x
  exact ⟨U, hx, nonempty_restrict_iso_free_of_isLocalFrame he⟩

/-- The unit section is a frame of the structure sheaf. -/
lemma structureModule_isLocalFrame :
    IsLocalFrame (structureModule X) ⊤
      (fun _ : ULift.{u} (Fin 1) => show Γ(structureModule X, ⊤) from (1 : Γ(X, ⊤))) := by
  intro V h
  have key : ⇑(localFrameMap (structureModule X)
      (fun _ : ULift.{u} (Fin 1) => show Γ(structureModule X, ⊤) from (1 : Γ(X, ⊤))) h) =
      ⇑(Equiv.funUnique (ULift.{u} (Fin 1)) Γ(X, V)) := by
    funext a
    rw [localFrameMap_apply, Fintype.sum_unique]
    change a default * X.presheaf.map (homOfLE h).op 1 = a default
    rw [map_one, mul_one]
  rw [key]
  exact (Equiv.funUnique (ULift.{u} (Fin 1)) Γ(X, V)).bijective

/-- The structure sheaf is invertible. -/
theorem structureModule_isInvertible : (structureModule X).IsInvertible :=
  isLocallyFreeOfRank_of_isLocalFrame fun _ => ⟨⊤, _, by simp, structureModule_isLocalFrame⟩

/-- **The dual of an invertible sheaf is invertible.** -/
theorem isInvertible_moduleSheafDual {L : X.Modules} (hL : L.IsInvertible) :
    (moduleSheafDual L).IsInvertible :=
  isLocallyFreeOfRank_of_isLocalFrame fun x => by
    obtain ⟨U, e, hx, he⟩ := exists_isLocalFrame_of_isLocallyFreeOfRank hL x
    exact ⟨U, _, hx, he.dual⟩

/-- The restriction to `V` of the local morphism with values `g` on a frame takes the values
`g|_V` on the restricted frame. -/
lemma IsLocalFrame.localFrameEval_restrict_homOfValues [DecidableEq ι] {A G : X.Modules}
    {U : X.Opens} {e : ι → Γ(A, U)} (hA : IsLocalFrame A U e) (g : ι → Γ(G, U)) {V : X.Opens}
    (h : V ≤ U) :
    localFrameEval e h ((moduleSheafHom A G).presheaf.map (homOfLE h).op
        (hA.homOfValues (le_refl U) g)) = fun j => G.presheaf.map (homOfLE h).op (g j) := by
  funext j
  rw [localFrameEval_apply, moduleSheafHomEval_restrict, IsLocalFrame.homOfValues_eval,
    hA.coord_self, Finset.sum_eq_single j (fun i _ hij => by rw [Pi.single_eq_of_ne hij, zero_smul])
      (fun hj => absurd (Finset.mem_univ j) hj), Pi.single_eq_same, one_smul]

/-- Frames of `A` and `G` over `U` give a frame of `ℋom(A, G)` over `U`. -/
lemma IsLocalFrame.homFrame [DecidableEq ι] {A G : X.Modules} {U : X.Opens} {e : ι → Γ(A, U)}
    {f : κ → Γ(G, U)} (hA : IsLocalFrame A U e) (hG : IsLocalFrame G U f) :
    IsLocalFrame (moduleSheafHom A G) U
      (fun p : ι × κ => hA.homOfValues (le_refl U) (Pi.single p.1 (f p.2))) := by
  intro V h
  rw [← Function.Bijective.of_comp_iff' (hA.localFrameEval_bijective (G := G) h)]
  have key : ⇑(localFrameEval (G := G) e h) ∘ ⇑(localFrameMap (moduleSheafHom A G)
      (fun p : ι × κ => hA.homOfValues (le_refl U) (Pi.single p.1 (f p.2))) h) =
      ⇑((Equiv.curry ι κ Γ(X, V)).trans
        (Equiv.piCongrRight fun _ => (LinearEquiv.ofBijective _ (hG V h)).toEquiv)) := by
    funext c i
    rw [Function.comp_apply, localFrameMap_apply, map_sum, Finset.sum_apply]
    simp_rw [map_smul, Pi.smul_apply, hA.localFrameEval_restrict_homOfValues]
    change _ = localFrameMap G f h (fun k => c (i, k))
    rw [localFrameMap_apply, Fintype.sum_prod_type, Finset.sum_eq_single i]
    · simp
    · intro a _ hai
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [Pi.single_eq_of_ne (Ne.symm hai), map_zero, smul_zero]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  rw [key]
  exact Equiv.bijective _

end Frames

section TensorInvertible

private lemma pic_isLocallyFree_and_finite {E : X.Modules} (hE : E.IsInvertible) :
    E.IsLocallyFree ∧ ∀ x, E.rankAt x < Cardinal.aleph0 := by
  obtain ⟨h1, h2⟩ := (E.isLocallyFreeOfRank_iff 1).mp hE
  exact ⟨h1, fun x => by rw [h2 x]; exact Cardinal.natCast_lt_aleph0⟩

/-- For an invertible `L`, `L ⊗ M ≅ ℋom(L^∨, M)`. -/
noncomputable def tensorIsoHomDual {L : X.Modules} (hL : L.IsInvertible) (M : X.Modules) :
    @Iso X.Modules _ (moduleSheafTensor L M) (moduleSheafHom (moduleSheafDual L) M) :=
  moduleSheafTensorIsoOfIso
      (moduleSheafDoubleDualIso L (pic_isLocallyFree_and_finite hL).1
        (pic_isLocallyFree_and_finite hL).2) (Iso.refl M) ≪≫
    moduleSheafDualTensorIso (moduleSheafDual L) M
      (pic_isLocallyFree_and_finite (isInvertible_moduleSheafDual hL)).1
      (pic_isLocallyFree_and_finite (isInvertible_moduleSheafDual hL)).2

/-- **Hartshorne II, Proposition 6.12 (first part).** The tensor product of two invertible
sheaves is invertible. -/
theorem isInvertible_moduleSheafTensor {L M : X.Modules} (hL : L.IsInvertible)
    (hM : M.IsInvertible) : Scheme.Modules.IsInvertible (moduleSheafTensor L M) := by
  refine isLocallyFreeOfRank_of_isLocalFrame fun x => ?_
  obtain ⟨U₁, e, hx₁, he⟩ := exists_isLocalFrame_of_isLocallyFreeOfRank hL x
  obtain ⟨U₂, f, hx₂, hf⟩ := exists_isLocalFrame_of_isLocallyFreeOfRank hM x
  have hd := (he.restrictLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).dual
  have hf' := hf.restrictLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)
  exact ⟨U₁ ⊓ U₂, _, ⟨hx₁, hx₂⟩, ((hd.homFrame hf').of_iso (tensorIsoHomDual hL M).symm).reindex
    (Equiv.prodUnique (ULift.{u} (Fin 1)) (ULift.{u} (Fin 1))).symm⟩

end TensorInvertible

section Evaluation

private lemma pic_stalk_bijective {Y : TopCat.{u}} {P Q : TopCat.Presheaf AddCommGrpCat.{u} Y}
    (p : P ⟶ Q) {x : Y} {U : Opens Y} (hx : x ∈ U)
    (hp : ∀ V : Opens Y, V ≤ U → Function.Bijective (p.app (op V))) :
    Function.Bijective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map p) := by
  constructor
  · intro s t hst
    obtain ⟨V, hVU, hxV, s, rfl⟩ := P.exists_le_germ_eq s hx
    obtain ⟨V', hV'U, hxV', t, rfl⟩ := P.exists_le_germ_eq t hx
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
      TopCat.Presheaf.stalkFunctor_map_germ_apply] at hst
    obtain ⟨W, hxW, iV, iV', heq⟩ := Q.germ_eq x hxV hxV' _ _ hst
    have hWU : W ≤ U := (leOfHom iV).trans hVU
    have e : ∀ {V₁ V₂ : Opens Y} (i : V₂ ⟶ V₁) (a : ToType (P.obj (op V₁))),
        Q.map i.op (p.app (op V₁) a) = p.app (op V₂) (P.map i.op a) := fun i a => by
      rw [← ConcreteCategory.comp_apply, ← p.naturality, ConcreteCategory.comp_apply]
    rw [e, e] at heq
    have := (hp W hWU).1 heq
    rw [← TopCat.Presheaf.germ_res_apply P iV x hxW,
      ← TopCat.Presheaf.germ_res_apply P iV' x hxW, this]
  · intro t
    obtain ⟨V, hVU, hxV, t, rfl⟩ := Q.exists_le_germ_eq t hx
    obtain ⟨s, rfl⟩ := (hp V hVU).2 t
    exact ⟨P.germ V x hxV s, TopCat.Presheaf.stalkFunctor_map_germ_apply _ _ _ _ _⟩

variable (L : X.Modules)

/-- The evaluation pairing `L × L^∨ → 𝒪_X`, `(l, ψ) ↦ ψ(l)`. -/
noncomputable def dualEvalBilinear :
    ModuleSheafBilinear L (moduleSheafDual L) (structureModule X) where
  app U := LinearMap.mk₂ _
    (fun (l : Γ(L, U.unop)) (ψ : Γ(moduleSheafDual L, U.unop)) => dualEval ψ (le_refl U.unop) l)
    (fun l l' ψ => map_add _ l l')
    (fun r l ψ => map_smul _ r l)
    (fun l ψ ψ' => rfl)
    (fun r l ψ => by
      change moduleSheafHomEval (r • ψ) (le_refl U.unop) l =
        (show Γ(X, U.unop) from r) *
          (show Γ(X, U.unop) from moduleSheafHomEval ψ (le_refl U.unop) l)
      erw [moduleSheafHomEval_smul, pic_ring_map_id]
      rfl)
  naturality {U V} i l ψ :=
    (moduleSheafHomEval_natural ψ (le_refl U.unop) (leOfHom i.unop) l).symm

/-- **The evaluation map** `L ⊗ L^∨ ⟶ 𝒪_X`, `l ⊗ ψ ↦ ψ(l)`. -/
noncomputable def moduleSheafDualEval :
    @Quiver.Hom X.Modules _ (moduleSheafTensor L (moduleSheafDual L)) (structureModule X) :=
  (moduleSheafTensorHomEquiv _ _ _).symm (dualEvalBilinear L)

/-- The evaluation map sends `l ⊗ ψ` to `ψ(l)`. -/
lemma moduleSheafDualEval_tmul {U : X.Opens} (l : Γ(L, U)) (ψ : Γ(moduleSheafDual L, U)) :
    (moduleSheafDualEval L).app U ((moduleSheafTensorBilinear L (moduleSheafDual L)).app (op U) l ψ) =
      dualEval ψ (le_refl U) l :=
  moduleSheafTensorHomEquiv_symm_tmul _ l ψ

/-- The presheaf-level map `U ↦ L(U) ⊗ L^∨(U) → 𝒪_X(U)` underlying the evaluation map. -/
noncomputable abbrev dualEvalPresheafMap :
    (moduleSheafTensorPresheaf L (moduleSheafDual L)).presheaf ⟶ (structureModule X).presheaf :=
  (PresheafOfModules.toPresheaf _).map
    (moduleSheafTensorUnit L (moduleSheafDual L) ≫ (moduleSheafDualEval L).val)

variable {L}

/-- The presheaf-level evaluation map sends `l ⊗ ψ` to `ψ(l)`. -/
lemma dualEvalPresheafMap_tmul {V : X.Opens} (l : Γ(L, V)) (ψ : Γ(moduleSheafDual L, V)) :
    (dualEvalPresheafMap L).app (op V)
        (show (moduleSheafTensorPresheaf L (moduleSheafDual L)).obj (op V) from l ⊗ₜ ψ) =
      dualEval ψ (le_refl V) l :=
  moduleSheafDualEval_tmul L l ψ

/-- On every open inside a rank-one frame of `L`, the pairing `L(V) ⊗ L^∨(V) → 𝒪_X(V)` is
bijective. -/
lemma dualEvalPresheafMap_bijective {ι : Type*} [Fintype ι] [Unique ι]
    {U : X.Opens} {e : ι → Γ(L, U)} (hL : IsLocalFrame L U e) {V : X.Opens} (h : V ≤ U) :
    Function.Bijective ((dualEvalPresheafMap L).app (op V)) := by
  let c : Γ(L, V) ≃ₗ[Γ(X, V)] Γ(X, V) :=
    (hL.coord h).trans (LinearEquiv.funUnique ι Γ(X, V) Γ(X, V))
  let d : Γ(moduleSheafDual L, V) ≃ₗ[Γ(X, V)] Γ(X, V) :=
    (LinearEquiv.ofBijective (localFrameEval (G := structureModule X) e h)
      (hL.localFrameEval_bijective h)).trans (LinearEquiv.funUnique ι Γ(X, V) Γ(X, V))
  let T : TensorProduct Γ(X, V) Γ(L, V) Γ(moduleSheafDual L, V) ≃ₗ[Γ(X, V)] Γ(X, V) :=
    (TensorProduct.congr c d).trans (TensorProduct.lid Γ(X, V) Γ(X, V))
  have key : ∀ t, (dualEvalPresheafMap L).app (op V) t = T t := by
    intro t
    change TensorProduct Γ(X, V) Γ(L, V) Γ(moduleSheafDual L, V) at t
    induction t using TensorProduct.induction_on with
    | zero => exact (map_zero _).trans (map_zero T).symm
    | tmul l ψ =>
      refine (dualEvalPresheafMap_tmul l ψ).trans ?_
      simp only [T, c, d, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
        TensorProduct.lid_tmul, LinearEquiv.funUnique_apply]
      conv_lhs => rw [← hL.localFrameMap_coord h l]
      rw [localFrameMap_apply, Fintype.sum_unique, map_smul]
      rfl
    | add a b ha hb => exact (map_add _ a b).trans ((congrArg₂ (· + ·) ha hb).trans
        (map_add T a b).symm)
  have : ⇑((dualEvalPresheafMap L).app (op V)) = ⇑T := funext key
  rw [this]
  exact T.bijective

variable (L)

/-- If `L` has frames of rank one locally, the evaluation map is an isomorphism. -/
lemma isIso_moduleSheafDualEval_of_localFrames
    (hL : ∀ x : X, ∃ (U : X.Opens) (e : ULift.{u} (Fin 1) → Γ(L, U)), x ∈ U ∧
      IsLocalFrame L U e) :
    IsIso (moduleSheafDualEval L) := by
  refine modules_isIso_of_stalk_bijective _ fun x => ?_
  obtain ⟨U, e, hx, hLU⟩ := hL x
  have h1 := pic_stalk_bijective (dualEvalPresheafMap L) hx
    (fun V h => dualEvalPresheafMap_bijective hLU h)
  have h2 := ModuleSheafTensor.moduleSheafTensorUnitStalk_bijective L (moduleSheafDual L) x
  have hc : dualEvalPresheafMap L =
      @CategoryStruct.comp (TopCat.Presheaf AddCommGrpCat.{u} X) _ _ _ _
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
          (moduleSheafTensorPresheaf L (moduleSheafDual L)).presheaf)
        (Scheme.Modules.Hom.mapPresheaf (moduleSheafDualEval L)) :=
    (PresheafOfModules.toPresheaf _).map_comp _ _
  have e := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map_comp
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
      (moduleSheafTensorPresheaf L (moduleSheafDual L)).presheaf)
    (Scheme.Modules.Hom.mapPresheaf (moduleSheafDualEval L))
  rw [hc, e] at h1
  exact (Function.Bijective.of_comp_iff _ h2).mp h1

/-- **Hartshorne II, Proposition 6.12 (second part).** For an invertible sheaf `L`, the
evaluation map `L ⊗ L^∨ ⟶ 𝒪_X` is an isomorphism. -/
theorem moduleSheafDualEval_isIso (hL : L.IsInvertible) : IsIso (moduleSheafDualEval L) :=
  isIso_moduleSheafDualEval_of_localFrames L (exists_isLocalFrame_of_isLocallyFreeOfRank hL)

/-- The isomorphism `L ⊗ L^∨ ≅ 𝒪_X` given by evaluation, for an invertible sheaf `L`. -/
noncomputable def moduleSheafDualEvalIso (hL : L.IsInvertible) :
    @Iso X.Modules _ (moduleSheafTensor L (moduleSheafDual L)) (structureModule X) :=
  haveI := moduleSheafDualEval_isIso L hL
  asIso (moduleSheafDualEval L)

end Evaluation

section Associativity

/-- A trilinear morphism `A × B × C → H` of `𝒪_X`-modules: for every open `U`, an
`𝒪_X(U)`-trilinear map `A(U) × B(U) × C(U) → H(U)`, compatible with restriction. -/
structure ModuleSheafTrilinear (A B C H : X.Modules) where
  /-- The trilinear map on sections over `U`, linear in the last variable. -/
  app (U : X.Opens) : Γ(A, U) → Γ(B, U) → Γ(C, U) →ₗ[Γ(X, U)] Γ(H, U)
  add_left (U : X.Opens) (a a' : Γ(A, U)) (b : Γ(B, U)) :
    app U (a + a') b = app U a b + app U a' b
  smul_left (U : X.Opens) (r : Γ(X, U)) (a : Γ(A, U)) (b : Γ(B, U)) :
    app U (r • a) b = r • app U a b
  add_mid (U : X.Opens) (a : Γ(A, U)) (b b' : Γ(B, U)) :
    app U a (b + b') = app U a b + app U a b'
  smul_mid (U : X.Opens) (r : Γ(X, U)) (a : Γ(A, U)) (b : Γ(B, U)) :
    app U a (r • b) = r • app U a b
  naturality {U V : X.Opens} (i : V ≤ U) (a : Γ(A, U)) (b : Γ(B, U)) (c : Γ(C, U)) :
    H.presheaf.map (homOfLE i).op (app U a b c) =
      app V (A.presheaf.map (homOfLE i).op a) (B.presheaf.map (homOfLE i).op b)
        (C.presheaf.map (homOfLE i).op c)

namespace ModuleSheafTrilinear

variable {A B C H : X.Modules} (τ : ModuleSheafTrilinear A B C H)

/-- The local morphism `c ↦ τ(a, b, c)` attached to sections `a`, `b` over `U`. -/
noncomputable def homSection {U : X.Opens} (a : Γ(A, U)) (b : Γ(B, U)) :
    Γ(moduleSheafHom C H, U) :=
  moduleSheafHomMk
    (fun V h => τ.app V (A.presheaf.map (homOfLE h).op a) (B.presheaf.map (homOfLE h).op b))
    (fun V V' hV j x => by
      rw [τ.naturality j, pic_map_map, pic_map_map])

/-- Evaluating `τ.homSection a b` at `c` gives `τ(a, b, c)`. -/
lemma homSection_eval {U : X.Opens} (a : Γ(A, U)) (b : Γ(B, U)) {V : X.Opens} (h : V ≤ U)
    (c : Γ(C, V)) :
    moduleSheafHomEval (τ.homSection a b) h c =
      τ.app V (A.presheaf.map (homOfLE h).op a) (B.presheaf.map (homOfLE h).op b) c := rfl

/-- The local morphisms `τ.homSection a b` are compatible with restriction. -/
lemma homSection_restrict {U V : X.Opens} (i : V ≤ U) (a : Γ(A, U)) (b : Γ(B, U)) :
    (moduleSheafHom C H).presheaf.map (homOfLE i).op (τ.homSection a b) =
      τ.homSection (A.presheaf.map (homOfLE i).op a) (B.presheaf.map (homOfLE i).op b) :=
  moduleSheafHomEval_ext fun W h => LinearMap.ext fun c => by
    change τ.app W (A.presheaf.map (homOfLE (h.trans i)).op a)
        (B.presheaf.map (homOfLE (h.trans i)).op b) c =
      τ.app W (A.presheaf.map (homOfLE h).op (A.presheaf.map (homOfLE i).op a))
        (B.presheaf.map (homOfLE h).op (B.presheaf.map (homOfLE i).op b)) c
    rw [pic_map_map, pic_map_map]

/-- The sections `τ.homSection a b`, as a bilinear map in `a` and `b`. -/
noncomputable def homSectionBilinear (U : X.Opens) :
    Γ(A, U) →ₗ[Γ(X, U)] Γ(B, U) →ₗ[Γ(X, U)] Γ(moduleSheafHom C H, U) :=
  LinearMap.mk₂ _ (fun a b => τ.homSection a b)
    (fun a a' b => moduleSheafHomEval_ext fun V h => LinearMap.ext fun c => by
      change τ.app V (A.presheaf.map (homOfLE h).op (a + a')) (B.presheaf.map (homOfLE h).op b) c =
        τ.app V (A.presheaf.map (homOfLE h).op a) (B.presheaf.map (homOfLE h).op b) c +
          τ.app V (A.presheaf.map (homOfLE h).op a') (B.presheaf.map (homOfLE h).op b) c
      rw [map_add, τ.add_left]
      rfl)
    (fun r a b => moduleSheafHomEval_ext fun V h => LinearMap.ext fun c => by
      change τ.app V (A.presheaf.map (homOfLE h).op (r • a)) (B.presheaf.map (homOfLE h).op b) c =
        X.presheaf.map (homOfLE h).op r •
          τ.app V (A.presheaf.map (homOfLE h).op a) (B.presheaf.map (homOfLE h).op b) c
      rw [Scheme.Modules.map_smul, τ.smul_left]
      rfl)
    (fun a b b' => moduleSheafHomEval_ext fun V h => LinearMap.ext fun c => by
      change τ.app V (A.presheaf.map (homOfLE h).op a) (B.presheaf.map (homOfLE h).op (b + b')) c =
        τ.app V (A.presheaf.map (homOfLE h).op a) (B.presheaf.map (homOfLE h).op b) c +
          τ.app V (A.presheaf.map (homOfLE h).op a) (B.presheaf.map (homOfLE h).op b') c
      rw [map_add, τ.add_mid]
      rfl)
    (fun r a b => moduleSheafHomEval_ext fun V h => LinearMap.ext fun c => by
      change τ.app V (A.presheaf.map (homOfLE h).op a) (B.presheaf.map (homOfLE h).op (r • b)) c =
        X.presheaf.map (homOfLE h).op r •
          τ.app V (A.presheaf.map (homOfLE h).op a) (B.presheaf.map (homOfLE h).op b) c
      rw [Scheme.Modules.map_smul, τ.smul_mid]
      rfl)

/-- The bilinear morphism `A × B → ℋom(C, H)` attached to a trilinear morphism. -/
noncomputable def toBilinearHom : ModuleSheafBilinear A B (moduleSheafHom C H) where
  app U := τ.homSectionBilinear U.unop
  naturality i a b := τ.homSection_restrict (leOfHom i.unop) a b

/-- The morphism `(A ⊗ B) ⊗ C ⟶ H`, `(a ⊗ b) ⊗ c ↦ τ(a, b, c)`. -/
noncomputable def tensorDesc :
    @Quiver.Hom X.Modules _ (moduleSheafTensor (moduleSheafTensor A B) C) H :=
  (moduleSheafTensorHomEquiv _ _ _).symm
    { app U := (homUncurry ((moduleSheafTensorHomEquiv _ _ _).symm τ.toBilinearHom)).app U |>.flip
      naturality i t c :=
        (homUncurry ((moduleSheafTensorHomEquiv _ _ _).symm τ.toBilinearHom)).naturality i c t }

/-- The morphism `τ.tensorDesc` sends `(a ⊗ b) ⊗ c` to `τ(a, b, c)`. -/
lemma tensorDesc_tmul {U : X.Opens} (a : Γ(A, U)) (b : Γ(B, U)) (c : Γ(C, U)) :
    τ.tensorDesc.app U ((moduleSheafTensorBilinear (moduleSheafTensor A B) C).app (op U)
      ((moduleSheafTensorBilinear A B).app (op U) a b) c) = τ.app U a b c := by
  refine (moduleSheafTensorHomEquiv_symm_tmul _ _ c).trans ?_
  change moduleSheafHomEval (Scheme.Modules.Hom.app ((moduleSheafTensorHomEquiv _ _ _).symm
    τ.toBilinearHom) U ((moduleSheafTensorBilinear A B).app (op U) a b)) (le_refl U) c = _
  refine (congrArg (fun ψ => moduleSheafHomEval ψ (le_refl U) c)
    (moduleSheafTensorHomEquiv_symm_tmul τ.toBilinearHom a b)).trans ?_
  change τ.app U (A.presheaf.map (homOfLE (le_refl U)).op a)
    (B.presheaf.map (homOfLE (le_refl U)).op b) c = _
  rw [pic_map_id, pic_map_id]

end ModuleSheafTrilinear

/-- Two morphisms out of `(A ⊗ B) ⊗ C` agreeing on all elementary tensors `(a ⊗ b) ⊗ c` are
equal. -/
lemma moduleSheafTensor_assoc_hom_ext {A B C H : X.Modules}
    {φ ψ : @Quiver.Hom X.Modules _ (moduleSheafTensor (moduleSheafTensor A B) C) H}
    (h : ∀ (U : X.Opens) (a : Γ(A, U)) (b : Γ(B, U)) (c : Γ(C, U)),
      φ.app U ((moduleSheafTensorBilinear (moduleSheafTensor A B) C).app (op U)
        ((moduleSheafTensorBilinear A B).app (op U) a b) c) =
      ψ.app U ((moduleSheafTensorBilinear (moduleSheafTensor A B) C).app (op U)
        ((moduleSheafTensorBilinear A B).app (op U) a b) c)) : φ = ψ := by
  let flipB : ∀ (χ : @Quiver.Hom X.Modules _ (moduleSheafTensor (moduleSheafTensor A B) C) H),
      ModuleSheafBilinear C (moduleSheafTensor A B) H := fun χ =>
    { app U := (moduleSheafTensorHomEquiv _ _ H χ).app U |>.flip
      naturality i c t := (moduleSheafTensorHomEquiv _ _ H χ).naturality i t c }
  have hcurry : bilinearCurry (flipB φ) = bilinearCurry (flipB ψ) := by
    refine modulesTensor_hom_ext fun U a b => moduleSheafHomEval_ext fun V hV =>
      LinearMap.ext fun c => ?_
    change φ.app V ((moduleSheafTensorBilinear (moduleSheafTensor A B) C).app (op V)
        ((moduleSheafTensor A B).val.map (homOfLE hV).op
          ((moduleSheafTensorBilinear A B).app (op U) a b)) c) =
      ψ.app V ((moduleSheafTensorBilinear (moduleSheafTensor A B) C).app (op V)
        ((moduleSheafTensor A B).val.map (homOfLE hV).op
          ((moduleSheafTensorBilinear A B).app (op U) a b)) c)
    have hn : (moduleSheafTensor A B).val.map (homOfLE hV).op
        ((moduleSheafTensorBilinear A B).app (op U) a b) =
        (moduleSheafTensorBilinear A B).app (op V) (A.presheaf.map (homOfLE hV).op a)
          (B.presheaf.map (homOfLE hV).op b) :=
      (moduleSheafTensorBilinear A B).naturality _ a b
    erw [hn]
    exact h V _ _ c
  have hflip : flipB φ = flipB ψ := bilinearCurryEquiv.injective hcurry
  apply (moduleSheafTensorHomEquiv _ _ H).injective
  ext U t c
  exact congrArg (fun β : ModuleSheafBilinear C (moduleSheafTensor A B) H => β.app U c t) hflip

variable (L M N : X.Modules)

/-- The tensor product of two `𝒪_X`-modules, as an object of `X.Modules`. -/
noncomputable abbrev modulesTensorObj (E F : X.Modules) : X.Modules := moduleSheafTensor E F

/-- The trilinear map `(l, m, n) ↦ l ⊗ (m ⊗ n)`. -/
noncomputable def assocTrilinear :
    ModuleSheafTrilinear L M N (modulesTensorObj L (modulesTensorObj M N)) where
  app U l m := by
    let f := ((moduleSheafTensorBilinear L (moduleSheafTensor M N)).app (op U) l).comp
      ((moduleSheafTensorBilinear M N).app (op U) m)
    exact f
  add_left U l l' m := LinearMap.ext fun _ =>
    LinearMap.map_add₂ ((moduleSheafTensorBilinear L (moduleSheafTensor M N)).app (op U)) l l' _
  smul_left U r l m := LinearMap.ext fun _ =>
    LinearMap.map_smul₂ ((moduleSheafTensorBilinear L (moduleSheafTensor M N)).app (op U))
      (show (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op U) from r) l _
  add_mid U l m m' := LinearMap.ext fun n =>
    (congrArg ((moduleSheafTensorBilinear L (moduleSheafTensor M N)).app (op U) l)
      (LinearMap.map_add₂ ((moduleSheafTensorBilinear M N).app (op U)) m m' n)).trans
      (map_add _ _ _)
  smul_mid U r l m := LinearMap.ext fun n =>
    (congrArg ((moduleSheafTensorBilinear L (moduleSheafTensor M N)).app (op U) l)
      (LinearMap.map_smul₂ ((moduleSheafTensorBilinear M N).app (op U))
        (show (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op U) from r) m n)).trans
      (map_smul _ _ _)
  naturality {U V} i l m n :=
    ((moduleSheafTensorBilinear L (moduleSheafTensor M N)).naturality (homOfLE i).op l _).trans
      (congrArg ((moduleSheafTensorBilinear L (moduleSheafTensor M N)).app (op V) _)
        ((moduleSheafTensorBilinear M N).naturality (homOfLE i).op m n))

/-- The trilinear map `(m, n, l) ↦ (l ⊗ m) ⊗ n`. -/
noncomputable def assocInvTrilinear :
    ModuleSheafTrilinear M N L (modulesTensorObj (modulesTensorObj L M) N) where
  app U m n := by
    let g := ((moduleSheafTensorBilinear (moduleSheafTensor L M) N).app (op U)).flip
    let h := ((moduleSheafTensorBilinear L M).app (op U)).flip
    let f := (g n).comp (h m)
    exact f
  add_left U m m' n := LinearMap.ext fun l =>
    (congrArg (fun x => (moduleSheafTensorBilinear (moduleSheafTensor L M) N).app (op U) x n)
      (LinearMap.map_add ((moduleSheafTensorBilinear L M).app (op U) l) m m')).trans
      (LinearMap.map_add₂ ((moduleSheafTensorBilinear (moduleSheafTensor L M) N).app (op U))
        _ _ n)
  smul_left U r m n := LinearMap.ext fun l =>
    (congrArg (fun x => (moduleSheafTensorBilinear (moduleSheafTensor L M) N).app (op U) x n)
      (LinearMap.map_smul ((moduleSheafTensorBilinear L M).app (op U) l)
        (show (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op U) from r) m)).trans
      (LinearMap.map_smul₂ ((moduleSheafTensorBilinear (moduleSheafTensor L M) N).app (op U))
        _ _ n)
  add_mid U m n n' := LinearMap.ext fun l =>
    LinearMap.map_add ((moduleSheafTensorBilinear (moduleSheafTensor L M) N).app (op U)
      ((moduleSheafTensorBilinear L M).app (op U) l m)) n n'
  smul_mid U r m n := LinearMap.ext fun l =>
    LinearMap.map_smul ((moduleSheafTensorBilinear (moduleSheafTensor L M) N).app (op U)
      ((moduleSheafTensorBilinear L M).app (op U) l m))
      (show (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op U) from r) n
  naturality {U V} i m n l :=
    ((moduleSheafTensorBilinear (moduleSheafTensor L M) N).naturality (homOfLE i).op _ n).trans
      (congrArg (fun x => (moduleSheafTensorBilinear (moduleSheafTensor L M) N).app (op V) x _)
        ((moduleSheafTensorBilinear L M).naturality (homOfLE i).op l m))

/-- **Associativity of the tensor product:** `(L ⊗ M) ⊗ N ≅ L ⊗ (M ⊗ N)`. -/
noncomputable def moduleSheafTensorAssoc :
    @Iso X.Modules _ (moduleSheafTensor (moduleSheafTensor L M) N)
      (moduleSheafTensor L (moduleSheafTensor M N)) where
  hom := (assocTrilinear L M N).tensorDesc
  inv := (moduleSheafTensorComm L (moduleSheafTensor M N)).hom ≫
    (assocInvTrilinear L M N).tensorDesc
  hom_inv_id := by
    refine moduleSheafTensor_assoc_hom_ext fun U l m n => ?_
    change (assocInvTrilinear L M N).tensorDesc.app U
      ((moduleSheafTensorFlip L (moduleSheafTensor M N)).app U
        ((assocTrilinear L M N).tensorDesc.app U _)) = _
    refine (congrArg (fun x => (assocInvTrilinear L M N).tensorDesc.app U
      ((moduleSheafTensorFlip L (moduleSheafTensor M N)).app U x))
        ((assocTrilinear L M N).tensorDesc_tmul l m n)).trans ?_
    refine (congrArg (fun x => (assocInvTrilinear L M N).tensorDesc.app U x)
      (moduleSheafTensorFlip_tmul L (moduleSheafTensor M N) l _)).trans ?_
    exact (assocInvTrilinear L M N).tensorDesc_tmul m n l
  inv_hom_id := by
    have h : (assocInvTrilinear L M N).tensorDesc ≫ (assocTrilinear L M N).tensorDesc =
        (moduleSheafTensorComm L (moduleSheafTensor M N)).inv := by
      refine moduleSheafTensor_assoc_hom_ext fun U m n l => ?_
      change (assocTrilinear L M N).tensorDesc.app U
        ((assocInvTrilinear L M N).tensorDesc.app U _) =
        (moduleSheafTensorFlip (moduleSheafTensor M N) L).app U _
      refine (congrArg (fun x => (assocTrilinear L M N).tensorDesc.app U x)
        ((assocInvTrilinear L M N).tensorDesc_tmul m n l)).trans ?_
      refine ((assocTrilinear L M N).tensorDesc_tmul l m n).trans ?_
      exact (moduleSheafTensorFlip_tmul (moduleSheafTensor M N) L _ l).symm
    exact (Category.assoc _ _ _).trans ((congrArg _ h).trans (Iso.hom_inv_id _))

end Associativity

section DualCongr

/-- The functoriality of `ℋom` is compatible with composition. -/
lemma moduleSheafHomMap_comp {F F' F'' G G' G'' : X.Modules} (f : F' ⟶ F) (g : G ⟶ G')
    (f' : F'' ⟶ F') (g' : G' ⟶ G'') :
    moduleSheafHomMap f g ≫ moduleSheafHomMap f' g' = moduleSheafHomMap (f' ≫ f) (g ≫ g') := by
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  ext ψ
  exact moduleSheafHomEval_ext fun V h => LinearMap.ext fun x => rfl

/-- `ℋom` sends identities to the identity. -/
lemma moduleSheafHomMap_id (F G : X.Modules) :
    moduleSheafHomMap (𝟙 F) (𝟙 G) = 𝟙 _ := by
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  ext ψ
  exact moduleSheafHomEval_ext fun V h => LinearMap.ext fun x => rfl

/-- Isomorphic modules have isomorphic duals. -/
noncomputable def moduleSheafDualIsoOfIso {L L' : X.Modules} (α : L ≅ L') :
    moduleSheafDual L ≅ moduleSheafDual L' where
  hom := moduleSheafHomMap α.inv (𝟙 _)
  inv := moduleSheafHomMap α.hom (𝟙 _)
  hom_inv_id := by
    rw [moduleSheafHomMap_comp, α.hom_inv_id, Category.id_comp, moduleSheafHomMap_id]
  inv_hom_id := by
    rw [moduleSheafHomMap_comp, α.inv_hom_id, Category.id_comp, moduleSheafHomMap_id]

end DualCongr

end Hartshorne

namespace AlgebraicGeometry.Scheme

open Hartshorne

/-- Two invertible `𝒪_X`-modules are related when they are isomorphic. -/
def invertibleModulesSetoid (X : Scheme.{u}) : Setoid {L : X.Modules // L.IsInvertible} where
  r L M := Nonempty (L.1 ≅ M.1)
  iseqv := ⟨fun _ => ⟨Iso.refl _⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e ≪≫ f⟩⟩

/-- **The Picard group** `Pic X`: the isomorphism classes of invertible `𝒪_X`-modules. -/
def Pic (X : Scheme.{u}) : Type (u + 1) :=
  Quotient X.invertibleModulesSetoid

namespace Pic

variable {X : Scheme.{u}}

/-- The class in `Pic X` of an invertible `𝒪_X`-module. -/
def mk (L : X.Modules) (hL : L.IsInvertible) : X.Pic :=
  Quotient.mk _ ⟨L, hL⟩

/-- Every element of `Pic X` is the class of an invertible module. -/
lemma mk_surjective (c : X.Pic) : ∃ (L : X.Modules) (hL : L.IsInvertible), mk L hL = c := by
  obtain ⟨⟨L, hL⟩, rfl⟩ := Quotient.exists_rep c
  exact ⟨L, hL, rfl⟩

/-- Two invertible modules have the same class exactly when they are isomorphic. -/
lemma mk_eq_mk_iff {L M : X.Modules} (hL : L.IsInvertible) (hM : M.IsInvertible) :
    mk L hL = mk M hM ↔ Nonempty (L ≅ M) :=
  Quotient.eq (r := X.invertibleModulesSetoid)

/-- The group structure on `Pic X`: multiplication is the tensor product, the identity is the
class of `𝒪_X`, and the inverse is the class of the dual `ℋom(L, 𝒪_X)`. -/
noncomputable instance instCommGroup : CommGroup X.Pic where
  mul := Quotient.map₂
    (fun L M => ⟨moduleSheafTensor L.1 M.1, isInvertible_moduleSheafTensor L.2 M.2⟩)
    (fun _ _ ⟨α⟩ _ _ ⟨β⟩ => ⟨moduleSheafTensorIsoOfIso α β⟩)
  one := mk (structureModule X) structureModule_isInvertible
  inv := Quotient.map (fun L => ⟨moduleSheafDual L.1, isInvertible_moduleSheafDual L.2⟩)
    (fun _ _ ⟨α⟩ => ⟨moduleSheafDualIsoOfIso α⟩)
  mul_assoc a b c := Quotient.inductionOn₃ a b c fun L M N =>
    Quotient.sound ⟨moduleSheafTensorAssoc L.1 M.1 N.1⟩
  one_mul a := Quotient.inductionOn a fun L => Quotient.sound ⟨moduleSheafUnitTensor L.1⟩
  mul_one a := Quotient.inductionOn a fun L =>
    Quotient.sound ⟨moduleSheafTensorComm _ _ ≪≫ moduleSheafUnitTensor L.1⟩
  inv_mul_cancel a := Quotient.inductionOn a fun L =>
    Quotient.sound ⟨moduleSheafTensorComm _ _ ≪≫ moduleSheafDualEvalIso L.1 L.2⟩
  mul_comm a b := Quotient.inductionOn₂ a b fun L M =>
    Quotient.sound ⟨moduleSheafTensorComm L.1 M.1⟩

/-- Multiplication in `Pic X` is induced by the tensor product. -/
lemma mk_mul_mk {L M : X.Modules} (hL : L.IsInvertible) (hM : M.IsInvertible) :
    mk L hL * mk M hM = mk (moduleSheafTensor L M) (isInvertible_moduleSheafTensor hL hM) :=
  rfl

/-- The identity of `Pic X` is the class of `𝒪_X`. -/
lemma one_eq_mk : (1 : X.Pic) = mk (structureModule X) structureModule_isInvertible :=
  rfl

/-- The inverse in `Pic X` is the class of the dual `ℋom(L, 𝒪_X)`. -/
lemma inv_mk {L : X.Modules} (hL : L.IsInvertible) :
    (mk L hL)⁻¹ = mk (moduleSheafDual L) (isInvertible_moduleSheafDual hL) :=
  rfl

end Pic

end AlgebraicGeometry.Scheme

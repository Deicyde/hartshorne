/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.FiniteLocallyFreeDuality

/-!
# The projection formula for finite locally free sheaves

Hartshorne, *Algebraic Geometry*, II, Exercise 5.1(d).

Let `f : X ⟶ Y` be a morphism of schemes, `F` an `𝒪_X`-module and `E` an `𝒪_Y`-module. Write
`η : E ⟶ f_* f^* E` for the unit of the pullback–pushforward adjunction (`pullbackUnit`). The
*projection-formula map* `projectionFormulaMap f F E : f_*F ⊗ E ⟶ f_*(F ⊗ f^*E)` is induced by
the bilinear map `(s, x) ↦ s ⊗ η(x)`; it is natural in `F` (`projectionFormulaMap_naturality_left`)
and in `E` (`projectionFormulaMap_naturality_right`). The main result is

* `projectionFormulaMap_isIso`: if `E` is finite locally free (locally free with finite rank at
  every point), the projection-formula map is an isomorphism; `projectionFormulaIso` is the
  resulting natural isomorphism `f_*(F ⊗ f^*E) ≅ f_*F ⊗ E`.

The finite locally free modules, duals and frames used here are those of
`Hartshorne.Scheme.FiniteLocallyFreeDuality`, which are set up for schemes; accordingly the
result is stated for morphisms of schemes.

## Proof

The argument is local on `Y`, using the frames (`IsLocalFrame`) of the duality file.

* `IsLocalFrame.pullback`: if `e` is a frame of `E` over `U`, then `η(e_i)` is a frame of `f^*E`
  over `f⁻¹U`. We show that the morphism `𝒪^ι ⟶ (f^*E)|_{f⁻¹U}` given by the `η(e_i)` is an
  isomorphism; its inverse is adjoint (for the adjunction `f^*(-)|_{f⁻¹U} ⊣ f_* j_*`) to the
  morphism `E ⟶ f_* j_* 𝒪^ι` sending a section to its coordinates pulled back along `f`.
* `IsLocalFrame.tensorFrameMap_bijective`: if `b` is a frame of `A` over `W`, then on every open
  `V ⊆ W` the map `F(V)^ι → (F ⊗ A)(V)`, `(s_i) ↦ ∑ s_i ⊗ b_i`, is bijective. This is proved by
  comparing `F ⊗ A` with `ℋom(A^∨, F)` through the pairing `A ⟶ A^∨∨`.
* On an open `V ⊆ U` the presheaf-level projection map `F(f⁻¹V) ⊗ E(V) → (F ⊗ f^*E)(f⁻¹V)`
  is the composite of the bijection `F(f⁻¹V)^ι ≅ F(f⁻¹V) ⊗ E(V)` with the bijection of the
  previous item for the frame `η(e_i)`, so it is bijective; since sheafification does not change
  stalks, the projection-formula map is bijective on stalks, hence an isomorphism.
-/

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Limits
open scoped TensorProduct

namespace Hartshorne

section Helpers

variable {X : Scheme.{u}}

lemma modules_map_map' (A : X.Modules) {U V W : X.Opens} (g : op U ⟶ op V) (g' : op V ⟶ op W)
    (g'' : op U ⟶ op W) (x : Γ(A, U)) :
    A.presheaf.map g' (A.presheaf.map g x) = A.presheaf.map g'' x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, Subsingleton.elim (g ≫ g') g'']

lemma modules_map_self (A : X.Modules) {U : X.Opens} (g : op U ⟶ op U) (x : Γ(A, U)) :
    A.presheaf.map g x = x := by
  rw [Subsingleton.elim g (𝟙 _), CategoryTheory.Functor.map_id]
  rfl

lemma ring_map_map' {U V W : X.Opens} (g : op U ⟶ op V) (g' : op V ⟶ op W)
    (g'' : op U ⟶ op W) (r : Γ(X, U)) :
    X.presheaf.map g' (X.presheaf.map g r) = X.presheaf.map g'' r := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, Subsingleton.elim (g ≫ g') g'']

lemma openImmersion_app_map {Z : Scheme.{u}} (g : Z ⟶ X) [IsOpenImmersion g] (W : X.Opens)
    {V : Z.Opens} (h : V ≤ g ⁻¹ᵁ W) (t : Γ(X, W)) :
    Z.presheaf.map (homOfLE h).op (g.app W t) =
      (g.appIso V).hom (X.presheaf.map
        (homOfLE ((g.image_mono h).trans (g.image_preimage_le W))).op t) := by
  change g.appLE W V h t = _
  rw [Scheme.Hom.appIso_hom', ← ConcreteCategory.comp_apply (X.presheaf.map _),
    Scheme.Hom.map_appLE]

lemma freeIncl_app_eq {I : Type u} (k : I) (V : X.Opens) (t : Γ(X, V)) :
    (freeIncl (Y := X) (I := I) k).app V t =
      t • (freeModule X I).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
        ((freeIncl (Y := X) (I := I) k).app ⊤ (1 : Γ(X, ⊤))) := by
  have h1 := ConcreteCategory.congr_hom
    ((freeIncl (Y := X) (I := I) k).mapPresheaf.naturality (homOfLE (le_top : V ≤ ⊤)).op)
    (1 : Γ(X, ⊤))
  change (freeIncl (Y := X) (I := I) k).app V (X.presheaf.map _ 1) =
    (freeModule X I).presheaf.map _ ((freeIncl k).app ⊤ (1 : Γ(X, ⊤))) at h1
  calc (freeIncl (Y := X) (I := I) k).app V t
      = (freeIncl (Y := X) (I := I) k).app V (t • X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
          (1 : Γ(X, ⊤))) := by
        rw [map_one]
        congr 1
        exact (mul_one t).symm
    _ = t • (freeIncl (Y := X) (I := I) k).app V
          (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (1 : Γ(X, ⊤))) :=
        Scheme.Modules.Hom.app_smul _ _ _
    _ = _ := by rw [h1]

private lemma stalk_bijective_of_locally_bijective' {Y : TopCat.{u}}
    {P Q : TopCat.Presheaf AddCommGrpCat.{u} Y} (p : P ⟶ Q) {x : Y} {U : Opens Y} (hx : x ∈ U)
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

/-- A morphism out of a tensor product of `𝒪_X`-modules is bijective on sections over every open
inside `W` if the induced map on the presheaf tensor product is bijective on all opens inside `W`. -/
lemma tensor_app_bijective_of_presheaf {F G H : X.Modules}
    (φ : @Quiver.Hom X.Modules _ (moduleSheafTensor F G) H) {W : X.Opens}
    (hφ : ∀ V : X.Opens, V ≤ W → Function.Bijective
      (((PresheafOfModules.toPresheaf _).map (moduleSheafTensorUnit F G ≫ φ.val)).app (op V)))
    {V : X.Opens} (hV : V ≤ W) : Function.Bijective (φ.app V) := by
  have hst : ∀ x ∈ V, Function.Bijective
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map φ.mapPresheaf) := by
    intro x hx
    have h1 := stalk_bijective_of_locally_bijective' _ (hV hx) hφ
    have h2 := ModuleSheafTensor.moduleSheafTensorUnitStalk_bijective F G x
    have hc : (PresheafOfModules.toPresheaf _).map (moduleSheafTensorUnit F G ≫ φ.val) =
        @CategoryStruct.comp (TopCat.Presheaf AddCommGrpCat.{u} X) _ _ _ _
          (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
            (moduleSheafTensorPresheaf F G).presheaf)
          (Scheme.Modules.Hom.mapPresheaf φ) :=
      (PresheafOfModules.toPresheaf _).map_comp _ _
    have e := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map_comp
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        (moduleSheafTensorPresheaf F G).presheaf)
      (Scheme.Modules.Hom.mapPresheaf φ)
    rw [hc] at h1
    erw [e] at h1
    exact (Function.Bijective.of_comp_iff _ h2).mp h1
  let T : X.Modules := moduleSheafTensor F G
  let f : (⟨T.presheaf, T.isSheaf⟩ :
      TopCat.Sheaf AddCommGrpCat.{u} X) ⟶ ⟨H.presheaf, H.isSheaf⟩ := ⟨φ.mapPresheaf⟩
  exact TopCat.Presheaf.app_bijective_of_stalkFunctor_map_bijective f V hst

end Helpers

section Algebra

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Tensoring with a module that has a finite basis on the right: the coordinate map
`M ⊗ N → M^ι`, `m ⊗ n ↦ (c_j(n) m)_j`, is bijective. -/
lemma tensor_frame_right_bijective (b : ι → N) (c : N →ₗ[R] (ι → R))
    (hc : ∀ n, ∑ j, c n j • b j = n) (hb : ∀ i, c (b i) = Pi.single i 1)
    (Φ : TensorProduct R M N →+ (ι → M)) (hΦ : ∀ m n, Φ (m ⊗ₜ n) = fun j => c n j • m) :
    Function.Bijective Φ := by
  have h := tensor_localFrame_bijective (M := N) (N := M) b c hc hb
    (Φ.comp (TensorProduct.comm R N M).toLinearMap.toAddMonoidHom) (fun n m => by
      simp only [AddMonoidHom.coe_comp, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe,
        Function.comp_apply, TensorProduct.comm_tmul, hΦ])
  have he : ⇑Φ = ⇑(Φ.comp (TensorProduct.comm R N M).toLinearMap.toAddMonoidHom) ∘
      ⇑(TensorProduct.comm R M N) := by
    funext t
    simp
  rw [he]
  exact h.comp (TensorProduct.comm R M N).bijective

/-- With a finite basis `b` of `N`, the map `M^ι → M ⊗ N`, `(m_i) ↦ ∑ m_i ⊗ b_i`, is bijective. -/
lemma sum_tmul_frame_bijective (b : ι → N) (c : N →ₗ[R] (ι → R))
    (hc : ∀ n, ∑ j, c n j • b j = n) (hb : ∀ i, c (b i) = Pi.single i 1) :
    Function.Bijective (fun m : ι → M => ∑ i, m i ⊗ₜ[R] b i) := by
  let β : M →ₗ[R] N →ₗ[R] (ι → M) := LinearMap.mk₂ R (fun m n j => c n j • m)
    (fun m m' n => by funext j; exact smul_add _ _ _)
    (fun r m n => by funext j; exact smul_comm _ _ _)
    (fun m n n' => by funext j; simp [add_smul])
    (fun r m n => by funext j; simp [mul_smul])
  let Φ : TensorProduct R M N →+ (ι → M) := (TensorProduct.lift β).toAddMonoidHom
  have hΦ : ∀ m n, Φ (m ⊗ₜ n) = fun j => c n j • m := fun m n => rfl
  have hbij := tensor_frame_right_bijective b c hc hb Φ hΦ
  refine (Function.Bijective.of_comp_iff' hbij _).mp ?_
  have hid : ⇑Φ ∘ (fun m : ι → M => ∑ i, m i ⊗ₜ[R] b i) = id := by
    funext m
    simp only [Function.comp_apply, map_sum, hΦ, hb, id]
    funext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · rw [Pi.single_eq_same, one_smul]
    · intro i _ hij
      rw [Pi.single_eq_of_ne (Ne.symm hij), zero_smul]
    · intro h'; exact absurd (Finset.mem_univ j) h'
  rw [hid]
  exact Function.bijective_id

end Algebra

section TensorFrame

variable {X : Scheme.{u}}

section Pairing

variable {F A B : X.Modules} (p : A ⟶ moduleSheafDual B)

lemma dualTensorSection_app_add {U : X.Opens} (s : Γ(F, U)) (a a' : Γ(A, U)) :
    dualTensorSection (p.app U (a + a')) s =
      dualTensorSection (p.app U a) s + dualTensorSection (p.app U a') s := by
  rw [map_add, dualTensorSection_add_left]

lemma dualTensorSection_app_smul {U : X.Opens} (r : Γ(X, U)) (s : Γ(F, U)) (a : Γ(A, U)) :
    dualTensorSection (p.app U (r • a)) s = r • dualTensorSection (p.app U a) s := by
  rw [Scheme.Modules.Hom.app_smul, dualTensorSection_smul_left]

lemma dualTensorSection_app_restrict {U V : X.Opens} (i : V ≤ U) (s : Γ(F, U)) (a : Γ(A, U)) :
    (moduleSheafHom B F).presheaf.map (homOfLE i).op (dualTensorSection (p.app U a) s) =
      dualTensorSection (p.app V (A.presheaf.map (homOfLE i).op a))
        (F.presheaf.map (homOfLE i).op s) := by
  rw [dualTensorSection_restrict]
  congr 1
  exact (ConcreteCategory.congr_hom (p.mapPresheaf.naturality (homOfLE i).op) a).symm

variable (F) in
/-- The bilinear map `F × A → ℋom(B, F)`, `(s, a) ↦ (x ↦ p(a)(x) s)`, attached to a pairing
`p : A ⟶ B^∨`. -/
noncomputable def pairingTensorBilinear : ModuleSheafBilinear F A (moduleSheafHom B F) where
  app U := LinearMap.mk₂ _
    (fun (s : Γ(F, U.unop)) (a : Γ(A, U.unop)) => dualTensorSection (p.app U.unop a) s)
    (fun s s' a => dualTensorSection_add_right (p.app U.unop a) s s')
    (fun r s a => dualTensorSection_smul_right r (p.app U.unop a) s)
    (fun s a a' => dualTensorSection_app_add p s a a')
    (fun r s a => dualTensorSection_app_smul p r s a)
  naturality {_ _} i s a := dualTensorSection_app_restrict p (leOfHom i.unop) s a

variable (F) in
/-- The morphism `F ⊗ A ⟶ ℋom(B, F)` attached to a pairing `p : A ⟶ B^∨`. -/
noncomputable def pairingTensorMap :
    @Quiver.Hom X.Modules _ (moduleSheafTensor F A) (moduleSheafHom B F) :=
  (moduleSheafTensorHomEquiv _ _ _).symm (pairingTensorBilinear F p)

lemma pairingTensorMap_tmul {U : X.Opens} (s : Γ(F, U)) (a : Γ(A, U)) :
    (pairingTensorMap F p).val.app (op U) ((moduleSheafTensorBilinear F A).app (op U) s a) =
      dualTensorSection (p.app U a) s := by
  have := congrArg (fun β : ModuleSheafBilinear _ _ _ => β.app (op U) s a)
    ((moduleSheafTensorHomEquiv_apply (pairingTensorMap F p)).symm.trans
      (Equiv.apply_symm_apply (moduleSheafTensorHomEquiv _ _ _) (pairingTensorBilinear F p)))
  exact this

end Pairing

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma localFrameEval_dualTensorSection {F B : X.Modules} {W : X.Opens} (c : ι → Γ(B, W))
    {V : X.Opens} (h : V ≤ W) (ψ : Γ(moduleSheafDual B, V)) (s : Γ(F, V)) :
    localFrameEval c h (dualTensorSection ψ s) =
      fun j => (show Γ(X, V) from localFrameEval c h ψ j) • s := by
  funext j
  rw [localFrameEval_apply, dualTensorSection_eval, modules_map_self]
  rfl

variable (F : X.Modules) {A : X.Modules} {W : X.Opens} (b : ι → Γ(A, W)) in
/-- The map `F(V)^ι → (F ⊗ A)(V)`, `(s_i) ↦ ∑ s_i ⊗ b_i|_V`, attached to a family `b` of
sections of `A` over `W ⊇ V`. -/
noncomputable def tensorFrameMap {V : X.Opens} (h : V ≤ W) (s : ι → Γ(F, V)) :
    (moduleSheafTensor F A).val.obj (op V) :=
  ∑ i, (moduleSheafTensorBilinear F A).app (op V) (s i) (A.presheaf.map (homOfLE h).op (b i))

/-- If `b` is a frame of `A` over `W` and `p : A ⟶ B^∨` identifies the coordinates with respect
to `b` with the values on a frame `c` of `B`, then `(s_i) ↦ ∑ s_i ⊗ b_i` is bijective on every open
`V ⊆ W`. -/
lemma tensorFrameMap_bijective_of_pairing {F A B : X.Modules} {W : X.Opens} {b : ι → Γ(A, W)}
    (hb : IsLocalFrame A W b) {c : ι → Γ(B, W)} (hc : IsLocalFrame B W c)
    (p : A ⟶ moduleSheafDual B)
    (hp : ∀ (V : X.Opens) (h : V ≤ W) (a : Γ(A, V)), localFrameEval c h (p.app V a) = hb.coord h a)
    {V : X.Opens} (h : V ≤ W) :
    Function.Bijective (tensorFrameMap F b h) := by
  have hΛ : ∀ V' : X.Opens, V' ≤ W → Function.Bijective
      (((PresheafOfModules.toPresheaf _).map
        (moduleSheafTensorUnit F A ≫ (pairingTensorMap F p).val)).app (op V')) := by
    intro V' h'
    refine (Function.Bijective.of_comp_iff' (hc.localFrameEval_bijective (G := F) h') _).mp ?_
    let Φ : TensorProduct Γ(X, V') Γ(F, V') Γ(A, V') →+ (ι → Γ(F, V')) :=
      (localFrameEval c h').toAddMonoidHom.comp
        (((PresheafOfModules.toPresheaf _).map
          (moduleSheafTensorUnit F A ≫ (pairingTensorMap F p).val)).app (op V')).hom
    have := tensor_frame_right_bijective (R := Γ(X, V')) (M := Γ(F, V')) (N := Γ(A, V'))
      (fun j => A.presheaf.map (homOfLE h').op (b j)) (hb.coord h').toLinearMap
      (fun a => by
        rw [← localFrameMap_apply]
        exact hb.localFrameMap_coord h' a)
      (fun i => hb.coord_self h' i) Φ (fun s a => by
        change localFrameEval c h' ((pairingTensorMap F p).val.app (op V')
          ((moduleSheafTensorBilinear F A).app (op V') s a)) = _
        rw [pairingTensorMap_tmul, localFrameEval_dualTensorSection, hp]
        rfl)
    exact this
  have hbij : Function.Bijective
      (localFrameEval (G := F) c h ∘ (pairingTensorMap F p).app V) :=
    (hc.localFrameEval_bijective (G := F) h).comp (tensor_app_bijective_of_presheaf _ hΛ h)
  refine (Function.Bijective.of_comp_iff' hbij _).mp ?_
  have hid : (localFrameEval (G := F) c h ∘ (pairingTensorMap F p).app V) ∘
      tensorFrameMap F b h = id := by
    funext s
    change localFrameEval c h ((pairingTensorMap F p).val.app (op V)
      (∑ i, (moduleSheafTensorBilinear F A).app (op V) (s i)
        (A.presheaf.map (homOfLE h).op (b i)))) = s
    rw [map_sum]
    erw [map_sum]
    simp_rw [pairingTensorMap_tmul, localFrameEval_dualTensorSection, hp, hb.coord_self]
    funext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · rw [Pi.single_eq_same, one_smul]
    · intro i _ hij
      rw [Pi.single_eq_of_ne (Ne.symm hij), zero_smul]
    · intro h'; exact absurd (Finset.mem_univ j) h'
  rw [hid]
  exact Function.bijective_id

/-- **Sections of `F ⊗ A` where `A` has a frame.** If `b` is a frame of `A` over `W`, then for
every open `V ⊆ W` the map `F(V)^ι → (F ⊗ A)(V)`, `(s_i) ↦ ∑ s_i ⊗ b_i`, is bijective. -/
lemma IsLocalFrame.tensorFrameMap_bijective {F A : X.Modules} {W : X.Opens} {b : ι → Γ(A, W)}
    (hb : IsLocalFrame A W b) {V : X.Opens} (h : V ≤ W) :
    Function.Bijective (tensorFrameMap F b h) :=
  tensorFrameMap_bijective_of_pairing hb hb.dual (moduleSheafDoubleDualMap A) (fun V' h' a => by
    conv_lhs => rw [← hb.localFrameMap_coord h' a]
    exact localFrameEval_doubleDualMap hb h' _) h

end TensorFrame

section FrameDesc

variable {X : Scheme.{u}} {ι : Type*} [Fintype ι] {A N : X.Modules} {e : ι → Γ(A, ⊤)}

/-- The morphism out of a module with a global frame `e` sending `e_i` to `s_i`. -/
noncomputable def IsLocalFrame.desc (hA : IsLocalFrame A ⊤ e) (s : ι → Γ(N, ⊤)) : A ⟶ N :=
  modulesHomMk (fun V => Fintype.linearCombination Γ(X, V)
      (fun i => N.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (s i)) ∘ₗ
        (hA.coord (le_top : V ≤ ⊤)).toLinearMap)
    (fun V V' i x => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Fintype.linearCombination_apply]
      rw [hA.coord_restrict le_top i x, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Scheme.Modules.map_smul, modules_map_map' N (homOfLE (le_top : V ≤ ⊤)).op
        (homOfLE i).op (homOfLE (le_top : V' ≤ ⊤)).op])

lemma IsLocalFrame.desc_app (hA : IsLocalFrame A ⊤ e) (s : ι → Γ(N, ⊤)) (V : X.Opens)
    (x : Γ(A, V)) :
    (hA.desc s).app V x =
      ∑ i, hA.coord (le_top : V ≤ ⊤) x i • N.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (s i) :=
  Fintype.linearCombination_apply _ _ _

lemma IsLocalFrame.desc_app_frame [DecidableEq ι] (hA : IsLocalFrame A ⊤ e) (s : ι → Γ(N, ⊤))
    (V : X.Opens) (j : ι) :
    (hA.desc s).app V (A.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (e j)) =
      N.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (s j) := by
  rw [hA.desc_app, hA.coord_self, Finset.sum_eq_single j]
  · rw [Pi.single_eq_same, one_smul]
  · intro i _ hij
    rw [Pi.single_eq_of_ne hij, zero_smul]
  · intro h'; exact absurd (Finset.mem_univ j) h'

lemma IsLocalFrame.desc_app_frame_top [DecidableEq ι] (hA : IsLocalFrame A ⊤ e)
    (s : ι → Γ(N, ⊤)) (j : ι) : (hA.desc s).app ⊤ (e j) = s j := by
  have := hA.desc_app_frame s ⊤ j
  rwa [modules_map_self, modules_map_self] at this

/-- Two morphisms out of a module with a global frame agreeing on the frame are equal. -/
lemma IsLocalFrame.hom_ext_top (hA : IsLocalFrame A ⊤ e) {φ ψ : A ⟶ N}
    (h : ∀ i, φ.app ⊤ (e i) = ψ.app ⊤ (e i)) : φ = ψ := by
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  ext x
  rw [← hA.localFrameMap_coord (le_top : V ≤ ⊤) x, localFrameMap_apply, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul]
  congr 1
  have hφ := ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE (le_top : V ≤ ⊤)).op)
    (e i)
  have hψ := ConcreteCategory.congr_hom (ψ.mapPresheaf.naturality (homOfLE (le_top : V ≤ ⊤)).op)
    (e i)
  change φ.app V (A.presheaf.map _ (e i)) = N.presheaf.map _ (φ.app ⊤ (e i)) at hφ
  change ψ.app V (A.presheaf.map _ (e i)) = N.presheaf.map _ (ψ.app ⊤ (e i)) at hψ
  rw [hφ, hψ, h]

end FrameDesc

section PullbackFrame

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The unit `E ⟶ f_* f^* E` of the pullback–pushforward adjunction. -/
noncomputable abbrev pullbackUnit (E : Y.Modules) :
    E ⟶ (Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj E) :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app E

namespace PullbackFrame

variable {f} (U : Y.Opens)

lemma preimage_le (V : Y.Opens) :
    (f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ V) ≤ (f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ (V ⊓ U)) := by
  intro x hx
  exact ⟨hx, x.2⟩

lemma image_le (V : Y.Opens) :
    (f ⁻¹ᵁ U).ι ''ᵁ ((f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ V)) ≤ f ⁻¹ᵁ (V ⊓ U) :=
  ((f ⁻¹ᵁ U).ι.image_mono (preimage_le U V)).trans ((f ⁻¹ᵁ U).ι.image_preimage_le _)

lemma top_le : (⊤ : (f ⁻¹ᵁ U).toScheme.Opens) ≤ (f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ U) :=
  (Scheme.Opens.ι_preimage_self _).ge

/-- The ring map `Γ(Y, V ∩ U) → Γ(f⁻¹U, f⁻¹V)` used to transport coordinates. -/
noncomputable def ringMap (V : Y.Opens) :
    Γ(Y, V ⊓ U) ⟶ Γ((f ⁻¹ᵁ U).toScheme, (f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ V)) :=
  f.app (V ⊓ U) ≫ X.presheaf.map (homOfLE (image_le U V)).op ≫
    ((f ⁻¹ᵁ U).ι.appIso _).hom

lemma ringMap_map (V : Y.Opens) (r : Γ(Y, V)) :
    ringMap U V (Y.presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op r) =
      (f ⁻¹ᵁ U).ι.app (f ⁻¹ᵁ V) (f.app V r) := by
  have h1 : f.app (V ⊓ U) (Y.presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op r) =
      X.presheaf.map (homOfLE (f.preimage_mono (inf_le_left : V ⊓ U ≤ V))).op (f.app V r) := by
    rw [← ConcreteCategory.comp_apply, f.naturality, ConcreteCategory.comp_apply]
    rfl
  have h2 : ((f ⁻¹ᵁ U).ι.appIso ((f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ V))).inv
      ((f ⁻¹ᵁ U).ι.app (f ⁻¹ᵁ V) (f.app V r)) =
      X.presheaf.map (homOfLE ((f ⁻¹ᵁ U).ι.image_preimage_le _)).op (f.app V r) := by
    rw [← ConcreteCategory.comp_apply, Scheme.Hom.app_appIso_inv]
    rfl
  rw [← Iso.inv_hom_id_apply ((f ⁻¹ᵁ U).ι.appIso _) ((f ⁻¹ᵁ U).ι.app (f ⁻¹ᵁ V) (f.app V r)), h2]
  change ((f ⁻¹ᵁ U).ι.appIso _).hom (X.presheaf.map _ (f.app (V ⊓ U) _)) = _
  rw [h1, ring_map_map']

lemma ringMap_natural {V V' : Y.Opens} (i : V' ≤ V) (r : Γ(Y, V ⊓ U)) :
    ringMap U V' (Y.presheaf.map (homOfLE (inf_le_inf_right U i)).op r) =
      (f ⁻¹ᵁ U).toScheme.presheaf.map (homOfLE ((f ⁻¹ᵁ U).ι.preimage_mono
        (f.preimage_mono i))).op (ringMap U V r) := by
  change ((f ⁻¹ᵁ U).ι.appIso _).hom (X.presheaf.map _ (f.app (V' ⊓ U) _)) =
    (f ⁻¹ᵁ U).toScheme.presheaf.map _ (((f ⁻¹ᵁ U).ι.appIso _).hom (X.presheaf.map _
      (f.app (V ⊓ U) r)))
  rw [← ConcreteCategory.comp_apply (((f ⁻¹ᵁ U).ι.appIso _).hom),
    ← Scheme.Hom.appIso_hom_naturality, ConcreteCategory.comp_apply,
    ← ConcreteCategory.comp_apply (Y.presheaf.map _) (f.app _), f.naturality,
    ConcreteCategory.comp_apply,
    ring_map_map' _ _ (homOfLE ((image_le U V').trans (f.preimage_mono (inf_le_inf_right U i)))).op,
    ring_map_map' _ _ (homOfLE ((image_le U V').trans (f.preimage_mono (inf_le_inf_right U i)))).op]

variable {E : Y.Modules} {ι : Type u} [Fintype ι] [DecidableEq ι] {e : ι → Γ(E, U)}
  (hE : IsLocalFrame E U e)

variable (f)

/-- The section `∑ ρ(x_k) ⋅ ε_k` of the free module on `f⁻¹U`, where `x_k` are the coordinates of
`x|_{V ∩ U}` with respect to the frame `e`. -/
noncomputable def cSection (V : Y.Opens) (x : Γ(E, V)) :
    Γ(freeModule (f ⁻¹ᵁ U).toScheme ι, (f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ V)) :=
  ∑ k, (freeIncl k).app _
    (ringMap U V (hE.coord (inf_le_right : V ⊓ U ≤ U)
      (E.presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op x) k))

omit [DecidableEq ι] in
lemma cSection_add (V : Y.Opens) (x x' : Γ(E, V)) :
    cSection f U hE V (x + x') = cSection f U hE V x + cSection f U hE V x' := by
  simp only [cSection, map_add, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => map_add _ _ _

omit [DecidableEq ι] in
lemma cSection_smul (V : Y.Opens) (r : Γ(Y, V)) (x : Γ(E, V)) :
    cSection f U hE V (r • x) =
      (f ⁻¹ᵁ U).ι.app (f ⁻¹ᵁ V) (f.app V r) • cSection f U hE V x := by
  simp only [cSection]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Scheme.Modules.map_smul, map_smul, Pi.smul_apply, smul_eq_mul, map_mul, ringMap_map]
  exact Scheme.Modules.Hom.app_smul (freeIncl k) _ _

omit [DecidableEq ι] in
lemma cSection_restrict {V V' : Y.Opens} (i : V' ≤ V) (x : Γ(E, V)) :
    cSection f U hE V' (E.presheaf.map (homOfLE i).op x) =
      (freeModule (f ⁻¹ᵁ U).toScheme ι).presheaf.map (homOfLE ((f ⁻¹ᵁ U).ι.preimage_mono
        (f.preimage_mono i))).op (cSection f U hE V x) := by
  simp only [cSection]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hx : E.presheaf.map (homOfLE (inf_le_left : V' ⊓ U ≤ V')).op
      (E.presheaf.map (homOfLE i).op x) =
      E.presheaf.map (homOfLE (inf_le_inf_right U i)).op
        (E.presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op x) := by
    rw [modules_map_map' E _ _ (homOfLE ((inf_le_left : V' ⊓ U ≤ V').trans i)).op,
      modules_map_map' E _ _ (homOfLE ((inf_le_left : V' ⊓ U ≤ V').trans i)).op]
  rw [hx, hE.coord_restrict (inf_le_right : V ⊓ U ≤ U) (inf_le_inf_right U i), ringMap_natural U i]
  exact ConcreteCategory.congr_hom ((freeIncl k).mapPresheaf.naturality _) _

/-- The morphism `E ⟶ f_* j_* 𝒪^ι` attached to the frame `e`. -/
noncomputable def cHom : E ⟶ (Scheme.Modules.pushforward f).obj
    ((Scheme.Modules.pushforward (f ⁻¹ᵁ U).ι).obj (freeModule (f ⁻¹ᵁ U).toScheme ι)) :=
  modulesHomMk (fun V =>
    { toFun := cSection f U hE V
      map_add' := cSection_add f U hE V
      map_smul' := cSection_smul f U hE V })
    (fun V V' i x => cSection_restrict f U hE (V := V) (V' := V') i x)

lemma ringMap_eq (V : Y.Opens) (r : Γ(Y, V ⊓ U)) :
    ringMap U V r = (f ⁻¹ᵁ U).toScheme.presheaf.map (homOfLE (preimage_le U V)).op
      ((f ⁻¹ᵁ U).ι.app (f ⁻¹ᵁ (V ⊓ U)) (f.app (V ⊓ U) r)) := by
  rw [openImmersion_app_map]
  rfl

/-- The adjunction `f^*(-)|_{f⁻¹U} ⊣ f_* j_*`. -/
noncomputable abbrev adj :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).comp
    (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι)

lemma adj_unit_app (V : Y.Opens) (x : Γ(E, V)) :
    ((adj f U).unit.app E).app V x =
      ((Scheme.Modules.pullback f).obj E).presheaf.map
        (homOfLE ((f ⁻¹ᵁ U).ι.image_preimage_le (f ⁻¹ᵁ V))).op ((pullbackUnit f E).app V x) := by
  rw [Adjunction.comp_unit_app]
  rfl

lemma adj_unit_restrict {V₁ V₂ : Y.Opens} (i : V₂ ≤ V₁) (y : Γ(E, V₁)) :
    ((adj f U).unit.app E).app V₂ (E.presheaf.map (homOfLE i).op y) =
      (((Scheme.Modules.pullback f).obj E).restrict (f ⁻¹ᵁ U).ι).presheaf.map
        (homOfLE ((f ⁻¹ᵁ U).ι.preimage_mono (f.preimage_mono i))).op
        (((adj f U).unit.app E).app V₁ y) :=
  ConcreteCategory.congr_hom (((adj f U).unit.app E).mapPresheaf.naturality (homOfLE i).op) y

variable (E) in
/-- The restriction `(f^*E)|_{f⁻¹U}`. -/
noncomputable abbrev restrictedPullback : (f ⁻¹ᵁ U).toScheme.Modules :=
  ((Scheme.Modules.pullback f).obj E).restrict (f ⁻¹ᵁ U).ι

/-- The unit `E(V) → (f^*E)|_{f⁻¹U}(f⁻¹V)` on sections. -/
noncomputable def uSec (V : Y.Opens) (x : Γ(E, V)) :
    Γ(restrictedPullback f U E, (f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ V)) :=
  ((adj f U).unit.app E).app V x

lemma uSec_restrict {V₁ V₂ : Y.Opens} (i : V₂ ≤ V₁) (y : Γ(E, V₁)) :
    uSec f U V₂ (E.presheaf.map (homOfLE i).op y) =
      (restrictedPullback f U E).presheaf.map (homOfLE ((f ⁻¹ᵁ U).ι.preimage_mono (f.preimage_mono i))).op
        (uSec f U V₁ y) :=
  adj_unit_restrict f U i y

lemma uSec_smul (V : Y.Opens) (r : Γ(Y, V)) (y : Γ(E, V)) :
    uSec f U V (r • y) = (f ⁻¹ᵁ U).ι.app (f ⁻¹ᵁ V) (f.app V r) • uSec f U V y :=
  Scheme.Modules.Hom.app_smul _ _ _

omit [DecidableEq ι] in
lemma uSec_sum (V : Y.Opens) (y : ι → Γ(E, V)) :
    uSec f U V (∑ k, y k) = ∑ k, uSec f U V (y k) :=
  map_sum (ConcreteCategory.hom (((adj f U).unit.app E).app V)) _ _

/-- The sections `η(e_i)|_{f⁻¹U}` of `(f^*E)|_{f⁻¹U}`. -/
noncomputable def frameSec (e : ι → Γ(E, U)) (i : ι) : Γ(restrictedPullback f U E, ⊤) :=
  (restrictedPullback f U E).presheaf.map
    (homOfLE (top_le U)).op (uSec f U U (e i))

/-- The morphism `𝒪^ι ⟶ (f^*E)|_{f⁻¹U}` given by the sections `η(e_i)`. -/
noncomputable def fromFree (e : ι → Γ(E, U)) :
    freeModule (f ⁻¹ᵁ U).toScheme ι ⟶ ((Scheme.Modules.pullback f).obj E).restrict (f ⁻¹ᵁ U).ι :=
  (free_isLocalFrame (Y := (f ⁻¹ᵁ U).toScheme) (I := ι)).desc (frameSec f U e)

/-- The morphism `(f^*E)|_{f⁻¹U} ⟶ 𝒪^ι` adjoint to `cHom`. -/
noncomputable def toFree :
    ((Scheme.Modules.pullback f).obj E).restrict (f ⁻¹ᵁ U).ι ⟶ freeModule (f ⁻¹ᵁ U).toScheme ι :=
  ((adj f U).homEquiv E _).symm (cHom f U hE)

omit [DecidableEq ι] in
lemma toFree_unit (V : Y.Opens) (x : Γ(E, V)) :
    (toFree f U hE).app ((f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ V)) (uSec f U V x) =
      cSection f U hE V x := by
  have h := (adj f U).homEquiv_unit E _ (toFree f U hE)
  rw [toFree, Equiv.apply_symm_apply] at h
  exact (ConcreteCategory.congr_hom (congrArg (fun φ => Scheme.Modules.Hom.app φ V) h) x).symm

lemma fromFree_toFree : fromFree f U e ≫ toFree f U hE = 𝟙 _ := by
  refine (free_isLocalFrame (Y := (f ⁻¹ᵁ U).toScheme) (I := ι)).hom_ext_top fun i => ?_
  change (toFree f U hE).app ⊤ ((fromFree f U e).app ⊤ ((freeIncl (Y := (f ⁻¹ᵁ U).toScheme) (I := ι) i).app ⊤
      (1 : Γ((f ⁻¹ᵁ U).toScheme, ⊤)))) =
    (freeIncl (Y := (f ⁻¹ᵁ U).toScheme) (I := ι) i).app ⊤ (1 : Γ((f ⁻¹ᵁ U).toScheme, ⊤))
  rw [fromFree, IsLocalFrame.desc_app_frame_top, frameSec]
  have hn := ConcreteCategory.congr_hom
    ((toFree f U hE).mapPresheaf.naturality (homOfLE (top_le U)).op) (uSec f U U (e i))
  change (toFree f U hE).app ⊤ ((restrictedPullback f U E).presheaf.map _ (uSec f U U (e i))) =
    (freeModule _ ι).presheaf.map _ ((toFree f U hE).app _ (uSec f U U (e i))) at hn
  rw [hn, toFree_unit, cSection, hE.coord_self (inf_le_right : U ⊓ U ≤ U) i, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, map_one]
    have h2 := ConcreteCategory.congr_hom ((freeIncl (Y := (f ⁻¹ᵁ U).toScheme) (I := ι) i).mapPresheaf.naturality
      (homOfLE (top_le U)).op) (1 : Γ((f ⁻¹ᵁ U).toScheme, (f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ U)))
    change (freeIncl (Y := (f ⁻¹ᵁ U).toScheme) (I := ι) i).app ⊤
      ((f ⁻¹ᵁ U).toScheme.presheaf.map (homOfLE (top_le U)).op
        (1 : Γ((f ⁻¹ᵁ U).toScheme, (f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ U)))) =
      (freeModule _ ι).presheaf.map (homOfLE (top_le U)).op
        ((freeIncl (Y := (f ⁻¹ᵁ U).toScheme) (I := ι) i).app _
          (1 : Γ((f ⁻¹ᵁ U).toScheme, (f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ U)))) at h2
    refine h2.symm.trans ?_
    congr 1
    exact ((f ⁻¹ᵁ U).toScheme.presheaf.map (homOfLE (top_le U)).op).hom.map_one
  · intro k _ hk
    rw [Pi.single_eq_of_ne hk, map_zero]
    exact map_zero (ConcreteCategory.hom ((freeIncl (Y := (f ⁻¹ᵁ U).toScheme) (I := ι) k).app _))
  · intro h'; exact absurd (Finset.mem_univ i) h'

lemma toFree_fromFree : toFree f U hE ≫ fromFree f U e = 𝟙 _ := by
  apply ((adj f U).homEquiv E _).injective
  rw [Adjunction.homEquiv_naturality_right, toFree, Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  ext x
  change (fromFree f U e).app ((f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ V)) (cSection f U hE V x) = uSec f U V x
  have h1 : uSec f U V x = (restrictedPullback f U E).presheaf.map (homOfLE (preimage_le U V)).op
      (uSec f U (V ⊓ U) (E.presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op x)) := by
    rw [uSec_restrict, modules_map_map' (restrictedPullback f U E) _ _ (homOfLE (le_refl _)).op,
      modules_map_self]
  rw [h1]
  conv_rhs => rw [← hE.localFrameMap_coord (inf_le_right : V ⊓ U ≤ U)
    (E.presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op x), localFrameMap_apply, uSec_sum,
    map_sum]
  rw [cSection, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [freeIncl_app_eq, Scheme.Modules.Hom.app_smul, fromFree, IsLocalFrame.desc_app_frame, uSec_smul,
    Scheme.Modules.map_smul, ← ringMap_eq, uSec_restrict, frameSec,
    modules_map_map' (restrictedPullback f U E) _ _ (homOfLE ((le_top : (f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ V) ≤ ⊤).trans
      (top_le U))).op,
    modules_map_map' (restrictedPullback f U E) _ _ (homOfLE ((le_top : (f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ V) ≤ ⊤).trans
      (top_le U))).op]

end PullbackFrame

/-- **The pullback of a frame is a frame.** If `e` is a frame of the `𝒪_Y`-module `E` over `U`,
then the sections `η(e_i)` of `f^*E` over `f⁻¹U`, where `η : E ⟶ f_* f^* E` is the unit of the
adjunction, form a frame of `f^*E` over `f⁻¹U`. -/
theorem IsLocalFrame.pullback {E : Y.Modules} {U : Y.Opens} {ι : Type u} [Fintype ι]
    [DecidableEq ι] {e : ι → Γ(E, U)} (hE : IsLocalFrame E U e) :
    IsLocalFrame ((Scheme.Modules.pullback f).obj E) (f ⁻¹ᵁ U)
      (fun i => (pullbackUnit f E).app U (e i)) := by
  have hiso : IsIso (PullbackFrame.fromFree f U e) :=
    ⟨⟨PullbackFrame.toFree f U hE, PullbackFrame.fromFree_toFree f U hE, PullbackFrame.toFree_fromFree f U hE⟩⟩
  have h := ((free_isLocalFrame (Y := (f ⁻¹ᵁ U).toScheme) (I := ι)).of_iso
    (asIso (PullbackFrame.fromFree f U e))).of_restrict
  refine (congrArg (IsLocalFrame ((Scheme.Modules.pullback f).obj E) (f ⁻¹ᵁ U)) ?_).mpr h
  funext i
  change _ = ((Scheme.Modules.pullback f).obj E).presheaf.map
    (homOfLE (f ⁻¹ᵁ U).ι_image_top.ge).op ((PullbackFrame.fromFree f U e).app ⊤
      ((freeIncl (Y := (f ⁻¹ᵁ U).toScheme) (I := ι) i).app ⊤ (1 : Γ((f ⁻¹ᵁ U).toScheme, ⊤))))
  rw [PullbackFrame.fromFree, IsLocalFrame.desc_app_frame_top]
  show _ = ((Scheme.Modules.pullback f).obj E).presheaf.map
    (homOfLE (f ⁻¹ᵁ U).ι_image_top.ge).op (((Scheme.Modules.pullback f).obj E).presheaf.map
      ((f ⁻¹ᵁ U).ι.opensFunctor.map (homOfLE (PullbackFrame.top_le U))).op
      (((Scheme.Modules.pullback f).obj E).presheaf.map
        (homOfLE ((f ⁻¹ᵁ U).ι.image_preimage_le (f ⁻¹ᵁ U))).op ((pullbackUnit f E).app U (e i))))
  have key : ∀ y : Γ((Scheme.Modules.pullback f).obj E, f ⁻¹ᵁ U),
      y = ((Scheme.Modules.pullback f).obj E).presheaf.map
        (homOfLE (f ⁻¹ᵁ U).ι_image_top.ge).op (((Scheme.Modules.pullback f).obj E).presheaf.map
          ((f ⁻¹ᵁ U).ι.opensFunctor.map (homOfLE (PullbackFrame.top_le U))).op
          (((Scheme.Modules.pullback f).obj E).presheaf.map
            (homOfLE ((f ⁻¹ᵁ U).ι.image_preimage_le (f ⁻¹ᵁ U))).op y)) := fun y => by
    rw [modules_map_map' _ _ _ (homOfLE ((f ⁻¹ᵁ U).ι_image_le ⊤)).op,
      modules_map_map' _ _ _ (𝟙 _), modules_map_self]
  exact key _

end PullbackFrame

section ProjectionFormula

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (E : Y.Modules)

/-- The `𝒪_X`-module `F ⊗ f^*E`. -/
noncomputable abbrev pullbackTensor : X.Modules :=
  moduleSheafTensor F ((Scheme.Modules.pullback f).obj E)

variable {E} in
/-- The unit `η : E(V) → (f^*E)(f⁻¹V)` on sections. -/
noncomputable def etaSec {V : Y.Opens} (x : Γ(E, V)) :
    Γ((Scheme.Modules.pullback f).obj E, f ⁻¹ᵁ V) :=
  (pullbackUnit f E).app V x

/-- The section `s ⊗ η(x)` of `F ⊗ f^*E` over `f⁻¹V`. -/
noncomputable def projSec {V : Y.Opens} (s : Γ(F, f ⁻¹ᵁ V)) (x : Γ(E, V)) :
    Γ(pullbackTensor f F E, f ⁻¹ᵁ V) :=
  (moduleSheafTensorBilinear F ((Scheme.Modules.pullback f).obj E)).app (op (f ⁻¹ᵁ V)) s
    (etaSec f x)

variable {f F E}

lemma etaSec_add {V : Y.Opens} (x x' : Γ(E, V)) :
    etaSec f (x + x') = etaSec f x + etaSec f x' :=
  map_add (ConcreteCategory.hom ((pullbackUnit f E).app V)) x x'

lemma etaSec_smul {V : Y.Opens} (r : Γ(Y, V)) (x : Γ(E, V)) :
    etaSec f (r • x) = f.app V r • etaSec f x :=
  Scheme.Modules.Hom.app_smul _ _ _

lemma etaSec_restrict {V V' : Y.Opens} (i : V' ≤ V) (x : Γ(E, V)) :
    etaSec f (E.presheaf.map (homOfLE i).op x) =
      ((Scheme.Modules.pullback f).obj E).presheaf.map (homOfLE (f.preimage_mono i)).op
        (etaSec f x) :=
  ConcreteCategory.congr_hom ((pullbackUnit f E).mapPresheaf.naturality (homOfLE i).op) x

lemma projSec_add_left {V : Y.Opens} (s s' : Γ(F, f ⁻¹ᵁ V)) (x : Γ(E, V)) :
    projSec f F E (s + s') x = projSec f F E s x + projSec f F E s' x :=
  LinearMap.map_add₂ ((moduleSheafTensorBilinear F ((Scheme.Modules.pullback f).obj E)).app
    (op (f ⁻¹ᵁ V))) s s' (etaSec f x)

lemma projSec_smul_left {V : Y.Opens} (r : Γ(Y, V)) (s : Γ(F, f ⁻¹ᵁ V)) (x : Γ(E, V)) :
    projSec f F E (f.app V r • s) x = f.app V r • projSec f F E s x :=
  LinearMap.map_smul₂ ((moduleSheafTensorBilinear F ((Scheme.Modules.pullback f).obj E)).app
    (op (f ⁻¹ᵁ V))) (f.app V r) s (etaSec f x)

lemma projSec_add_right {V : Y.Opens} (s : Γ(F, f ⁻¹ᵁ V)) (x x' : Γ(E, V)) :
    projSec f F E s (x + x') = projSec f F E s x + projSec f F E s x' := by
  rw [projSec, etaSec_add]
  exact map_add (((moduleSheafTensorBilinear F ((Scheme.Modules.pullback f).obj E)).app
    (op (f ⁻¹ᵁ V))) s) _ _

lemma projSec_smul_right {V : Y.Opens} (r : Γ(Y, V)) (s : Γ(F, f ⁻¹ᵁ V)) (x : Γ(E, V)) :
    projSec f F E s (r • x) = f.app V r • projSec f F E s x := by
  rw [projSec, etaSec_smul]
  exact map_smul (((moduleSheafTensorBilinear F ((Scheme.Modules.pullback f).obj E)).app
    (op (f ⁻¹ᵁ V))) s) _ _

lemma projSec_restrict {V V' : Y.Opens} (i : V' ≤ V) (s : Γ(F, f ⁻¹ᵁ V)) (x : Γ(E, V)) :
    (pullbackTensor f F E).presheaf.map
        (homOfLE (f.preimage_mono i)).op (projSec f F E s x) =
      projSec f F E (F.presheaf.map (homOfLE (f.preimage_mono i)).op s)
        (E.presheaf.map (homOfLE i).op x) := by
  rw [projSec, projSec, etaSec_restrict]
  exact (moduleSheafTensorBilinear F _).naturality _ _ _

variable (f F E)

/-- The bilinear map `f_*F × E → f_*(F ⊗ f^*E)`, `(s, x) ↦ s ⊗ η(x)`. -/
noncomputable def projectionFormulaBilinear :
    ModuleSheafBilinear ((Scheme.Modules.pushforward f).obj F) E
      ((Scheme.Modules.pushforward f).obj (pullbackTensor f F E)) where
  app V := LinearMap.mk₂ _ (fun (s : Γ(F, f ⁻¹ᵁ V.unop)) (x : Γ(E, V.unop)) => projSec f F E s x)
    (fun s s' x => projSec_add_left s s' x)
    (fun r s x => projSec_smul_left r s x)
    (fun s x x' => projSec_add_right s x x')
    (fun r s x => projSec_smul_right r s x)
  naturality {V V'} i s x := projSec_restrict (V := V.unop) (V' := V'.unop) (leOfHom i.unop) s x

/-- **The projection-formula map** `f_*F ⊗ E ⟶ f_*(F ⊗ f^*E)`, `s ⊗ x ↦ s ⊗ η(x)`, where
`η : E ⟶ f_* f^* E` is the unit of the pullback–pushforward adjunction. -/
noncomputable def projectionFormulaMap :
    @Quiver.Hom Y.Modules _ (moduleSheafTensor ((Scheme.Modules.pushforward f).obj F) E)
      ((Scheme.Modules.pushforward f).obj (pullbackTensor f F E)) :=
  (moduleSheafTensorHomEquiv _ _ _).symm (projectionFormulaBilinear f F E)

variable {f F E}

lemma projectionFormulaMap_tmul {V : Y.Opens} (s : Γ(F, f ⁻¹ᵁ V)) (x : Γ(E, V)) :
    (projectionFormulaMap f F E).val.app (op V)
        ((moduleSheafTensorBilinear ((Scheme.Modules.pushforward f).obj F) E).app (op V) s x) =
      projSec f F E s x := by
  have := congrArg (fun β : ModuleSheafBilinear _ _ _ => β.app (op V) s x)
    ((moduleSheafTensorHomEquiv_apply (projectionFormulaMap f F E)).symm.trans
      (Equiv.apply_symm_apply (moduleSheafTensorHomEquiv _ _ _) (projectionFormulaBilinear f F E)))
  exact this

lemma projectionFormulaMap_presheaf_bijective {U : Y.Opens} {ι : Type u} [Fintype ι]
    [DecidableEq ι] {e : ι → Γ(E, U)} (hE : IsLocalFrame E U e) {V : Y.Opens} (h : V ≤ U) :
    Function.Bijective (((PresheafOfModules.toPresheaf _).map
      (moduleSheafTensorUnit ((Scheme.Modules.pushforward f).obj F) E ≫
        (projectionFormulaMap f F E).val)).app (op V)) := by
  have h1 := sum_tmul_frame_bijective (R := Γ(Y, V)) (M := Γ((Scheme.Modules.pushforward f).obj F, V))
    (N := Γ(E, V)) (fun j => E.presheaf.map (homOfLE h).op (e j)) (hE.coord h).toLinearMap
    (fun n => by
      rw [← localFrameMap_apply]
      exact hE.localFrameMap_coord h n)
    (fun i => hE.coord_self h i)
  have h3 := (hE.pullback f).tensorFrameMap_bijective (F := F) (f.preimage_mono h)
  let P' : TensorProduct Γ(Y, V) Γ((Scheme.Modules.pushforward f).obj F, V) Γ(E, V) →+
      Γ((Scheme.Modules.pushforward f).obj (pullbackTensor f F E), V) :=
    (((PresheafOfModules.toPresheaf _).map
      (moduleSheafTensorUnit ((Scheme.Modules.pushforward f).obj F) E ≫
        (projectionFormulaMap f F E).val)).app (op V)).hom
  have h2 : ⇑P' ∘ (fun m : ι → Γ((Scheme.Modules.pushforward f).obj F, V) =>
        ∑ i, m i ⊗ₜ[Γ(Y, V)] E.presheaf.map (homOfLE h).op (e i)) =
      tensorFrameMap F (fun i => (pullbackUnit f E).app U (e i)) (f.preimage_mono h) := by
    funext m
    rw [Function.comp_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    change (projectionFormulaMap f F E).val.app (op V)
        ((moduleSheafTensorBilinear ((Scheme.Modules.pushforward f).obj F) E).app (op V) (m i)
          (E.presheaf.map (homOfLE h).op (e i))) = _
    refine (projectionFormulaMap_tmul (m i) (E.presheaf.map (homOfLE h).op (e i))).trans ?_
    exact congrArg (((moduleSheafTensorBilinear F ((Scheme.Modules.pullback f).obj E)).app
      (op (f ⁻¹ᵁ V))) (m i)) (etaSec_restrict h (e i))
  rw [← h2] at h3
  exact (Function.Bijective.of_comp_iff P' h1).mp h3

/-- **Hartshorne II, Exercise 5.1(d): the projection formula.** For a morphism of schemes
`f : X ⟶ Y`, an `𝒪_X`-module `F` and a finite locally free `𝒪_Y`-module `E`, the canonical map
`f_*F ⊗ E ⟶ f_*(F ⊗ f^*E)` is an isomorphism. -/
theorem projectionFormulaMap_isIso (hE : E.IsLocallyFree)
    (hfin : ∀ y, E.rankAt y < Cardinal.aleph0) : IsIso (projectionFormulaMap f F E) :=
  modules_isIso_of_locally_bijective _ fun y => by
    classical
    obtain ⟨U, ι, _, e, hy, hEU⟩ := exists_isLocalFrame_of_isLocallyFree hE hfin y
    exact ⟨U, hy, fun V hV => tensor_app_bijective_of_presheaf _
      (fun V' hV' => projectionFormulaMap_presheaf_bijective hEU hV') hV⟩

variable (f F E) in
/-- **Hartshorne II, Exercise 5.1(d).** The natural isomorphism
`f_*(F ⊗ f^*E) ≅ f_*F ⊗ E` for a finite locally free `𝒪_Y`-module `E`, inverse to the
projection-formula map. -/
noncomputable def projectionFormulaIso (hE : E.IsLocallyFree)
    (hfin : ∀ y, E.rankAt y < Cardinal.aleph0) :
    @Iso Y.Modules _ ((Scheme.Modules.pushforward f).obj (pullbackTensor f F E))
      (moduleSheafTensor ((Scheme.Modules.pushforward f).obj F) E) :=
  haveI := projectionFormulaMap_isIso (f := f) (F := F) hE hfin
  (asIso (projectionFormulaMap f F E)).symm

/-- The projection-formula map is natural in `F`. -/
lemma projectionFormulaMap_naturality_left {F' : X.Modules} (φ : F ⟶ F') :
    modulesTensorMap ((Scheme.Modules.pushforward f).map φ) (𝟙 E) ≫
        projectionFormulaMap f F' E =
      projectionFormulaMap f F E ≫
        (Scheme.Modules.pushforward f).map (modulesTensorMap φ (𝟙 ((Scheme.Modules.pullback f).obj E))) := by
  refine modulesTensor_hom_ext fun V s x => ?_
  change (projectionFormulaMap f F' E).app V ((modulesTensorMap ((Scheme.Modules.pushforward f).map φ)
      (𝟙 E)).app V ((moduleSheafTensorBilinear _ E).app (op V) s x)) =
    (modulesTensorMap φ (𝟙 ((Scheme.Modules.pullback f).obj E))).app (f ⁻¹ᵁ V)
      ((projectionFormulaMap f F E).app V ((moduleSheafTensorBilinear _ E).app (op V) s x))
  rw [modulesTensorMap_tmul]
  refine (projectionFormulaMap_tmul (f := f) (F := F') (E := E) (φ.app (f ⁻¹ᵁ V) s) x).trans ?_
  refine Eq.trans ?_ (congrArg (fun t => (modulesTensorMap φ
    (𝟙 ((Scheme.Modules.pullback f).obj E))).app (f ⁻¹ᵁ V) t)
    (projectionFormulaMap_tmul (f := f) (F := F) (E := E) s x)).symm
  exact (modulesTensorMap_tmul φ (𝟙 _) s (etaSec f x)).symm

lemma etaSec_naturality {E' : Y.Modules} (g : E ⟶ E') {V : Y.Opens} (x : Γ(E, V)) :
    etaSec f (g.app V x) = ((Scheme.Modules.pullback f).map g).app (f ⁻¹ᵁ V) (etaSec f x) := by
  have h := (Scheme.Modules.pullbackPushforwardAdjunction f).unit_naturality g
  exact (ConcreteCategory.congr_hom (congrArg (fun φ => Scheme.Modules.Hom.app φ V) h) x).symm

/-- The projection-formula map is natural in `E`. -/
lemma projectionFormulaMap_naturality_right {E' : Y.Modules} (g : E ⟶ E') :
    modulesTensorMap (𝟙 ((Scheme.Modules.pushforward f).obj F)) g ≫
        projectionFormulaMap f F E' =
      projectionFormulaMap f F E ≫
        (Scheme.Modules.pushforward f).map
          (modulesTensorMap (𝟙 F) ((Scheme.Modules.pullback f).map g)) := by
  refine modulesTensor_hom_ext fun V s x => ?_
  change (projectionFormulaMap f F E').app V ((modulesTensorMap
      (𝟙 ((Scheme.Modules.pushforward f).obj F)) g).app V
        ((moduleSheafTensorBilinear _ E).app (op V) s x)) =
    (modulesTensorMap (𝟙 F) ((Scheme.Modules.pullback f).map g)).app (f ⁻¹ᵁ V)
      ((projectionFormulaMap f F E).app V ((moduleSheafTensorBilinear _ E).app (op V) s x))
  rw [modulesTensorMap_tmul]
  refine (projectionFormulaMap_tmul (f := f) (F := F) (E := E') s (g.app V x)).trans ?_
  refine Eq.trans ?_ (congrArg (fun t => (modulesTensorMap (𝟙 F)
    ((Scheme.Modules.pullback f).map g)).app (f ⁻¹ᵁ V) t)
    (projectionFormulaMap_tmul (f := f) (F := F) (E := E) s x)).symm
  refine Eq.trans ?_ (modulesTensorMap_tmul (𝟙 F) ((Scheme.Modules.pullback f).map g) s
    (etaSec f x)).symm
  exact congrArg (((moduleSheafTensorBilinear F ((Scheme.Modules.pullback f).obj E')).app
    (op (f ⁻¹ᵁ V))) s) (etaSec_naturality g x)

end ProjectionFormula

end Hartshorne

/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.RingedSpace.FiniteLocallyFreeDuality
import Hartshorne.RingedSpace.OpenRestriction

/-!
# The projection formula for finite locally free sheaves

Hartshorne, *Algebraic Geometry*, II, Exercise 5.1(d).

Let `(X, 𝒪_X)` and `(Y, 𝒪_Y)` be ringed spaces, given by sheaves of commutative rings `R` on `X`
and `S` on `Y`, and let `f : X ⟶ Y` be a morphism of ringed spaces: a continuous map together with
a morphism `φ : 𝒪_Y ⟶ f_* 𝒪_X` of sheaves of rings. Modules are `SheafOfModules (ringCatSheafOf R)`
and `SheafOfModules (ringCatSheafOf S)`, with Mathlib's pushforward `SheafOfModules.pushforward φ`
and pullback `SheafOfModules.pullback φ`. Write `η : E ⟶ f_* f^* E` for the unit of the
pullback–pushforward adjunction (`pullbackUnit`). For an `𝒪_X`-module `F` and an `𝒪_Y`-module
`E`, the *projection-formula map* `projectionFormulaMap φ F E : f_*F ⊗ E ⟶ f_*(F ⊗ f^*E)` is
induced by the bilinear map `(s, x) ↦ s ⊗ η(x)`; it is natural in `F`
(`projectionFormulaMap_naturality_left`) and in `E` (`projectionFormulaMap_naturality_right`).
The main result is

* `projectionFormulaMap_isIso`: if `E` is finite locally free (`IsFiniteLocallyFree E`), the
  projection-formula map is an isomorphism; `projectionFormulaIso` is the resulting natural
  isomorphism `f_*(F ⊗ f^*E) ≅ f_*F ⊗ E`.

For a morphism of schemes, take `φ := f.toRingCatSheafHom`.

## Proof

The argument is local on `Y`, using the frames (`IsLocalFrame`) of
`Hartshorne.RingedSpace.FiniteLocallyFreeDuality`.

* `IsLocalFrame.pullback`: if `e` is a frame of `E` over `U`, then `η(e_i)` is a frame of `f^*E`
  over `f⁻¹U`. The morphism `𝒪^ι ⟶ (f^*E)|_{f⁻¹U}` given by the `η(e_i)`
  (`PullbackFrame.fromFree`) is an isomorphism: its inverse (`PullbackFrame.toFree`) is adjoint,
  for the adjunction `f^*(-)|_{f⁻¹U} ⊣ f_* j_*` built from the pullback–pushforward adjunction and
  `restrictionAdjunction`, to the morphism `E ⟶ f_* j_* 𝒪^ι` (`PullbackFrame.cHom`) sending a
  section to its coordinates pulled back along `f`.
* `IsLocalFrame.tensorFrameMap_bijective`: if `b` is a frame of `A` over `W`, then on every open
  `V ⊆ W` the map `F(V)^ι → (F ⊗ A)(V)`, `(s_i) ↦ ∑ s_i ⊗ b_i`, is bijective. This is proved by
  comparing `F ⊗ A` with `ℋom(A^∨, F)` through the pairing `A ⟶ A^∨∨`.
* On an open `V ⊆ U` the presheaf-level projection map `F(f⁻¹V) ⊗ E(V) → (F ⊗ f^*E)(f⁻¹V)` is the
  composite of the bijection `F(f⁻¹V)^ι ≅ F(f⁻¹V) ⊗ E(V)` with the bijection of the previous item
  for the frame `η(e_i)`, so it is bijective; since sheafification does not change stalks, the
  projection-formula map is bijective on stalks, hence an isomorphism.

The pushforward of presheaves of modules along `φ` has a left adjoint by Mathlib's general
construction; instance search does not find it for `ringCatSheafOf`, so this file records the
instance explicitly.
-/

universe u

open CategoryTheory Opposite TopologicalSpace Limits
open scoped TensorProduct

namespace Hartshorne

namespace Ringed

section Helpers

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

set_option hygiene false in
/-- `𝒪_X`-modules. -/
local notation "𝓜" => SheafOfModules.{u} (ringCatSheafOf R)

set_option hygiene false in
/-- Sections of the structure sheaf over an open. -/
local notation3 "𝒪(" U ")" => R.obj.obj (Opposite.op U)

/-- Sections of a module sheaf over an open, as an abelian group. -/
local notation3 "Γ(" M ", " U ")" => (PresheafOfModules.presheaf (SheafOfModules.val M)).obj
  (Opposite.op U)

private lemma modules_map_map' (A : 𝓜) {U V W : Opens X} (g : op U ⟶ op V) (g' : op V ⟶ op W)
    (g'' : op U ⟶ op W) (x : Γ(A, U)) :
    A.val.presheaf.map g' (A.val.presheaf.map g x) = A.val.presheaf.map g'' x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, Subsingleton.elim (g ≫ g') g'']

private lemma modules_map_self (A : 𝓜) {U : Opens X} (g : op U ⟶ op U) (x : Γ(A, U)) :
    A.val.presheaf.map g x = x := by
  rw [Subsingleton.elim g (𝟙 _), CategoryTheory.Functor.map_id]
  rfl

private lemma hom_app_smul {A B : 𝓜} (φ : A ⟶ B) (U : Opens X) (r : 𝒪(U)) (x : Γ(A, U)) :
    sectionsMap φ U (r • x) = r • sectionsMap φ U x :=
  (φ.val.app (op U)).hom.map_smul r x

private lemma hom_naturality {A B : 𝓜} (φ : A ⟶ B) {U V : Opens X} (i : V ≤ U) (x : Γ(A, U)) :
    sectionsMap φ V (A.val.presheaf.map (homOfLE i).op x) =
      B.val.presheaf.map (homOfLE i).op (sectionsMap φ U x) :=
  ConcreteCategory.congr_hom ((modulesMapPresheaf φ).naturality (homOfLE i).op) x

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
lemma tensor_app_bijective_of_presheaf {F G H : 𝓜} (φ : moduleSheafTensor F G ⟶ H) {W : Opens X}
    (hφ : ∀ V : Opens X, V ≤ W → Function.Bijective
      (((PresheafOfModules.toPresheaf _).map (moduleSheafTensorUnit F G ≫ φ.val)).app (op V)))
    {V : Opens X} (hV : V ≤ W) : Function.Bijective (sectionsMap φ V) := by
  have hst : ∀ x ∈ V, Function.Bijective
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (modulesMapPresheaf φ)) := by
    intro x hx
    have h1 := stalk_bijective_of_locally_bijective' _ (hV hx) hφ
    have h2 := ModuleSheafTensor.moduleSheafTensorUnitStalk_bijective F G x
    have hc : (PresheafOfModules.toPresheaf _).map (moduleSheafTensorUnit F G ≫ φ.val) =
        @CategoryStruct.comp (TopCat.Presheaf AddCommGrpCat.{u} X) _ _ _ _
          (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
            (moduleSheafTensorPresheaf F G).presheaf)
          (modulesMapPresheaf φ) :=
      (PresheafOfModules.toPresheaf _).map_comp _ _
    have e := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map_comp
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        (moduleSheafTensorPresheaf F G).presheaf)
      (modulesMapPresheaf φ)
    rw [hc] at h1
    erw [e] at h1
    exact (Function.Bijective.of_comp_iff _ h2).mp h1
  let T : 𝓜 := moduleSheafTensor F G
  let f : (⟨T.val.presheaf, T.isSheaf⟩ :
      TopCat.Sheaf AddCommGrpCat.{u} X) ⟶ ⟨H.val.presheaf, H.isSheaf⟩ := ⟨modulesMapPresheaf φ⟩
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

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

set_option hygiene false in
/-- `𝒪_X`-modules. -/
local notation "𝓜" => SheafOfModules.{u} (ringCatSheafOf R)

set_option hygiene false in
/-- Sections of the structure sheaf over an open. -/
local notation3 "𝒪(" U ")" => R.obj.obj (Opposite.op U)

/-- Sections of a module sheaf over an open, as an abelian group. -/
local notation3 "Γ(" M ", " U ")" => (PresheafOfModules.presheaf (SheafOfModules.val M)).obj
  (Opposite.op U)

section Pairing

variable {F A B : 𝓜} (p : A ⟶ moduleSheafDual B)

lemma dualTensorSection_app_add {U : Opens X} (s : Γ(F, U)) (a a' : Γ(A, U)) :
    dualTensorSection (sectionsMap p U (a + a')) s =
      dualTensorSection (sectionsMap p U a) s + dualTensorSection (sectionsMap p U a') s := by
  rw [map_add, dualTensorSection_add_left]

lemma dualTensorSection_app_smul {U : Opens X} (r : 𝒪(U)) (s : Γ(F, U)) (a : Γ(A, U)) :
    dualTensorSection (sectionsMap p U (r • a)) s = r • dualTensorSection (sectionsMap p U a) s := by
  rw [hom_app_smul, dualTensorSection_smul_left]

lemma dualTensorSection_app_restrict {U V : Opens X} (i : V ≤ U) (s : Γ(F, U)) (a : Γ(A, U)) :
    (moduleSheafHom B F).val.presheaf.map (homOfLE i).op
        (dualTensorSection (sectionsMap p U a) s) =
      dualTensorSection (sectionsMap p V (A.val.presheaf.map (homOfLE i).op a))
        (F.val.presheaf.map (homOfLE i).op s) := by
  rw [dualTensorSection_restrict, hom_naturality]

variable (F) in
/-- The bilinear map `F × A → ℋom(B, F)`, `(s, a) ↦ (x ↦ p(a)(x) s)`, attached to a pairing
`p : A ⟶ B^∨`. -/
noncomputable def pairingTensorBilinear : ModuleSheafBilinear F A (moduleSheafHom B F) where
  app U := LinearMap.mk₂ _
    (fun (s : Γ(F, U.unop)) (a : Γ(A, U.unop)) => dualTensorSection (sectionsMap p U.unop a) s)
    (fun s s' a => dualTensorSection_add_right (sectionsMap p U.unop a) s s')
    (fun r s a => dualTensorSection_smul_right r (sectionsMap p U.unop a) s)
    (fun s a a' => dualTensorSection_app_add p s a a')
    (fun r s a => dualTensorSection_app_smul p r s a)
  naturality {_ _} i s a := dualTensorSection_app_restrict p (leOfHom i.unop) s a

variable (F) in
/-- The morphism `F ⊗ A ⟶ ℋom(B, F)` attached to a pairing `p : A ⟶ B^∨`. -/
noncomputable def pairingTensorMap : moduleSheafTensor F A ⟶ moduleSheafHom B F :=
  (moduleSheafTensorHomEquiv _ _ _).symm (pairingTensorBilinear F p)

lemma pairingTensorMap_tmul {U : Opens X} (s : Γ(F, U)) (a : Γ(A, U)) :
    (pairingTensorMap F p).val.app (op U) ((moduleSheafTensorBilinear F A).app (op U) s a) =
      dualTensorSection (sectionsMap p U a) s := by
  have := congrArg (fun β : ModuleSheafBilinear _ _ _ => β.app (op U) s a)
    ((moduleSheafTensorHomEquiv_apply (pairingTensorMap F p)).symm.trans
      (Equiv.apply_symm_apply (moduleSheafTensorHomEquiv _ _ _) (pairingTensorBilinear F p)))
  exact this

end Pairing

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma localFrameEval_dualTensorSection {F B : 𝓜} {W : Opens X} (c : ι → Γ(B, W))
    {V : Opens X} (h : V ≤ W) (ψ : Γ(moduleSheafDual B, V)) (s : Γ(F, V)) :
    localFrameEval c h (dualTensorSection ψ s) =
      fun j => (show 𝒪(V) from localFrameEval c h ψ j) • s := by
  funext j
  rw [localFrameEval_apply, dualTensorSection_eval, modules_map_self]
  rfl

variable (F : 𝓜) {A : 𝓜} {W : Opens X} (b : ι → Γ(A, W)) in
/-- The map `F(V)^ι → (F ⊗ A)(V)`, `(s_i) ↦ ∑ s_i ⊗ b_i|_V`, attached to a family `b` of
sections of `A` over `W ⊇ V`. -/
noncomputable def tensorFrameMap {V : Opens X} (h : V ≤ W) (s : ι → Γ(F, V)) :
    Γ(moduleSheafTensor F A, V) :=
  ∑ i, (moduleSheafTensorBilinear F A).app (op V) (s i) (A.val.presheaf.map (homOfLE h).op (b i))

/-- If `b` is a frame of `A` over `W` and `p : A ⟶ B^∨` identifies the coordinates with respect
to `b` with the values on a frame `c` of `B`, then `(s_i) ↦ ∑ s_i ⊗ b_i` is bijective on every open
`V ⊆ W`. -/
lemma tensorFrameMap_bijective_of_pairing {F A B : 𝓜} {W : Opens X} {b : ι → Γ(A, W)}
    (hb : IsLocalFrame A W b) {c : ι → Γ(B, W)} (hc : IsLocalFrame B W c)
    (p : A ⟶ moduleSheafDual B)
    (hp : ∀ (V : Opens X) (h : V ≤ W) (a : Γ(A, V)),
      localFrameEval c h (sectionsMap p V a) = hb.coord h a)
    {V : Opens X} (h : V ≤ W) :
    Function.Bijective (tensorFrameMap F b h) := by
  have hΛ : ∀ V' : Opens X, V' ≤ W → Function.Bijective
      (((PresheafOfModules.toPresheaf _).map
        (moduleSheafTensorUnit F A ≫ (pairingTensorMap F p).val)).app (op V')) := by
    intro V' h'
    refine (Function.Bijective.of_comp_iff' (hc.localFrameEval_bijective (G := F) h') _).mp ?_
    let Φ : TensorProduct 𝒪(V') Γ(F, V') Γ(A, V') →+ (ι → Γ(F, V')) :=
      (localFrameEval c h').toAddMonoidHom.comp
        (((PresheafOfModules.toPresheaf _).map
          (moduleSheafTensorUnit F A ≫ (pairingTensorMap F p).val)).app (op V')).hom
    have := tensor_frame_right_bijective (R := 𝒪(V')) (M := Γ(F, V')) (N := Γ(A, V'))
      (fun j => A.val.presheaf.map (homOfLE h').op (b j)) (hb.coord h').toLinearMap
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
      (localFrameEval (G := F) c h ∘ sectionsMap (pairingTensorMap F p) V) :=
    (hc.localFrameEval_bijective (G := F) h).comp (tensor_app_bijective_of_presheaf _ hΛ h)
  refine (Function.Bijective.of_comp_iff' hbij _).mp ?_
  have hid : (localFrameEval (G := F) c h ∘ sectionsMap (pairingTensorMap F p) V) ∘
      tensorFrameMap F b h = id := by
    funext s
    change localFrameEval c h ((pairingTensorMap F p).val.app (op V)
      (∑ i, (moduleSheafTensorBilinear F A).app (op V) (s i)
        (A.val.presheaf.map (homOfLE h).op (b i)))) = s
    have hterm : ∀ i, localFrameEval c h ((pairingTensorMap F p).val.app (op V)
        ((moduleSheafTensorBilinear F A).app (op V) (s i)
          (A.val.presheaf.map (homOfLE h).op (b i)))) =
        fun j => (show 𝒪(V) from (Pi.single i 1 : ι → 𝒪(V)) j) • s i := by
      intro i
      rw [pairingTensorMap_tmul, localFrameEval_dualTensorSection, hp, hb.coord_self]
    rw [map_sum]
    erw [map_sum]
    refine (Finset.sum_congr rfl fun i _ => hterm i).trans ?_
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
lemma IsLocalFrame.tensorFrameMap_bijective {F A : 𝓜} {W : Opens X} {b : ι → Γ(A, W)}
    (hb : IsLocalFrame A W b) {V : Opens X} (h : V ≤ W) :
    Function.Bijective (tensorFrameMap F b h) :=
  tensorFrameMap_bijective_of_pairing hb hb.dual (moduleSheafDoubleDualMap A) (fun V' h' a => by
    conv_lhs => rw [← hb.localFrameMap_coord h' a]
    exact localFrameEval_doubleDualMap hb h' _) h

end TensorFrame

section PullbackFrame

/-- Sections of a module sheaf over an open, as an abelian group. -/
local notation3 "Γ(" M ", " U ")" => (PresheafOfModules.presheaf (SheafOfModules.val M)).obj
  (Opposite.op U)

variable {X Y : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {S : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}} {f : X ⟶ Y}
  (φ : ringCatSheafOf S ⟶
    ((Opens.map f).sheafPushforwardContinuous RingCat.{u} _ _).obj (ringCatSheafOf R))

/-- The pushforward of presheaves of modules along a morphism of ringed spaces has a left
adjoint. -/
instance : (PresheafOfModules.pushforward.{u} φ.hom).IsRightAdjoint :=
  Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
    (PresheafOfModules.pullbackObjIsDefined_eq_top φ.hom)

/-- The unit `E ⟶ f_* f^* E` of the pullback–pushforward adjunction. -/
noncomputable abbrev pullbackUnit (E : SheafOfModules.{u} (ringCatSheafOf S)) :
    E ⟶ (SheafOfModules.pushforward.{u} φ).obj ((SheafOfModules.pullback.{u} φ).obj E) :=
  (SheafOfModules.pullbackPushforwardAdjunction.{u} φ).unit.app E

/-- The value of the ring map `𝒪_Y(W) → 𝒪_X(f⁻¹W)` of a morphism of ringed spaces. -/
noncomputable def phiApp (W : Opens Y) :
    S.obj.obj (op W) →+* R.obj.obj (op ((Opens.map f).obj W)) :=
  (φ.hom.app (op W)).hom

variable {φ} in
/-- The unit `η : E(W) → (f^*E)(f⁻¹W)` on sections. -/
noncomputable def etaSec {E : SheafOfModules.{u} (ringCatSheafOf S)} {W : Opens Y} (x : Γ(E, W)) :
    Γ((SheafOfModules.pullback.{u} φ).obj E, (Opens.map f).obj W) :=
  sectionsMap (pullbackUnit φ E) W x

variable {φ}

lemma etaSec_add {E : SheafOfModules.{u} (ringCatSheafOf S)} {W : Opens Y} (x x' : Γ(E, W)) :
    etaSec (φ := φ) (x + x') = etaSec x + etaSec x' :=
  (sectionsMap (pullbackUnit φ E) W).hom.map_add x x'

lemma etaSec_smul {E : SheafOfModules.{u} (ringCatSheafOf S)} {W : Opens Y} (r : S.obj.obj (op W))
    (x : Γ(E, W)) : etaSec (φ := φ) (r • x) = phiApp φ W r • etaSec x :=
  ((pullbackUnit φ E).val.app (op W)).hom.map_smul r x

lemma etaSec_restrict {E : SheafOfModules.{u} (ringCatSheafOf S)} {W W' : Opens Y} (i : W' ≤ W)
    (x : Γ(E, W)) :
    etaSec (φ := φ) (E.val.presheaf.map (homOfLE i).op x) =
      ((SheafOfModules.pullback.{u} φ).obj E).val.presheaf.map
        (homOfLE ((Opens.map f).monotone i)).op (etaSec x) :=
  ConcreteCategory.congr_hom ((modulesMapPresheaf (pullbackUnit φ E)).naturality (homOfLE i).op) x

private lemma modules_hom_ext' {T : TopCat.{u}} {Q : Sheaf (Opens.grothendieckTopology T) CommRingCat.{u}}
    {A B : SheafOfModules.{u} (ringCatSheafOf Q)} {g g' : A ⟶ B}
    (h : ∀ (W : Opens T) (x : Γ(A, W)), sectionsMap g W x = sectionsMap g' W x) : g = g' := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  ext x
  exact h W.unop x

private lemma ring_map_map' {T : TopCat.{u}} {Q : Sheaf (Opens.grothendieckTopology T) CommRingCat.{u}}
    {U V W : Opens T} (g : op U ⟶ op V) (g' : op V ⟶ op W) (g'' : op U ⟶ op W)
    (r : Q.obj.obj (op U)) : Q.obj.map g' (Q.obj.map g r) = Q.obj.map g'' r := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, Subsingleton.elim (g ≫ g') g'']

lemma phiApp_map {W W' : Opens Y} (i : W' ≤ W) (r : S.obj.obj (op W)) :
    phiApp φ W' (S.obj.map (homOfLE i).op r) =
      R.obj.map (homOfLE ((Opens.map f).monotone i)).op (phiApp φ W r) :=
  ConcreteCategory.congr_hom (φ.hom.naturality (homOfLE i).op) r

/-- The section of `M|_V` on the opens of `V` given by restricting a section over `V`. -/
private noncomputable def overSection' {M : SheafOfModules.{u} (ringCatSheafOf R)} {V : Opens X}
    (s : Γ(M, V)) : (M.over V).sections :=
  PresheafOfModules.sectionsMk
    (fun A => (show (M.over V).val.obj A from M.val.presheaf.map A.unop.hom.op s))
    (fun A B g => by
      change M.val.presheaf.map g.unop.left.op (M.val.presheaf.map A.unop.hom.op s) =
        M.val.presheaf.map B.unop.hom.op s
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, Over.w g.unop])

/-- The morphism `𝒪_V^{⊕ I} ⟶ M|_V` sending the `i`-th basis vector to `s i`. -/
private noncomputable def frameHom' {I : Type u} {M : SheafOfModules.{u} (ringCatSheafOf R)}
    {V : Opens X} (s : I → Γ(M, V)) :
    (SheafOfModules.free I : SheafOfModules.{u} ((ringCatSheafOf R).over V)) ⟶ M.over V :=
  (M.over V).freeHomEquiv.symm (fun i => overSection' (s i))

private lemma frameHom'_ιFree {I : Type u} {M : SheafOfModules.{u} (ringCatSheafOf R)}
    {V : Opens X} (s : I → Γ(M, V)) (i : I) (A : (Over V)ᵒᵖ) :
    (frameHom' s).val.app A
        ((SheafOfModules.ιFree (R := (ringCatSheafOf R).over V) (I := I) i).val.app A
          (show (SheafOfModules.unit ((ringCatSheafOf R).over V)).val.obj A from
            (1 : R.obj.obj (op A.unop.left)))) =
      M.val.presheaf.map A.unop.hom.op (s i) := by
  have h : (M.over V).freeHomEquiv (frameHom' s) i = overSection' (s i) := by
    simp only [frameHom', Equiv.apply_symm_apply]
  exact congrArg (fun t : (M.over V).sections => t.1 A) h

private lemma ιFree_app_smul_one' {V : Opens X} {I : Type u} (i : I) (A : (Over V)ᵒᵖ)
    (r : R.obj.obj (op A.unop.left)) :
    (SheafOfModules.ιFree (R := (ringCatSheafOf R).over V) (I := I) i).val.app A
        (show (SheafOfModules.unit ((ringCatSheafOf R).over V)).val.obj A from r) =
      r • (SheafOfModules.ιFree (R := (ringCatSheafOf R).over V) (I := I) i).val.app A
        (show (SheafOfModules.unit ((ringCatSheafOf R).over V)).val.obj A from
          (1 : R.obj.obj (op A.unop.left))) := by
  have h :=
    ((SheafOfModules.ιFree (R := (ringCatSheafOf R).over V) (I := I) i).val.app A).hom.map_smul
    r (show (SheafOfModules.unit ((ringCatSheafOf R).over V)).val.obj A from
      (1 : R.obj.obj (op A.unop.left)))
  refine Eq.trans ?_ h
  congr 1
  exact (mul_one r).symm

/-- Two morphisms out of `𝒪_V` agreeing on the unit section over `V` are equal. -/
private lemma unit_hom_ext_top {V : Opens X}
    {M : SheafOfModules.{u} ((ringCatSheafOf R).over V)}
    (g g' : SheafOfModules.unit ((ringCatSheafOf R).over V) ⟶ M)
    (h : g.val.app (op (Over.mk (𝟙 V)))
        (show (SheafOfModules.unit ((ringCatSheafOf R).over V)).val.obj (op (Over.mk (𝟙 V))) from
          (1 : R.obj.obj (op V))) =
      g'.val.app (op (Over.mk (𝟙 V)))
        (show (SheafOfModules.unit ((ringCatSheafOf R).over V)).val.obj (op (Over.mk (𝟙 V))) from
          (1 : R.obj.obj (op V)))) : g = g' := by
  apply M.unitHomEquiv.injective
  apply Subtype.ext
  funext A
  rw [SheafOfModules.unitHomEquiv_apply_coe, SheafOfModules.unitHomEquiv_apply_coe]
  let t : op (Over.mk (𝟙 V)) ⟶ A :=
    (Over.homMk A.unop.hom (Category.comp_id _) : A.unop ⟶ Over.mk (𝟙 V)).op
  have hA : ∀ k : SheafOfModules.unit ((ringCatSheafOf R).over V) ⟶ M,
      k.val.app A (show (SheafOfModules.unit ((ringCatSheafOf R).over V)).val.obj A from
        (1 : R.obj.obj (op A.unop.left))) =
      M.val.map t (k.val.app (op (Over.mk (𝟙 V)))
        (show (SheafOfModules.unit ((ringCatSheafOf R).over V)).val.obj (op (Over.mk (𝟙 V))) from
          (1 : R.obj.obj (op V)))) := by
    intro k
    have := ConcreteCategory.congr_hom (k.val.naturality t)
      (show (SheafOfModules.unit ((ringCatSheafOf R).over V)).val.obj (op (Over.mk (𝟙 V))) from
        (1 : R.obj.obj (op V)))
    refine Eq.trans ?_ this
    change _ = k.val.app A (show (SheafOfModules.unit ((ringCatSheafOf R).over V)).val.obj A from
      R.obj.map (A.unop.hom).op 1)
    rw [map_one]
  exact (hA g).trans ((congrArg (M.val.map t) h).trans (hA g').symm)

namespace PullbackFrame

variable (f) (U : Opens Y)

/-- The open `f⁻¹U ∩ f⁻¹W`, as an open over `f⁻¹U`. -/
noncomputable abbrev ov (W : Opens Y) : Over ((Opens.map f).obj U) :=
  (Over.star ((Opens.map f).obj U)).obj ((Opens.map f).obj W)

lemma ov_le (W : Opens Y) : (ov f U W).left ≤ (Opens.map f).obj W :=
  leOfHom ((Over.forgetAdjStar ((Opens.map f).obj U)).counit.app ((Opens.map f).obj W))

lemma ov_le_self (W : Opens Y) : (ov f U W).left ≤ (Opens.map f).obj U :=
  leOfHom (ov f U W).hom

lemma ov_le_inf (W : Opens Y) : (ov f U W).left ≤ (Opens.map f).obj (W ⊓ U) :=
  fun _ hx => ⟨ov_le f U W hx, ov_le_self f U W hx⟩

lemma le_ov {Z : Opens X} (W : Opens Y) (h₁ : Z ≤ (Opens.map f).obj U)
    (h₂ : Z ≤ (Opens.map f).obj W) : Z ≤ (ov f U W).left :=
  leOfHom (((Over.forgetAdjStar ((Opens.map f).obj U)).homEquiv (Over.mk (homOfLE h₁)) _
    (homOfLE h₂)).left)

lemma ov_mono {W W' : Opens Y} (i : W' ≤ W) : (ov f U W').left ≤ (ov f U W).left :=
  le_ov f U W (ov_le_self f U W') ((ov_le f U W').trans ((Opens.map f).monotone i))

/-- The restriction between opens over `f⁻¹U`, as a morphism of the opposite category. -/
def ovMap {A B : Over ((Opens.map f).obj U)} (h : B.left ≤ A.left) : op A ⟶ op B :=
  (Over.homMk (homOfLE h) (Subsingleton.elim _ _) : B ⟶ A).op

lemma over_hom_eq {A B : (Over ((Opens.map f).obj U))ᵒᵖ} (g g' : A ⟶ B) : g = g' :=
  Quiver.Hom.unop_inj (Over.OverMorphism.ext (Subsingleton.elim _ _))

variable (R) in
/-- The free module `𝒪^ι` on the opens over `f⁻¹U`. -/
noncomputable abbrev freeOver (ι : Type u) : SheafOfModules.{u} ((ringCatSheafOf R).over ((Opens.map f).obj U)) :=
  SheafOfModules.free ι

variable {f}

variable (φ) in
/-- The ring map `𝒪_Y(W ∩ U) → 𝒪_X(f⁻¹U ∩ f⁻¹W)` used to transport coordinates. -/
noncomputable def ringMap (W : Opens Y) :
    S.obj.obj (op (W ⊓ U)) →+* R.obj.obj (op (ov f U W).left) :=
  (R.obj.map (homOfLE (ov_le_inf f U W)).op).hom.comp (phiApp φ (W ⊓ U))

variable {U} in
lemma ringMap_map (W : Opens Y) (r : S.obj.obj (op W)) :
    ringMap φ U W (S.obj.map (homOfLE (inf_le_left : W ⊓ U ≤ W)).op r) =
      R.obj.map (homOfLE (ov_le f U W)).op (phiApp φ W r) := by
  change R.obj.map _ (phiApp φ (W ⊓ U) (S.obj.map _ r)) = _
  rw [phiApp_map, ring_map_map']

variable {U} in
lemma ringMap_natural {W W' : Opens Y} (i : W' ≤ W) (r : S.obj.obj (op (W ⊓ U))) :
    ringMap φ U W' (S.obj.map (homOfLE (inf_le_inf_right U i)).op r) =
      R.obj.map (homOfLE (ov_mono f U i)).op (ringMap φ U W r) := by
  change R.obj.map _ (phiApp φ (W' ⊓ U) (S.obj.map _ r)) =
    R.obj.map _ (R.obj.map _ (phiApp φ (W ⊓ U) r))
  rw [phiApp_map, ring_map_map' _ _ (homOfLE ((ov_mono f U i).trans (ov_le_inf f U W))).op,
    ring_map_map']

variable {E : SheafOfModules.{u} (ringCatSheafOf S)} {ι : Type u} [Fintype ι] [DecidableEq ι]
  {e : ι → Γ(E, U)} (hE : IsLocalFrame E U e)

/-- Module sheaves on the opens over `f⁻¹U`, at `f⁻¹U ∩ f⁻¹W`, are modules over `𝒪_X(f⁻¹U ∩ f⁻¹W)`. -/
noncomputable local instance (W : Opens Y)
    (M : SheafOfModules.{u} ((ringCatSheafOf R).over ((Opens.map f).obj U))) :
    Module (R.obj.obj (op (ov f U W).left)) (M.val.obj (op (ov f U W))) :=
  (M.val.obj (op (ov f U W))).isModule

variable (φ) in
/-- The section `∑ ρ(x_k) ⋅ ε_k` of the free module over `f⁻¹U ∩ f⁻¹W`, where `x_k` are the
coordinates of `x|_{W ∩ U}` with respect to the frame `e`. -/
noncomputable def cSection (W : Opens Y) (x : Γ(E, W)) :
    (freeOver R f U ι).val.obj (op (ov f U W)) :=
  ∑ k, (SheafOfModules.ιFree k).val.app (op (ov f U W))
    (show (SheafOfModules.unit ((ringCatSheafOf R).over ((Opens.map f).obj U))).val.obj
      (op (ov f U W)) from ringMap φ U W (hE.coord (inf_le_right : W ⊓ U ≤ U)
        (E.val.presheaf.map (homOfLE (inf_le_left : W ⊓ U ≤ W)).op x) k))

omit [DecidableEq ι] in
lemma cSection_add (W : Opens Y) (x x' : Γ(E, W)) :
    cSection φ U hE W (x + x') = cSection φ U hE W x + cSection φ U hE W x' := by
  unfold cSection
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_add, map_add, Pi.add_apply, map_add]
  exact ((SheafOfModules.ιFree k).val.app (op (ov f U W))).hom.map_add _ _

omit [DecidableEq ι] in
lemma cSection_smul (W : Opens Y) (r : S.obj.obj (op W)) (x : Γ(E, W)) :
    cSection φ U hE W (r • x) =
      R.obj.map (homOfLE (ov_le f U W)).op (phiApp φ W r) • cSection φ U hE W x := by
  unfold cSection
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hx : E.val.presheaf.map (homOfLE (inf_le_left : W ⊓ U ≤ W)).op (r • x) =
      S.obj.map (homOfLE (inf_le_left : W ⊓ U ≤ W)).op r •
        E.val.presheaf.map (homOfLE (inf_le_left : W ⊓ U ≤ W)).op x :=
    E.val.map_smul _ r x
  rw [hx, LinearEquiv.map_smul, Pi.smul_apply, smul_eq_mul, map_mul, ringMap_map]
  exact ((SheafOfModules.ιFree (R := (ringCatSheafOf R).over ((Opens.map f).obj U)) k).val.app
    (op (ov f U W))).hom.map_smul _ _

omit [DecidableEq ι] in
lemma cSection_restrict {W W' : Opens Y} (i : W' ≤ W) (x : Γ(E, W)) :
    cSection φ U hE W' (E.val.presheaf.map (homOfLE i).op x) =
      (freeOver R f U ι).val.map (ovMap f U (ov_mono f U i)) (cSection φ U hE W x) := by
  unfold cSection
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hx : E.val.presheaf.map (homOfLE (inf_le_left : W' ⊓ U ≤ W')).op
      (E.val.presheaf.map (homOfLE i).op x) =
      E.val.presheaf.map (homOfLE (inf_le_inf_right U i)).op
        (E.val.presheaf.map (homOfLE (inf_le_left : W ⊓ U ≤ W)).op x) := by
    rw [modules_map_map' E _ _ (homOfLE ((inf_le_left : W' ⊓ U ≤ W').trans i)).op,
      modules_map_map' E _ _ (homOfLE ((inf_le_left : W' ⊓ U ≤ W').trans i)).op]
  rw [hx, hE.coord_restrict (inf_le_right : W ⊓ U ≤ U) (inf_le_inf_right U i),
    ringMap_natural (φ := φ) i]
  exact ConcreteCategory.congr_hom ((SheafOfModules.ιFree k).val.naturality
    (ovMap f U (ov_mono f U i))) _

variable (φ) in
/-- The morphism `E ⟶ f_* j_* 𝒪^ι` attached to the frame `e`. -/
noncomputable def cHom : E ⟶ (SheafOfModules.pushforward.{u} φ).obj
    ((openPushforward (R := R) ((Opens.map f).obj U)).obj (freeOver R f U ι)) :=
  modulesHomMk (fun W =>
    { toFun := cSection φ U hE W
      map_add' := cSection_add U hE W
      map_smul' := fun r x => by
        rw [RingHom.id_apply]
        exact cSection_smul (φ := φ) U hE W r x })
    (fun W W' i x => cSection_restrict U hE (W := W) (W' := W') i x)

variable (φ) in
/-- The adjunction `f^*(-)|_{f⁻¹U} ⊣ f_* j_*`. -/
noncomputable abbrev adj :=
  (SheafOfModules.pullbackPushforwardAdjunction.{u} φ).comp
    (restrictionAdjunction (R := R) ((Opens.map f).obj U))

variable (φ E) in
/-- The restriction `(f^*E)|_{f⁻¹U}`. -/
noncomputable abbrev restrictedPullback :
    SheafOfModules.{u} ((ringCatSheafOf R).over ((Opens.map f).obj U)) :=
  ((SheafOfModules.pullback.{u} φ).obj E).over ((Opens.map f).obj U)

variable (φ) in
/-- The section `η(x)|_{f⁻¹U ∩ f⁻¹W}` of `f^*E`. -/
noncomputable def uSec (W : Opens Y) (x : Γ(E, W)) :
    Γ((SheafOfModules.pullback.{u} φ).obj E, (ov f U W).left) :=
  ((SheafOfModules.pullback.{u} φ).obj E).val.presheaf.map (homOfLE (ov_le f U W)).op (etaSec x)

lemma adj_unit_app (W : Opens Y) (x : Γ(E, W)) :
    ((adj φ U).unit.app E).val.app (op W) x =
      (uSec φ U W x : (restrictedPullback φ U E).val.obj (op (ov f U W))) := by
  rw [Adjunction.comp_unit_app]
  rfl

variable (φ) in
/-- The morphism `(f^*E)|_{f⁻¹U} ⟶ 𝒪^ι` adjoint to `cHom`. -/
noncomputable def toFree : restrictedPullback φ U E ⟶ freeOver R f U ι :=
  ((adj φ U).homEquiv E _).symm (cHom φ U hE)

omit [DecidableEq ι] in
lemma toFree_unit (W : Opens Y) (x : Γ(E, W)) :
    (toFree φ U hE).val.app (op (ov f U W)) (uSec φ U W x) = cSection φ U hE W x := by
  have h := (adj φ U).homEquiv_unit E _ (toFree φ U hE)
  rw [toFree, Equiv.apply_symm_apply] at h
  have h' := congrArg (fun g => g.val.app (op W) x) h
  refine Eq.trans ?_ h'.symm
  change (toFree φ U hE).val.app (op (ov f U W)) (uSec φ U W x) =
    (toFree φ U hE).val.app (op (ov f U W)) (((adj φ U).unit.app E).val.app (op W) x)
  rw [adj_unit_app]

variable (φ) in
/-- The morphism `𝒪^ι ⟶ (f^*E)|_{f⁻¹U}` given by the sections `η(e_i)`. -/
noncomputable def fromFree (e : ι → Γ(E, U)) : freeOver R f U ι ⟶ restrictedPullback φ U E :=
  frameHom' (fun i => etaSec (φ := φ) (e i))

/-- `f⁻¹U` as the terminal open over `f⁻¹U`. -/
private abbrev topOver : (Over ((Opens.map f).obj U))ᵒᵖ := op (Over.mk (𝟙 ((Opens.map f).obj U)))

lemma fromFree_toFree : fromFree φ U e ≫ toFree φ U hE = 𝟙 _ := by
  refine Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan ι) _ _ fun i => ?_
  apply unit_hom_ext_top
  change (toFree φ U hE).val.app (topOver U) ((fromFree φ U e).val.app (topOver U)
      ((SheafOfModules.ιFree (R := (ringCatSheafOf R).over ((Opens.map f).obj U)) (I := ι) i).val.app
        (topOver U) (show (SheafOfModules.unit _).val.obj (topOver U) from
          (1 : R.obj.obj (op ((Opens.map f).obj U)))))) =
    (SheafOfModules.ιFree (R := (ringCatSheafOf R).over ((Opens.map f).obj U)) (I := ι) i).val.app
        (topOver U) (show (SheafOfModules.unit _).val.obj (topOver U) from
          (1 : R.obj.obj (op ((Opens.map f).obj U))))
  rw [fromFree, frameHom'_ιFree]
  let g : op (ov f U U) ⟶ topOver U := ovMap f U (le_ov f U U le_rfl le_rfl)
  have key : ((SheafOfModules.pullback.{u} φ).obj E).val.presheaf.map
      (Over.mk (𝟙 ((Opens.map f).obj U))).hom.op (etaSec (φ := φ) (e i)) =
      (restrictedPullback φ U E).val.map g (uSec φ U U (e i)) := by
    change _ = ((SheafOfModules.pullback.{u} φ).obj E).val.presheaf.map
      (homOfLE (le_ov f U U le_rfl le_rfl)).op
      (((SheafOfModules.pullback.{u} φ).obj E).val.presheaf.map (homOfLE (ov_le f U U)).op
        (etaSec (φ := φ) (e i)))
    rw [modules_map_map' _ _ _ (Over.mk (𝟙 ((Opens.map f).obj U))).hom.op]
  rw [key]
  refine (ConcreteCategory.congr_hom ((toFree φ U hE).val.naturality g) (uSec φ U U (e i))).trans ?_
  change (freeOver R f U ι).val.map g ((toFree φ U hE).val.app (op (ov f U U)) (uSec φ U U (e i))) = _
  rw [toFree_unit, cSection, hE.coord_self (inf_le_right : U ⊓ U ≤ U) i, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, map_one]
    have h2 := ConcreteCategory.congr_hom
      ((SheafOfModules.ιFree (R := (ringCatSheafOf R).over ((Opens.map f).obj U)) (I := ι) i).val.naturality g)
      (show (SheafOfModules.unit _).val.obj (op (ov f U U)) from
        (1 : R.obj.obj (op (ov f U U).left)))
    refine h2.symm.trans (congrArg (fun t =>
      (SheafOfModules.ιFree (R := (ringCatSheafOf R).over ((Opens.map f).obj U)) (I := ι) i).val.app
        (topOver U) t) ?_)
    change R.obj.map _ (1 : R.obj.obj (op (ov f U U).left)) = 1
    rw [map_one]
  · intro k _ hk
    rw [Pi.single_eq_of_ne hk, map_zero]
    exact ((SheafOfModules.ιFree (R := (ringCatSheafOf R).over ((Opens.map f).obj U)) (I := ι) k).val.app
      (op (ov f U U))).hom.map_zero
  · intro h'; exact absurd (Finset.mem_univ i) h'

omit [Fintype ι] [DecidableEq ι] in
lemma uSec_sum {κ : Type*} [Fintype κ] (W : Opens Y) (y : κ → Γ(E, W)) :
    uSec φ U W (∑ k, y k) = ∑ k, uSec φ U W (y k) := by
  have h : etaSec (φ := φ) (∑ k, y k) = ∑ k, etaSec (φ := φ) (y k) :=
    map_sum (ConcreteCategory.hom (sectionsMap (pullbackUnit φ E) W)) _ _
  unfold uSec
  rw [h]
  exact map_sum (ConcreteCategory.hom (((SheafOfModules.pullback.{u} φ).obj E).val.presheaf.map
    (homOfLE (ov_le f U W)).op)) _ _

omit [Fintype ι] [DecidableEq ι] in
lemma uSec_smul (W : Opens Y) (r : S.obj.obj (op W)) (y : Γ(E, W)) :
    uSec φ U W (r • y) = R.obj.map (homOfLE (ov_le f U W)).op (phiApp φ W r) • uSec φ U W y := by
  unfold uSec
  rw [etaSec_smul]
  exact ((SheafOfModules.pullback.{u} φ).obj E).val.map_smul _ _ _

omit [Fintype ι] [DecidableEq ι] in
lemma fromFree_ιFree (W : Opens Y) (k : ι) (c : R.obj.obj (op (ov f U W).left)) :
    (fromFree φ U e).val.app (op (ov f U W))
        ((SheafOfModules.ιFree (R := (ringCatSheafOf R).over ((Opens.map f).obj U)) (I := ι) k).val.app
          (op (ov f U W)) c) =
      c • ((SheafOfModules.pullback.{u} φ).obj E).val.presheaf.map (ov f U W).hom.op
        (etaSec (φ := φ) (e k)) := by
  rw [ιFree_app_smul_one']
  refine (((fromFree φ U e).val.app (op (ov f U W))).hom.map_smul _ _).trans ?_
  rw [fromFree, frameHom'_ιFree]
  rfl

omit [DecidableEq ι] in
lemma toFree_fromFree : toFree φ U hE ≫ fromFree φ U e = 𝟙 _ := by
  apply ((adj φ U).homEquiv E _).injective
  rw [Adjunction.homEquiv_naturality_right, toFree, Equiv.apply_symm_apply,
    Adjunction.homEquiv_unit]
  refine modules_hom_ext' fun W x => ?_
  change (fromFree φ U e).val.app (op (ov f U W)) (cSection φ U hE W x) =
    ((adj φ U).unit.app E).val.app (op W) x
  rw [adj_unit_app]
  have hle : (ov f U W).left ≤ (ov f U (W ⊓ U)).left :=
    le_ov f U (W ⊓ U) (ov_le_self f U W) (ov_le_inf f U W)
  have h1 : uSec φ U W x = ((SheafOfModules.pullback.{u} φ).obj E).val.presheaf.map (homOfLE hle).op
      (uSec φ U (W ⊓ U) (E.val.presheaf.map (homOfLE (inf_le_left : W ⊓ U ≤ W)).op x)) := by
    unfold uSec
    rw [etaSec_restrict, modules_map_map' _ _ _
      (homOfLE ((ov_le f U (W ⊓ U)).trans ((Opens.map f).monotone inf_le_left))).op,
      modules_map_map' _ _ _ (homOfLE (ov_le f U W)).op]
  rw [h1, ← hE.localFrameMap_coord (inf_le_right : W ⊓ U ≤ U)
    (E.val.presheaf.map (homOfLE (inf_le_left : W ⊓ U ≤ W)).op x), localFrameMap_apply, uSec_sum,
    map_sum, cSection, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [fromFree_ιFree, uSec_smul]
  refine Eq.trans ?_ (((SheafOfModules.pullback.{u} φ).obj E).val.map_smul _ _ _).symm
  congr 1
  · change R.obj.map _ (phiApp φ (W ⊓ U) _) = R.obj.map _ (R.obj.map _ (phiApp φ (W ⊓ U) _))
    rw [ring_map_map']
  · change _ = ((SheafOfModules.pullback.{u} φ).obj E).val.presheaf.map (homOfLE hle).op
      (((SheafOfModules.pullback.{u} φ).obj E).val.presheaf.map (homOfLE (ov_le f U (W ⊓ U))).op
        (etaSec (φ := φ) (E.val.presheaf.map (homOfLE (inf_le_right : W ⊓ U ≤ U)).op (e k))))
    rw [etaSec_restrict, modules_map_map' _ _ _
      (homOfLE ((ov_le f U (W ⊓ U)).trans ((Opens.map f).monotone inf_le_right))).op,
      modules_map_map' _ _ _ (ov f U W).hom.op]

end PullbackFrame

/-- **The pullback of a frame is a frame.** If `e` is a frame of the `𝒪_Y`-module `E` over `U`,
then the sections `η(e_i)` of `f^*E` over `f⁻¹U`, where `η : E ⟶ f_* f^* E` is the unit of the
adjunction, form a frame of `f^*E` over `f⁻¹U`. -/
theorem IsLocalFrame.pullback {E : SheafOfModules.{u} (ringCatSheafOf S)} {U : Opens Y}
    {ι : Type u} [Fintype ι] [DecidableEq ι] {e : ι → Γ(E, U)} (hE : IsLocalFrame E U e) :
    IsLocalFrame ((SheafOfModules.pullback.{u} φ).obj E) ((Opens.map f).obj U)
      (fun i => etaSec (φ := φ) (e i)) := by
  have : IsIso (PullbackFrame.fromFree φ U e) :=
    ⟨⟨PullbackFrame.toFree φ U hE, PullbackFrame.fromFree_toFree U hE,
      PullbackFrame.toFree_fromFree U hE⟩⟩
  have h := isLocalFrame_of_over_iso (asIso (PullbackFrame.fromFree φ U e)).symm
  refine (congrArg (IsLocalFrame _ _) (funext fun i => ?_)).mpr h
  change _ = (PullbackFrame.fromFree φ U e).val.app (op (Over.mk (𝟙 ((Opens.map f).obj U))))
    (freeVec _ i)
  rw [freeVec, PullbackFrame.fromFree, frameHom'_ιFree]
  exact (modules_map_self _ _ _).symm

end PullbackFrame

section ProjectionFormula

variable {X Y : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {S : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}} {f : X ⟶ Y}
  (φ : ringCatSheafOf S ⟶
    ((Opens.map f).sheafPushforwardContinuous RingCat.{u} _ _).obj (ringCatSheafOf R))
  (F : SheafOfModules.{u} (ringCatSheafOf R)) (E : SheafOfModules.{u} (ringCatSheafOf S))

/-- Sections of a module sheaf over an open, as an abelian group. -/
local notation3 "Γ(" M ", " U ")" => (PresheafOfModules.presheaf (SheafOfModules.val M)).obj
  (Opposite.op U)

/-- The `𝒪_X`-module `F ⊗ f^*E`. -/
noncomputable abbrev pullbackTensor : SheafOfModules.{u} (ringCatSheafOf R) :=
  moduleSheafTensor F ((SheafOfModules.pullback.{u} φ).obj E)

/-- The section `s ⊗ η(x)` of `F ⊗ f^*E` over `f⁻¹V`. -/
noncomputable def projSec {V : Opens Y} (s : Γ(F, (Opens.map f).obj V)) (x : Γ(E, V)) :
    Γ(pullbackTensor φ F E, (Opens.map f).obj V) :=
  (moduleSheafTensorBilinear F ((SheafOfModules.pullback.{u} φ).obj E)).app
    (op ((Opens.map f).obj V)) s (etaSec x)

variable {φ F E}

lemma projSec_add_left {V : Opens Y} (s s' : Γ(F, (Opens.map f).obj V)) (x : Γ(E, V)) :
    projSec φ F E (s + s') x = projSec φ F E s x + projSec φ F E s' x :=
  LinearMap.map_add₂ ((moduleSheafTensorBilinear F ((SheafOfModules.pullback.{u} φ).obj E)).app
    (op ((Opens.map f).obj V))) s s' (etaSec x)

lemma projSec_smul_left {V : Opens Y} (r : S.obj.obj (op V)) (s : Γ(F, (Opens.map f).obj V))
    (x : Γ(E, V)) : projSec φ F E (phiApp φ V r • s) x = phiApp φ V r • projSec φ F E s x :=
  LinearMap.map_smul₂ ((moduleSheafTensorBilinear F ((SheafOfModules.pullback.{u} φ).obj E)).app
    (op ((Opens.map f).obj V))) (phiApp φ V r) s (etaSec x)

lemma projSec_add_right {V : Opens Y} (s : Γ(F, (Opens.map f).obj V)) (x x' : Γ(E, V)) :
    projSec φ F E s (x + x') = projSec φ F E s x + projSec φ F E s x' := by
  rw [projSec, etaSec_add]
  exact map_add (((moduleSheafTensorBilinear F ((SheafOfModules.pullback.{u} φ).obj E)).app
    (op ((Opens.map f).obj V))) s) _ _

lemma projSec_smul_right {V : Opens Y} (r : S.obj.obj (op V)) (s : Γ(F, (Opens.map f).obj V))
    (x : Γ(E, V)) : projSec φ F E s (r • x) = phiApp φ V r • projSec φ F E s x := by
  rw [projSec, etaSec_smul]
  exact map_smul (((moduleSheafTensorBilinear F ((SheafOfModules.pullback.{u} φ).obj E)).app
    (op ((Opens.map f).obj V))) s) _ _

lemma projSec_restrict {V V' : Opens Y} (i : V' ≤ V) (s : Γ(F, (Opens.map f).obj V))
    (x : Γ(E, V)) :
    (pullbackTensor φ F E).val.presheaf.map (homOfLE ((Opens.map f).monotone i)).op
        (projSec φ F E s x) =
      projSec φ F E (F.val.presheaf.map (homOfLE ((Opens.map f).monotone i)).op s)
        (E.val.presheaf.map (homOfLE i).op x) := by
  rw [projSec, projSec, etaSec_restrict]
  exact (moduleSheafTensorBilinear F _).naturality _ _ _

variable (φ F E)

/-- The bilinear map `f_*F × E → f_*(F ⊗ f^*E)`, `(s, x) ↦ s ⊗ η(x)`. -/
noncomputable def projectionFormulaBilinear :
    ModuleSheafBilinear ((SheafOfModules.pushforward.{u} φ).obj F) E
      ((SheafOfModules.pushforward.{u} φ).obj (pullbackTensor φ F E)) where
  app V := LinearMap.mk₂ _
    (fun (s : Γ(F, (Opens.map f).obj V.unop)) (x : Γ(E, V.unop)) => projSec φ F E s x)
    (fun s s' x => projSec_add_left s s' x)
    (fun r s x => projSec_smul_left r s x)
    (fun s x x' => projSec_add_right s x x')
    (fun r s x => projSec_smul_right r s x)
  naturality {V V'} i s x := projSec_restrict (V := V.unop) (V' := V'.unop) (leOfHom i.unop) s x

/-- **The projection-formula map** `f_*F ⊗ E ⟶ f_*(F ⊗ f^*E)`, `s ⊗ x ↦ s ⊗ η(x)`, where
`η : E ⟶ f_* f^* E` is the unit of the pullback–pushforward adjunction. -/
noncomputable def projectionFormulaMap :
    moduleSheafTensor ((SheafOfModules.pushforward.{u} φ).obj F) E ⟶
      (SheafOfModules.pushforward.{u} φ).obj (pullbackTensor φ F E) :=
  (moduleSheafTensorHomEquiv _ _ _).symm (projectionFormulaBilinear φ F E)

variable {φ F E}

lemma projectionFormulaMap_tmul {V : Opens Y} (s : Γ(F, (Opens.map f).obj V)) (x : Γ(E, V)) :
    (projectionFormulaMap φ F E).val.app (op V)
        ((moduleSheafTensorBilinear ((SheafOfModules.pushforward.{u} φ).obj F) E).app (op V) s x) =
      projSec φ F E s x := by
  have := congrArg (fun β : ModuleSheafBilinear _ _ _ => β.app (op V) s x)
    ((moduleSheafTensorHomEquiv_apply (projectionFormulaMap φ F E)).symm.trans
      (Equiv.apply_symm_apply (moduleSheafTensorHomEquiv _ _ _) (projectionFormulaBilinear φ F E)))
  exact this

lemma projectionFormulaMap_presheaf_bijective {U : Opens Y} {ι : Type u} [Fintype ι]
    [DecidableEq ι] {e : ι → Γ(E, U)} (hE : IsLocalFrame E U e) {V : Opens Y} (h : V ≤ U) :
    Function.Bijective (((PresheafOfModules.toPresheaf _).map
      (moduleSheafTensorUnit ((SheafOfModules.pushforward.{u} φ).obj F) E ≫
        (projectionFormulaMap φ F E).val)).app (op V)) := by
  have h1 := sum_tmul_frame_bijective (R := S.obj.obj (op V))
    (M := Γ((SheafOfModules.pushforward.{u} φ).obj F, V))
    (N := Γ(E, V)) (fun j => E.val.presheaf.map (homOfLE h).op (e j)) (hE.coord h).toLinearMap
    (fun n => by
      rw [← localFrameMap_apply]
      exact hE.localFrameMap_coord h n)
    (fun i => hE.coord_self h i)
  have h3 := (IsLocalFrame.pullback (φ := φ) hE).tensorFrameMap_bijective (F := F) ((Opens.map f).monotone h)
  let P' : TensorProduct (S.obj.obj (op V)) Γ((SheafOfModules.pushforward.{u} φ).obj F, V)
      Γ(E, V) →+ Γ((SheafOfModules.pushforward.{u} φ).obj (pullbackTensor φ F E), V) :=
    (((PresheafOfModules.toPresheaf _).map
      (moduleSheafTensorUnit ((SheafOfModules.pushforward.{u} φ).obj F) E ≫
        (projectionFormulaMap φ F E).val)).app (op V)).hom
  have h2 : ⇑P' ∘ (fun m : ι → Γ((SheafOfModules.pushforward.{u} φ).obj F, V) =>
        ∑ i, m i ⊗ₜ[S.obj.obj (op V)] E.val.presheaf.map (homOfLE h).op (e i)) =
      tensorFrameMap F (fun i => etaSec (φ := φ) (e i)) ((Opens.map f).monotone h) := by
    funext m
    rw [Function.comp_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    change (projectionFormulaMap φ F E).val.app (op V)
        ((moduleSheafTensorBilinear ((SheafOfModules.pushforward.{u} φ).obj F) E).app (op V) (m i)
          (E.val.presheaf.map (homOfLE h).op (e i))) = _
    refine (projectionFormulaMap_tmul (m i) (E.val.presheaf.map (homOfLE h).op (e i))).trans ?_
    exact congrArg (((moduleSheafTensorBilinear F ((SheafOfModules.pullback.{u} φ).obj E)).app
      (op ((Opens.map f).obj V))) (m i)) (etaSec_restrict h (e i))
  rw [← h2] at h3
  exact (Function.Bijective.of_comp_iff P' h1).mp h3

/-- **Hartshorne II, Exercise 5.1(d): the projection formula.** For a morphism of ringed spaces
`f : X ⟶ Y`, an `𝒪_X`-module `F` and a finite locally free `𝒪_Y`-module `E`, the canonical map
`f_*F ⊗ E ⟶ f_*(F ⊗ f^*E)` is an isomorphism. -/
theorem projectionFormulaMap_isIso (hE : IsFiniteLocallyFree E) :
    IsIso (projectionFormulaMap φ F E) :=
  modules_isIso_of_locally_bijective _ fun y => by
    classical
    obtain ⟨U, ι, _, e, hy, hEU⟩ := exists_isLocalFrame_of_isFiniteLocallyFree hE y
    exact ⟨U, hy, fun V hV => tensor_app_bijective_of_presheaf _
      (fun V' hV' => projectionFormulaMap_presheaf_bijective hEU hV') hV⟩

variable (φ F E) in
/-- **Hartshorne II, Exercise 5.1(d).** The natural isomorphism `f_*(F ⊗ f^*E) ≅ f_*F ⊗ E` for a
finite locally free `𝒪_Y`-module `E`, inverse to the projection-formula map. -/
noncomputable def projectionFormulaIso (hE : IsFiniteLocallyFree E) :
    (SheafOfModules.pushforward.{u} φ).obj (pullbackTensor φ F E) ≅
      moduleSheafTensor ((SheafOfModules.pushforward.{u} φ).obj F) E :=
  haveI := projectionFormulaMap_isIso (φ := φ) (F := F) hE
  (asIso (projectionFormulaMap φ F E)).symm

/-- The projection-formula map is natural in `F`. -/
lemma projectionFormulaMap_naturality_left {F' : SheafOfModules.{u} (ringCatSheafOf R)}
    (g : F ⟶ F') :
    modulesTensorMap ((SheafOfModules.pushforward.{u} φ).map g) (𝟙 E) ≫
        projectionFormulaMap φ F' E =
      projectionFormulaMap φ F E ≫
        (SheafOfModules.pushforward.{u} φ).map
          (modulesTensorMap g (𝟙 ((SheafOfModules.pullback.{u} φ).obj E))) := by
  refine modulesTensor_hom_ext fun V s x => ?_
  change (projectionFormulaMap φ F' E).val.app (op V)
      (sectionsMap (modulesTensorMap ((SheafOfModules.pushforward.{u} φ).map g) (𝟙 E)) V
        ((moduleSheafTensorBilinear _ E).app (op V) s x)) =
    sectionsMap (modulesTensorMap g (𝟙 ((SheafOfModules.pullback.{u} φ).obj E))) ((Opens.map f).obj V)
      ((projectionFormulaMap φ F E).val.app (op V) ((moduleSheafTensorBilinear _ E).app (op V) s x))
  rw [modulesTensorMap_tmul]
  refine (projectionFormulaMap_tmul (φ := φ) (F := F') (E := E)
    (sectionsMap g ((Opens.map f).obj V) s) x).trans ?_
  refine Eq.trans ?_ (congrArg (fun t => sectionsMap (modulesTensorMap g
    (𝟙 ((SheafOfModules.pullback.{u} φ).obj E))) ((Opens.map f).obj V) t)
    (projectionFormulaMap_tmul (φ := φ) (F := F) (E := E) s x)).symm
  exact (modulesTensorMap_tmul g (𝟙 _) s (etaSec x)).symm

lemma etaSec_naturality {E' : SheafOfModules.{u} (ringCatSheafOf S)} (g : E ⟶ E') {V : Opens Y}
    (x : Γ(E, V)) :
    etaSec (φ := φ) (sectionsMap g V x) =
      sectionsMap ((SheafOfModules.pullback.{u} φ).map g) ((Opens.map f).obj V) (etaSec x) := by
  have h := (SheafOfModules.pullbackPushforwardAdjunction.{u} φ).unit_naturality g
  exact (congrArg (fun t => t.val.app (op V) x) h).symm

/-- The projection-formula map is natural in `E`. -/
lemma projectionFormulaMap_naturality_right {E' : SheafOfModules.{u} (ringCatSheafOf S)}
    (g : E ⟶ E') :
    modulesTensorMap (𝟙 ((SheafOfModules.pushforward.{u} φ).obj F)) g ≫
        projectionFormulaMap φ F E' =
      projectionFormulaMap φ F E ≫
        (SheafOfModules.pushforward.{u} φ).map
          (modulesTensorMap (𝟙 F) ((SheafOfModules.pullback.{u} φ).map g)) := by
  refine modulesTensor_hom_ext fun V s x => ?_
  change (projectionFormulaMap φ F E').val.app (op V) (sectionsMap (modulesTensorMap
      (𝟙 ((SheafOfModules.pushforward.{u} φ).obj F)) g) V
        ((moduleSheafTensorBilinear _ E).app (op V) s x)) =
    sectionsMap (modulesTensorMap (𝟙 F) ((SheafOfModules.pullback.{u} φ).map g))
      ((Opens.map f).obj V)
      ((projectionFormulaMap φ F E).val.app (op V) ((moduleSheafTensorBilinear _ E).app (op V) s x))
  rw [modulesTensorMap_tmul]
  refine (projectionFormulaMap_tmul (φ := φ) (F := F) (E := E') s (sectionsMap g V x)).trans ?_
  refine Eq.trans ?_ (congrArg (fun t => sectionsMap (modulesTensorMap (𝟙 F)
    ((SheafOfModules.pullback.{u} φ).map g)) ((Opens.map f).obj V) t)
    (projectionFormulaMap_tmul (φ := φ) (F := F) (E := E) s x)).symm
  refine Eq.trans ?_ (modulesTensorMap_tmul (𝟙 F) ((SheafOfModules.pullback.{u} φ).map g) s
    (etaSec x)).symm
  exact congrArg (((moduleSheafTensorBilinear F ((SheafOfModules.pullback.{u} φ).obj E')).app
    (op ((Opens.map f).obj V))) s) (etaSec_naturality g x)

end ProjectionFormula

end Ringed

end Hartshorne

/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.RingedSpace.LocallyFree
import Hartshorne.RingedSpace.ModuleSkyscraper
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Topology.LocallyConstant.Basic

/-!
# The rank of a locally free module on a ringed space

Let `(X, 𝒪_X)` be a ringed space, given by a topological space `X` and a sheaf `R` of commutative
rings on `X`. The rank of a locally free `𝒪_X`-module `F` at a point `x`
(`Hartshorne.Ringed.rankAt`) is the number of copies (a cardinal, possibly infinite) in a free
presentation `F|_U ≅ 𝒪_U ^ (⊕ I)` on some open neighbourhood `U` of `x`.

This is well defined only where the stalk `𝒪_{X,x}` is a nonzero ring: if `𝒪_{X,x} = 0` then
`𝒪_X` vanishes near `x`, and every module is free there of every rank. So the theorems below
assume that the stalks of `𝒪_X` are nontrivial, which holds on every locally ringed space, and
in particular on every scheme.

The proof goes through stalks. For an `𝒪_{X,x}`-module `N` with skyscraper sheaf `x_* N`,
morphisms `F_x → N` are morphisms `F ⟶ x_* N` (the stalk–skyscraper adjunction), and these are
the same as morphisms `F|_U ⟶ (x_* N)|_U` for any open `U ∋ x`. If `F|_U ≅ 𝒪_U ^ (⊕ I)`, the
latter are the families `I → N`, naturally in `N`, so by the Yoneda lemma the stalk `F_x` is the
free `𝒪_{X,x}`-module on `I` (`moduleStalkIsoFree`). A nonzero commutative ring has invariant
basis number, so `#I` is the rank of `F_x` over `𝒪_{X,x}` (`rank_moduleStalk_eq`), which does not
depend on the presentation. Hence the rank of a locally free module is locally constant
(`isLocallyConstant_rankAt`), and constant when `X` is connected
(`rankAt_eq_of_connectedSpace`).
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace Hartshorne

namespace Ringed

open ModuleSheafTensor

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

set_option hygiene false in
/-- `𝒪_X`-modules. -/
local notation "𝓜" => SheafOfModules.{u} (ringCatSheafOf R)

section Skyscraper

variable {x : X} {U : Opens X}

/-- For `x ∈ U`, the sections over `U` of the skyscraper sheaf `x_* N` restricted to `U` are the
elements of `N`. -/
noncomputable def skyscraperOverSectionsEquiv (hx : x ∈ U)
    (N : ModuleCat.{u} (ringSheafStalk R x)) :
    (((moduleSkyscraper x).obj N).over U).sections ≃ N where
  toFun s := s.1 (op (Over.mk (𝟙 U))) ⟨hx⟩
  invFun n := ⟨fun _ _ => n, fun _ => rfl⟩
  left_inv s := by
    refine PresheafOfModules.sections_ext _ _ fun V => ?_
    funext h
    have hs := s.2 (Over.homMk V.unop.hom : V.unop ⟶ Over.mk (𝟙 U)).op
    rw [← hs]
    rfl
  right_inv _ := rfl

/-- For `x ∈ U`, restricting morphisms `F ⟶ x_* N` to `U` is a bijection onto the morphisms
`F|_U ⟶ (x_* N)|_U`. -/
theorem over_map_bijective_moduleSkyscraper (hx : x ∈ U) (F : 𝓜)
    (N : ModuleCat.{u} (ringSheafStalk R x)) :
    Function.Bijective (fun φ : F ⟶ (moduleSkyscraper x).obj N =>
      (SheafOfModules.overFunctor (ringCatSheafOf R) U).map φ) := by
  constructor
  · intro φ φ' h
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
    ext s
    funext hV
    let W : Over U := Over.mk (homOfLE inf_le_right : V.unop ⊓ U ⟶ U)
    have key := congrArg (fun ψ : F.over U ⟶ ((moduleSkyscraper x).obj N).over U =>
      ψ.val.app (op W) (F.val.map (homOfLE inf_le_left : V.unop ⊓ U ⟶ V.unop).op s)
        ⟨⟨hV.down, hx⟩⟩) h
    have e1 := congrFun (PresheafOfModules.naturality_apply φ.val
      (homOfLE inf_le_left : V.unop ⊓ U ⟶ V.unop).op s) ⟨⟨hV.down, hx⟩⟩
    have e2 := congrFun (PresheafOfModules.naturality_apply φ'.val
      (homOfLE inf_le_left : V.unop ⊓ U ⟶ V.unop).op s) ⟨⟨hV.down, hx⟩⟩
    exact e1.symm.trans (key.trans e2)
  · intro ψ
    let W : Opens X → Over U := fun V => Over.mk (homOfLE inf_le_right : V ⊓ U ⟶ U)
    let f : ∀ V : Opens X, F.val.presheaf.obj (op V) →ₗ[R.obj.obj (op V)]
        ((moduleSkyscraper x).obj N).val.presheaf.obj (op V) := fun V =>
      { toFun := fun s h => ψ.val.app (op (W V))
            (F.val.presheaf.map (homOfLE inf_le_left : V ⊓ U ⟶ V).op s) ⟨⟨h.down, hx⟩⟩
        map_add' := fun s t => by
          funext h
          have e := congrFun ((ψ.val.app (op (W V))).hom.map_add
            (F.val.map (homOfLE inf_le_left : V ⊓ U ⟶ V).op s)
            (F.val.map (homOfLE inf_le_left : V ⊓ U ⟶ V).op t)) ⟨⟨h.down, hx⟩⟩
          simp only [map_add]
          exact e
        map_smul' := fun r s => by
          funext h
          have e := (ψ.val.app (op (W V))).hom.map_smul
            (R.obj.map (homOfLE inf_le_left : V ⊓ U ⟶ V).op r)
            (F.val.map (homOfLE inf_le_left : V ⊓ U ⟶ V).op s)
          have e' := congrFun e ⟨⟨h.down, hx⟩⟩
          have e0 := F.val.map_smul (homOfLE inf_le_left : V ⊓ U ⟶ V).op r s
          refine (congrArg (fun m => ψ.val.app (op (W V)) m ⟨⟨h.down, hx⟩⟩) e0).trans
            (e'.trans ?_)
          exact congrArg (fun c : ringSheafStalk R x => c • (ψ.val.app (op (W V))
              (F.val.map (homOfLE inf_le_left : V ⊓ U ⟶ V).op s) ⟨⟨h.down, hx⟩⟩ : N))
            (TopCat.Presheaf.germ_res_apply R.obj (homOfLE inf_le_left) x ⟨h.down, hx⟩ r) }
    have hf : ∀ (V V' : Opens X) (i : V' ≤ V) (s : F.val.presheaf.obj (op V)),
        f V' (F.val.presheaf.map (homOfLE i).op s) =
          ((moduleSkyscraper x).obj N).val.presheaf.map (homOfLE i).op (f V s) := by
      intro V V' i s
      funext h
      let j : W V' ⟶ W V := Over.homMk (homOfLE (inf_le_inf_right U i))
      have e := congrFun (PresheafOfModules.naturality_apply ψ.val j.op
        (F.val.presheaf.map (homOfLE inf_le_left : V ⊓ U ⟶ V).op s)) ⟨⟨h.down, hx⟩⟩
      have e2 : F.val.presheaf.map (homOfLE inf_le_left : V' ⊓ U ⟶ V').op
          (F.val.presheaf.map (homOfLE i).op s) =
            F.val.presheaf.map (homOfLE (inf_le_inf_right U i) : V' ⊓ U ⟶ V ⊓ U).op
              (F.val.presheaf.map (homOfLE inf_le_left : V ⊓ U ⟶ V).op s) := by
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← ConcreteCategory.comp_apply,
          ← Functor.map_comp]
        rfl
      exact (congrArg (fun m => ψ.val.app (op (W V')) m ⟨⟨h.down, hx⟩⟩) e2).trans e
    refine ⟨modulesHomMk f hf, ?_⟩
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
    ext s
    funext h
    let k : W V.unop.left ⟶ V.unop := Over.homMk (homOfLE inf_le_left)
    exact congrFun (PresheafOfModules.naturality_apply ψ.val k.op s) ⟨⟨h.down, hx⟩⟩

end Skyscraper

section Stalk

variable {x : X} {U : Opens X} {F : 𝓜} {I : Type u}

/-- Families `I → N` are morphisms out of the free module on `I`. -/
noncomputable def piEquivFreeHom (k : Type u) [Ring k] (I : Type u) (N : ModuleCat.{u} k) :
    (I → N) ≃ ((ModuleCat.free k).obj I ⟶ N) where
  toFun g := ModuleCat.freeDesc (TypeCat.ofHom g)
  invFun h i := h (ModuleCat.freeMk i)
  left_inv _ := funext fun i => ModuleCat.freeDesc_apply _ i
  right_inv _ := ModuleCat.free_hom_ext fun i => ModuleCat.freeDesc_apply _ i

/-- If `F|_U ≅ 𝒪_U ^ (⊕ I)` and `x ∈ U`, morphisms out of the stalk `F_x` into an
`𝒪_{X,x}`-module `N` are morphisms out of the free `𝒪_{X,x}`-module on `I`. -/
noncomputable def moduleStalkHomEquivFree (α : F.over U ≅ SheafOfModules.free I) (hx : x ∈ U)
    (N : ModuleCat.{u} (ringSheafStalk R x)) :
    ((moduleStalkFunctor x).obj F ⟶ N) ≃
      ((ModuleCat.free (ringSheafStalk R x)).obj I ⟶ N) :=
  ((moduleStalkSkyscraperAdjunction x).homEquiv F N).trans <|
    (Equiv.ofBijective _ (over_map_bijective_moduleSkyscraper hx F N)).trans <|
    (α.homCongr (Iso.refl _)).trans <|
    (SheafOfModules.freeHomEquiv _).trans <|
    (Equiv.piCongrRight fun _ => skyscraperOverSectionsEquiv hx N).trans <|
    piEquivFreeHom (ringSheafStalk R x) I N

theorem moduleStalkHomEquivFree_comp (α : F.over U ≅ SheafOfModules.free I) (hx : x ∈ U)
    {N N' : ModuleCat.{u} (ringSheafStalk R x)} (f : (moduleStalkFunctor x).obj F ⟶ N)
    (g : N ⟶ N') :
    moduleStalkHomEquivFree α hx N' (f ≫ g) = moduleStalkHomEquivFree α hx N f ≫ g := by
  refine ModuleCat.free_hom_ext fun i => ?_
  change ModuleCat.freeDesc _ (ModuleCat.freeMk i) = g (ModuleCat.freeDesc _ (ModuleCat.freeMk i))
  rw [ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
  rfl

/-- **The stalk of a locally free module.** If `F|_U ≅ 𝒪_U ^ (⊕ I)` and `x ∈ U`, the stalk
`F_x` is the free `𝒪_{X,x}`-module on `I`. -/
noncomputable def moduleStalkIsoFree (α : F.over U ≅ SheafOfModules.free I) (hx : x ∈ U) :
    (moduleStalkFunctor x).obj F ≅ (ModuleCat.free (ringSheafStalk R x)).obj I :=
  (Coyoneda.fullyFaithful.preimageIso
    (NatIso.ofComponents (fun N => (moduleStalkHomEquivFree α hx N).toIso) (fun g => by
      ext f
      exact moduleStalkHomEquivFree_comp α hx f g))).unop.symm

/-- If `F|_U ≅ 𝒪_U ^ (⊕ I)`, `x ∈ U` and the stalk `𝒪_{X,x}` is a nonzero ring, the stalk `F_x`
has rank `#I` over `𝒪_{X,x}`. -/
theorem rank_moduleStalk_eq (α : F.over U ≅ SheafOfModules.free I) (hx : x ∈ U)
    [Nontrivial (ringSheafStalk R x)] :
    Module.rank (ringSheafStalk R x) ((moduleStalkFunctor x).obj F) = Cardinal.mk I := by
  rw [(moduleStalkIsoFree α hx).toLinearEquiv.rank_eq]
  exact rank_finsupp_self' (ringSheafStalk R x)

end Stalk

section Rank

open Classical in
/-- The rank of an `𝒪_X`-module at a point `x`: the cardinal number of copies of `𝒪_U` in a
free presentation `F|_U ≅ 𝒪_U ^ (⊕ I)` on some open neighbourhood `U` of `x` (and `0` if there
is none). Where the stalk `𝒪_{X,x}` is a nonzero ring it does not depend on the choice of
presentation (`rankAt_eq`). -/
noncomputable def rankAt (F : 𝓜) (x : X) : Cardinal.{u} :=
  if h : ∃ (U : Opens X) (I : Type u), x ∈ U ∧ Nonempty (F.over U ≅ SheafOfModules.free I)
  then Cardinal.mk h.choose_spec.choose else 0

/-- The rank is well defined where the stalk of `𝒪_X` is a nonzero ring: on any open `U` with
`F|_U ≅ 𝒪_U ^ (⊕ I)`, the rank at a point `x ∈ U` with `𝒪_{X,x} ≠ 0` is `#I`. -/
theorem rankAt_eq (F : 𝓜) {U : Opens X} {I : Type u} (α : F.over U ≅ SheafOfModules.free I)
    {x : X} (hx : x ∈ U) [Nontrivial (ringSheafStalk R x)] :
    rankAt F x = Cardinal.mk I := by
  have h : ∃ (U : Opens X) (I : Type u), x ∈ U ∧
      Nonempty (F.over U ≅ SheafOfModules.free I) := ⟨U, I, hx, ⟨α⟩⟩
  rw [rankAt, dif_pos h]
  obtain ⟨hx', ⟨α'⟩⟩ := h.choose_spec.choose_spec
  rw [← rank_moduleStalk_eq α' hx', rank_moduleStalk_eq α hx]

/-- **The rank of a locally free module is locally constant** on a ringed space all of whose
stalks `𝒪_{X,x}` are nonzero rings. -/
theorem isLocallyConstant_rankAt [∀ x : X, Nontrivial (ringSheafStalk R x)] (F : 𝓜)
    (hF : IsLocallyFree F) : IsLocallyConstant (rankAt F) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  obtain ⟨U, hxU, I, ⟨α⟩⟩ := hF x
  exact ⟨U, U.2, hxU, fun y hy => (rankAt_eq F α hy).trans (rankAt_eq F α hxU).symm⟩

/-- **The rank of a locally free module on a connected ringed space is constant**, when all the
stalks `𝒪_{X,x}` are nonzero rings. -/
theorem rankAt_eq_of_connectedSpace [ConnectedSpace X] [∀ x : X, Nontrivial (ringSheafStalk R x)]
    (F : 𝓜) (hF : IsLocallyFree F) (x y : X) : rankAt F x = rankAt F y :=
  (isLocallyConstant_rankAt F hF).apply_eq_of_preconnectedSpace x y

end Rank

section ZeroStalk

/-- If the stalk `𝒪_{X,x}` is the zero ring, then `𝒪_X` vanishes on an open neighbourhood `U`
of `x`, and every module over `𝒪_X|_U` is a zero object. -/
theorem exists_isZero_over_of_subsingleton_stalk (x : X) [Subsingleton (ringSheafStalk R x)] :
    ∃ U : Opens X, x ∈ U ∧ (∀ V : Opens X, V ≤ U → Subsingleton (R.obj.obj (op V))) ∧
      ∀ M : SheafOfModules.{u} ((ringCatSheafOf R).over U), IsZero M := by
  have h1 : TopCat.Presheaf.germ R.obj ⊤ x trivial 1 =
      TopCat.Presheaf.germ R.obj ⊤ x trivial 0 :=
    Subsingleton.elim _ _
  obtain ⟨U, hxU, i, j, hij⟩ :=
    TopCat.Presheaf.germ_eq R.obj (U := ⊤) (V := ⊤) x trivial trivial 1 0 h1
  have hU : (1 : R.obj.obj (op U)) = 0 := by simpa using hij
  have hsub : ∀ V : Opens X, V ≤ U → Subsingleton (R.obj.obj (op V)) := fun V hV =>
    subsingleton_of_zero_eq_one (by
      have := congrArg (R.obj.map (homOfLE hV).op).hom hU
      simpa using this.symm)
  refine ⟨U, hxU, hsub, fun M => ?_⟩
  refine (IsZero.iff_id_eq_zero M).mpr ?_
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  have : Subsingleton (((ringCatSheafOf R).over U).val.obj W) :=
    hsub W.unop.left (leOfHom W.unop.hom)
  have : Subsingleton (M.val.obj W) :=
    Module.subsingleton (((ringCatSheafOf R).over U).val.obj W) _
  ext s
  exact Subsingleton.elim _ _

/-- **The stalk hypothesis on the rank is needed.** If the stalk `𝒪_{X,x}` is the zero ring,
then `𝒪_X` vanishes on an open neighbourhood `U` of `x`, where every `𝒪_X`-module is free of
every rank: `F|_U ≅ 𝒪_U ^ (⊕ I)` for every `F` and every index type `I`. -/
theorem exists_over_iso_free_of_subsingleton_stalk (x : X) [Subsingleton (ringSheafStalk R x)] :
    ∃ U : Opens X, x ∈ U ∧ (∀ V : Opens X, V ≤ U → Subsingleton (R.obj.obj (op V))) ∧
      ∀ (F : 𝓜) (I : Type u), Nonempty (F.over U ≅ SheafOfModules.free I) := by
  obtain ⟨U, hxU, hsub, h⟩ := exists_isZero_over_of_subsingleton_stalk (R := R) x
  exact ⟨U, hxU, hsub, fun F I => ⟨(h _).iso (h _)⟩⟩

end ZeroStalk

end Ringed

end Hartshorne

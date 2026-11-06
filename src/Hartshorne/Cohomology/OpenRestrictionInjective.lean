/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.AddCommGrpCat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Injective module sheaves restrict to injectives on open subsets

Hartshorne, *Algebraic Geometry*, III.6, Lemma 6.1 (printed p. 233).

Let `(X, O_X)` be a ringed space (a sheaf of rings `R` on `X`) and `U` an open subset. The
restriction of an `O_X`-module to `U` is the module-sheaf pushforward along the inclusion of
opens `Opens U ⥤ Opens X`, over the restricted structure sheaf `O_U = O_X|_U` whose sections over
an open of `U` are those of `O_X` over the same open. No coherence or finiteness hypothesis is
used.

Following Hartshorne, extension by zero is lifted to modules: for a presheaf of `O_U`-modules
`P`, the presheaf `j_! P` has sections `P(V ∩ U)` over opens `V ⊆ U` and zero over every other
open, with `O_X(V)` acting through the restriction `O_X(V) ⟶ O_X(V ∩ U)`. It is left adjoint to
restriction of presheaves of modules and preserves monomorphisms. Sheafifying it gives a left
adjoint of restriction of module sheaves (Mathlib's construction of the module-sheaf pullback),
which still preserves monomorphisms because sheafification is left exact. The right adjoint of a
monomorphism-preserving functor preserves injective objects.
-/

noncomputable section

open CategoryTheory Opposite TopologicalSpace

namespace Hartshorne

universe u

namespace OpenRestrictionInjective

variable {X : TopCat.{u}} (U : Opens X)

/-- The image of the preimage of an open is contained in it. -/
theorem image_preimage_le (V : Opens X) :
    U.isOpenEmbedding.functor.obj ((Opens.map U.inclusion').obj V) ≤ V := by
  rintro _ ⟨y, hy, rfl⟩
  exact hy

/-- The preimage of the image of an open of `U` is contained in it. -/
theorem preimage_image_le (W : Opens ((Opens.toTopCat X).obj U)) :
    (Opens.map U.inclusion').obj (U.isOpenEmbedding.functor.obj W) ≤ W := by
  rintro y ⟨z, hz, hzy⟩
  have : z = y := Subtype.ext hzy
  exact this ▸ hz

/-- An open contained in `U` is the image of its preimage. -/
theorem le_image_preimage {V : Opens X} (hV : V ≤ U) :
    V ≤ U.isOpenEmbedding.functor.obj ((Opens.map U.inclusion').obj V) :=
  fun x hx => ⟨⟨x, hV hx⟩, hx, rfl⟩

/-- The image of an open of `U` is contained in `U`. -/
theorem image_le (W : Opens ((Opens.toTopCat X).obj U)) :
    U.isOpenEmbedding.functor.obj W ≤ U := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

/-- Over a thin site, two composites of restriction maps with the same ends agree. -/
theorem map_map_eq {T : TopCat.{u}} {S : (Opens T)ᵒᵖ ⥤ RingCat.{u}}
    (M : PresheafOfModules.{u} S) {A B B' C : (Opens T)ᵒᵖ}
    (f : A ⟶ B) (g : B ⟶ C) (f' : A ⟶ B') (g' : B' ⟶ C) (x : M.obj A) :
    M.map g (M.map f x) = M.map g' (M.map f' x) := by
  rw [← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply]
  exact M.congr_map_apply (Subsingleton.elim _ _) x

/-- Over a thin site, a composite of restriction maps from an open to itself is the identity. -/
theorem map_map_self {T : TopCat.{u}} {S : (Opens T)ᵒᵖ ⥤ RingCat.{u}}
    (M : PresheafOfModules.{u} S) {A B : (Opens T)ᵒᵖ}
    (f : A ⟶ B) (g : B ⟶ A) (x : M.obj A) :
    M.map g (M.map f x) = x := by
  rw [← PresheafOfModules.map_comp_apply, M.congr_map_apply (Subsingleton.elim _ (𝟙 A)) x]
  rw [M.map_id]
  rfl

/-- Over a thin site, a composite of ring restriction maps from an open to itself is the
identity. -/
theorem ringMap_map_self {T : TopCat.{u}} (S : (Opens T)ᵒᵖ ⥤ RingCat.{u}) {A B : (Opens T)ᵒᵖ}
    (f : A ⟶ B) (g : B ⟶ A) (r : S.obj A) :
    S.map g (S.map f r) = r := by
  rw [← RingCat.comp_apply, ← S.map_comp, Subsingleton.elim (f ≫ g) (𝟙 A), S.map_id]
  rfl

variable (R : (Opens X)ᵒᵖ ⥤ RingCat.{u})

/-- The restricted ring presheaf on `U`. -/
abbrev ringRestrict : (Opens ((Opens.toTopCat X).obj U))ᵒᵖ ⥤ RingCat.{u} :=
  U.isOpenEmbedding.functor.op ⋙ R

/-- Restriction of rings `R(V) ⟶ R(V ∩ U)`, used to view direct images as `R`-modules. -/
def ringToDirectImage :
    R ⟶ (Opens.map U.inclusion').op ⋙ ringRestrict U R where
  app V := R.map (homOfLE (image_preimage_le U V.unop)).op
  naturality V V' f := by
    dsimp
    rw [← R.map_comp, ← R.map_comp]
    rfl

/-- The direct image of presheaves of modules from `U` to `X`. -/
abbrev directImage :
    PresheafOfModules.{u} (ringRestrict U R) ⥤ PresheafOfModules.{u} R :=
  PresheafOfModules.pushforward (ringToDirectImage U R)

/-- Restriction of presheaves of modules from `X` to `U`. -/
abbrev presheafRestrict :
    PresheafOfModules.{u} R ⥤ PresheafOfModules.{u} (ringRestrict U R) :=
  PresheafOfModules.pushforward (𝟙 (ringRestrict U R))

/-- The sections of the direct image over `V` that are zero unless `V ⊆ U`. -/
def zeroSubmodule (P : PresheafOfModules.{u} (ringRestrict U R)) :
    ((directImage U R).obj P).Submodule where
  obj V :=
    { carrier := {s | V.unop ≤ U ∨ s = 0}
      zero_mem' := Or.inr rfl
      add_mem' := by
        rintro a b (h | rfl) (h' | rfl)
        · exact Or.inl h
        · exact Or.inl h
        · exact Or.inl h'
        · exact Or.inr (add_zero _)
      smul_mem' := by
        rintro r a (h | rfl)
        · exact Or.inl h
        · exact Or.inr (smul_zero _) }
  map {V V'} f := by
    rintro s (h | rfl)
    · exact Or.inl ((leOfHom f.unop).trans h)
    · exact Or.inr (map_zero _)


/-- Extension by zero of a presheaf of modules on `U`: the sections of the direct image over
opens contained in `U`, and zero over every other open. -/
def extendObj (P : PresheafOfModules.{u} (ringRestrict U R)) : PresheafOfModules.{u} R :=
  (zeroSubmodule U R P).toPresheafOfModules

/-- Extension by zero on morphisms. -/
def extendMap {P Q : PresheafOfModules.{u} (ringRestrict U R)} (α : P ⟶ Q) :
    extendObj U R P ⟶ extendObj U R Q where
  app V := ModuleCat.ofHom
    ((((directImage U R).map α).app V).hom.restrict (p := (zeroSubmodule U R P).obj V)
      (q := (zeroSubmodule U R Q).obj V) (by
        rintro s (h | rfl)
        · exact Or.inl h
        · exact Or.inr (map_zero _)))
  naturality {V V'} f := by
    ext s
    exact Subtype.ext (PresheafOfModules.naturality_apply ((directImage U R).map α) f s.1)

/-- Extension by zero of presheaves of modules from `U` to `X`. -/
def extend : PresheafOfModules.{u} (ringRestrict U R) ⥤ PresheafOfModules.{u} R where
  obj := extendObj U R
  map := extendMap U R
  map_id P := by
    ext V s
    rfl
  map_comp α β := by
    ext V s
    rfl


/-- The unit `P ⟶ (j_! P)|_U`. -/
def unitApp (P : PresheafOfModules.{u} (ringRestrict U R)) :
    P ⟶ (presheafRestrict U R).obj ((extend U R).obj P) where
  app W := ModuleCat.ofHom
    { toFun := fun x => ⟨P.map (homOfLE (preimage_image_le U W.unop)).op x,
        Or.inl (image_le U W.unop)⟩
      map_add' := fun x y => Subtype.ext (map_add _ x y)
      map_smul' := fun r x => Subtype.ext ((P.map _).hom.map_smul r x) }
  naturality {W W'} f := by
    ext x
    apply Subtype.ext
    exact map_map_eq P _ _ _ _ x


open Classical in
/-- The underlying map of the counit `j_!(M|_U) ⟶ M` over `V`: restriction from `V ∩ U` to
`V` when `V ⊆ U`, and zero otherwise (where the source is zero). -/
def counitFun (M : PresheafOfModules.{u} R) (V : (Opens X)ᵒᵖ)
    (s : M.obj (op (U.isOpenEmbedding.functor.obj ((Opens.map U.inclusion').obj V.unop)))) :
    M.obj V :=
  if h : V.unop ≤ U then M.map (homOfLE (le_image_preimage U h)).op s else 0

theorem counitFun_of_le (M : PresheafOfModules.{u} R) (V : (Opens X)ᵒᵖ) (h : V.unop ≤ U)
    (s : M.obj (op (U.isOpenEmbedding.functor.obj ((Opens.map U.inclusion').obj V.unop)))) :
    counitFun U R M V s = M.map (homOfLE (le_image_preimage U h)).op s :=
  dif_pos h

theorem counitFun_of_not_le (M : PresheafOfModules.{u} R) (V : (Opens X)ᵒᵖ) (h : ¬ V.unop ≤ U)
    (s : M.obj (op (U.isOpenEmbedding.functor.obj ((Opens.map U.inclusion').obj V.unop)))) :
    counitFun U R M V s = 0 :=
  dif_neg h

set_option backward.isDefEq.respectTransparency false in
/-- The counit `j_!(M|_U) ⟶ M`. -/
def counitApp (M : PresheafOfModules.{u} R) :
    (extend U R).obj ((presheafRestrict U R).obj M) ⟶ M where
  app V := ModuleCat.ofHom
    { toFun := fun s => counitFun U R M V s.1
      map_add' := fun s t => by
        unfold counitFun
        split_ifs with h
        · exact (M.map _).hom.map_add _ _
        · exact (add_zero 0).symm
      map_smul' := fun r s => by
        unfold counitFun
        split_ifs with h
        · refine ((M.map (homOfLE (le_image_preimage U h)).op).hom.map_smul
            ((ringToDirectImage U R).app V r)
            (show M.obj (op (U.isOpenEmbedding.functor.obj
              ((Opens.map U.inclusion').obj V.unop))) from s.1)).trans ?_
          change ((R.map (homOfLE (le_image_preimage U h)).op) ((ringToDirectImage U R).app V r) :
            R.obj V) • (_ : M.obj V) = r • (_ : M.obj V)
          dsimp only [ringToDirectImage]
          erw [ringMap_map_self]
        · exact (smul_zero r).symm }
  naturality {V V'} f := by
    ext ⟨s, hs⟩
    change counitFun U R M V'
      (M.map (U.isOpenEmbedding.functor.map ((Opens.map U.inclusion').map f.unop)).op
        (show M.obj (op (U.isOpenEmbedding.functor.obj ((Opens.map U.inclusion').obj V.unop)))
          from s)) = M.map f (counitFun U R M V s)
    by_cases h : V.unop ≤ U
    · have h' : V'.unop ≤ U := (leOfHom f.unop).trans h
      rw [counitFun_of_le U R M V' h', counitFun_of_le U R M V h]
      exact map_map_eq M _ _ _ _
        (show M.obj (op (U.isOpenEmbedding.functor.obj ((Opens.map U.inclusion').obj V.unop)))
          from s)
    · obtain h'' | rfl := hs
      · exact absurd h'' h
      · rw [counitFun_of_not_le U R M V h, map_zero, map_zero]
        unfold counitFun
        split_ifs
        · exact map_zero _
        · rfl


set_option backward.isDefEq.respectTransparency false in
/-- Extension by zero is left adjoint to restriction, for presheaves of modules. -/
def extendAdjunction : extend U R ⊣ presheafRestrict U R where
  unit :=
    { app := unitApp U R
      naturality {P Q} α := by
        ext W x
        apply Subtype.ext
        exact (PresheafOfModules.naturality_apply α
          (homOfLE (preimage_image_le U W.unop)).op x).symm }
  counit :=
    { app := counitApp U R
      naturality {M N} β := by
        ext V ⟨s, hs⟩
        change counitFun U R N V (β.app _ s) = β.app V (counitFun U R M V s)
        by_cases h : V.unop ≤ U
        · rw [counitFun_of_le U R N V h, counitFun_of_le U R M V h]
          exact (PresheafOfModules.naturality_apply β (homOfLE (le_image_preimage U h)).op
            (show M.obj (op (U.isOpenEmbedding.functor.obj
              ((Opens.map U.inclusion').obj V.unop))) from s)).symm
        · rw [counitFun_of_not_le U R N V h, counitFun_of_not_le U R M V h, map_zero] }
  left_triangle_components P := by
    ext V ⟨s, hs⟩
    apply Subtype.ext
    change (counitFun U R ((extend U R).obj P) V
      ⟨P.map (homOfLE (preimage_image_le U _)).op s, Or.inl (image_le U _)⟩).1 = s
    by_cases h : V.unop ≤ U
    · rw [counitFun_of_le U R _ V h]
      exact map_map_self P _ _ s
    · rw [counitFun_of_not_le U R _ V h]
      obtain h'' | rfl := hs
      · exact absurd h'' h
      · rfl
  right_triangle_components M := by
    ext W x
    change counitFun U R M (op (U.isOpenEmbedding.functor.obj W.unop))
      (M.map (U.isOpenEmbedding.functor.map (homOfLE (preimage_image_le U W.unop))).op
        (show M.obj (op (U.isOpenEmbedding.functor.obj W.unop)) from x)) = x
    rw [counitFun_of_le U R M _ (image_le U W.unop)]
    exact map_map_self M _ _ (show M.obj (op (U.isOpenEmbedding.functor.obj W.unop)) from x)


/-- Extension by zero preserves monomorphisms of presheaves of modules. -/
instance extend_preservesMonomorphisms : (extend U R).PreservesMonomorphisms where
  preserves {_ _} α _ := PresheafOfModules.mono_of_injective fun V _ _ hst =>
    Subtype.ext (PresheafOfModules.injective_of_mono ((directImage U R).map α) V
      (congrArg Subtype.val hst))

end OpenRestrictionInjective

open OpenRestrictionInjective

variable {X : TopCat.{u}} (U : Opens X)

instance openFunctor_isContinuous :
    U.isOpenEmbedding.functor.IsContinuous
      (Opens.grothendieckTopology ((Opens.toTopCat X).obj U)) (Opens.grothendieckTopology X) :=
  Topology.IsOpenEmbedding.functor_isContinuous U.isOpenEmbedding

variable (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- The restricted structure sheaf `O_X|_U` on `U`: its sections over an open of `U` are the
sections of `O_X` over the same open regarded in `X`. -/
def restrictedRingSheaf :
    Sheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U)) RingCat.{u} :=
  (U.isOpenEmbedding.functor.sheafPushforwardContinuous RingCat.{u} _ _).obj R

/-- The identification of `O_U` with the pushforward of `O_X` along the inclusion of opens. -/
def restrictedRingHom : restrictedRingSheaf U R ⟶
    (U.isOpenEmbedding.functor.sheafPushforwardContinuous RingCat.{u} _ _).obj R :=
  𝟙 _

/-- Restriction of `O_X`-modules to `O_U`-modules, along the restricted structure sheaf. -/
def moduleSheafRestrict : SheafOfModules.{u} R ⥤ SheafOfModules.{u} (restrictedRingSheaf U R) :=
  SheafOfModules.pushforward (restrictedRingHom U R)

instance : (PresheafOfModules.pushforward.{u} (restrictedRingHom U R).hom).IsRightAdjoint :=
  ⟨_, ⟨extendAdjunction U R.obj⟩⟩

/-- **Hartshorne III.6, Lemma 6.1.** For an open subset `U` of a ringed space `(X, O_X)`, the
restriction of an injective `O_X`-module to `U` is an injective `O_U`-module. -/
theorem injective_moduleSheafRestrict_obj (J : SheafOfModules.{u} R) [Injective J] :
    Injective ((moduleSheafRestrict U R).obj J) := by
  let φ := restrictedRingHom U R
  let adj := SheafOfModules.PullbackConstruction.adjunction.{u} φ
  have e : PresheafOfModules.pullback.{u} φ.hom ≅ extend U R.obj :=
    (PresheafOfModules.pullbackPushforwardAdjunction φ.hom).leftAdjointUniq
      (extendAdjunction U R.obj)
  have : (PresheafOfModules.pullback.{u} φ.hom).PreservesMonomorphisms :=
    @Functor.PreservesMonomorphisms.of_iso _ _ _ _ _ _ (extend_preservesMonomorphisms U R.obj)
      e.symm
  exact adj.map_injective J inferInstance


end Hartshorne

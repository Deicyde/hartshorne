/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.RingedSpace.SheafExtContravariant
import Hartshorne.RingedSpace.SheafExtFiniteLocallyFree

/-!
# Dualizing a short exact sequence

Let `(X, 𝒪_X)` be a ringed space and `0 ⟶ F' ⟶ F ⟶ F'' ⟶ 0` a short exact sequence of
`𝒪_X`-modules with `F''` locally free of finite rank. Then the dual sequence

`0 ⟶ F''^∨ ⟶ F^∨ ⟶ F'^∨ ⟶ 0`

is short exact (`Hartshorne.Ringed.dualShortComplex_shortExact`): the contravariant sequence of
`ℋom(-, 𝒪_X)` (Hartshorne III.6, Proposition 6.4) continues with `ℰxt¹(F'', 𝒪_X)`, which vanishes
because `F''` is finite locally free. This is the step "taking the dual of the exact sequence"
of Hartshorne II, Example 8.20.1.

We also record that the dual of a finite direct sum is the direct sum of the duals
(`Hartshorne.Ringed.moduleSheafHomBiproductIso`), using that precomposition is additive
(`Hartshorne.Ringed.moduleSheafHomPrecomp_add`).
-/

universe u

open CategoryTheory Limits Opposite

namespace Hartshorne

namespace Ringed

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

set_option hygiene false in
/-- `𝒪_X`-modules. -/
local notation "𝓜" => SheafOfModules.{u} (ringCatSheafOf R)

/- As in `Hartshorne.RingedSpace.SheafExt`, elaborate with the preadditive structure coming from
the abelian structure. -/
attribute [local instance 2000] Abelian.toPreadditive

section Precomp

/-- Precomposition with an identity is the identity. -/
lemma moduleSheafHomPrecomp_id_app (F G : 𝓜) :
    (moduleSheafHomPrecomp (𝟙 F)).app G = 𝟙 _ :=
  NatTrans.congr_app ((moduleSheafHomBifunctor R).map_id (op F)) G

/-- Precomposition is contravariantly functorial. -/
lemma moduleSheafHomPrecomp_comp_app {F'' F' F : 𝓜} (f : F'' ⟶ F') (g : F' ⟶ F) (G : 𝓜) :
    (moduleSheafHomPrecomp g).app G ≫ (moduleSheafHomPrecomp f).app G =
      (moduleSheafHomPrecomp (f ≫ g)).app G :=
  (NatTrans.congr_app ((moduleSheafHomBifunctor R).map_comp g.op f.op) G).symm

/-- Restriction to an open is additive. -/
lemma over_map_add {F' F : 𝓜} (f g : F' ⟶ F) (U : TopologicalSpace.Opens X) :
    (SheafOfModules.overFunctor (ringCatSheafOf R) U).map (f + g) =
      (SheafOfModules.overFunctor (ringCatSheafOf R) U).map f +
        (SheafOfModules.overFunctor (ringCatSheafOf R) U).map g :=
  rfl

/-- Precomposition is additive. -/
lemma moduleSheafHomPrecomp_add_app {F' F : 𝓜} (f g : F' ⟶ F) (G : 𝓜) :
    (moduleSheafHomPrecomp (f + g)).app G =
      (moduleSheafHomPrecomp f).app G + (moduleSheafHomPrecomp g).app G := by
  apply SheafOfModules.hom_ext
  ext U σ
  obtain ⟨τ, rfl⟩ : ∃ τ : F.over U.unop ⟶ G.over U.unop, τ = σ := ⟨σ, rfl⟩
  change (SheafOfModules.overFunctor.{u} (ringCatSheafOf R) U.unop).map (f + g) ≫ τ ≫
      (SheafOfModules.overFunctor.{u} (ringCatSheafOf R) U.unop).map (𝟙 G) =
    (SheafOfModules.overFunctor.{u} (ringCatSheafOf R) U.unop).map f ≫ τ ≫
        (SheafOfModules.overFunctor.{u} (ringCatSheafOf R) U.unop).map (𝟙 G) +
      (SheafOfModules.overFunctor.{u} (ringCatSheafOf R) U.unop).map g ≫ τ ≫
        (SheafOfModules.overFunctor.{u} (ringCatSheafOf R) U.unop).map (𝟙 G)
  rw [over_map_add, Preadditive.add_comp]

/-- Precomposition, as an additive map on morphisms. -/
noncomputable def moduleSheafHomPrecompAddHom (F' F G : 𝓜) :
    (F' ⟶ F) →+ (moduleSheafHom F G ⟶ moduleSheafHom F' G) where
  toFun f := (moduleSheafHomPrecomp f).app G
  map_zero' := by rw [moduleSheafHomPrecomp_zero]; rfl
  map_add' f g := moduleSheafHomPrecomp_add_app f g G

/-- Precomposition commutes with finite sums. -/
lemma moduleSheafHomPrecomp_sum_app {ι : Type*} (s : Finset ι) {F' F : 𝓜} (f : ι → (F' ⟶ F))
    (G : 𝓜) :
    (moduleSheafHomPrecomp (∑ i ∈ s, f i)).app G = ∑ i ∈ s, (moduleSheafHomPrecomp (f i)).app G :=
  map_sum (moduleSheafHomPrecompAddHom F' F G) f s

/-- **The dual of a finite direct sum is the direct sum of the duals**, and more generally
`ℋom(⨁ᵢ Fᵢ, G) ≅ ⨁ᵢ ℋom(Fᵢ, G)`. -/
noncomputable def moduleSheafHomBiproductIso {ι : Type} [Fintype ι] (F : ι → 𝓜)
    [hF : HasBiproduct F] (G : 𝓜) [hG : HasBiproduct fun i ↦ (moduleSheafHomFunctor (F i)).obj G] :
    (moduleSheafHomFunctor (⨁ F)).obj G ≅ ⨁ fun i ↦ (moduleSheafHomFunctor (F i)).obj G where
  hom := biproduct.lift fun i ↦ (moduleSheafHomPrecomp (biproduct.ι F i)).app G
  inv := biproduct.desc fun i ↦ (moduleSheafHomPrecomp (biproduct.π F i)).app G
  hom_inv_id := by
    refine (biproduct.lift_desc (f := fun i : ι ↦ (moduleSheafHomFunctor (F i)).obj G)
      (T := (moduleSheafHomFunctor (⨁ F)).obj G) (U := (moduleSheafHomFunctor (⨁ F)).obj G)
      (g := fun i : ι ↦ (moduleSheafHomPrecomp (biproduct.ι F i)).app G)
      (h := fun i : ι ↦ (moduleSheafHomPrecomp (biproduct.π F i)).app G)).trans ?_
    simp_rw [moduleSheafHomPrecomp_comp_app]
    rw [← moduleSheafHomPrecomp_sum_app, biproduct.total, moduleSheafHomPrecomp_id_app]
  inv_hom_id := by
    classical
    refine biproduct.hom_ext _ _ fun j ↦ biproduct.hom_ext' _ _ fun i ↦ ?_
    rw [Category.assoc, biproduct.lift_π, biproduct.ι_desc_assoc,
      moduleSheafHomPrecomp_comp_app, Category.id_comp]
    by_cases h : i = j
    · subst h
      rw [biproduct.ι_π_self, biproduct.ι_π_self, moduleSheafHomPrecomp_id_app]
    · rw [biproduct.ι_π_ne _ (Ne.symm h), biproduct.ι_π_ne _ h, moduleSheafHomPrecomp_zero]
      rfl

end Precomp

section Dual

/-- The dual `0 ⟶ F''^∨ ⟶ F^∨ ⟶ F'^∨ ⟶ 0` of a complex `F' ⟶ F ⟶ F''`, the maps being
precomposition. -/
noncomputable abbrev dualShortComplex (S : ShortComplex 𝓜) : ShortComplex 𝓜 :=
  ShortComplex.mk ((moduleSheafHomPrecomp S.g).app (structureModule R))
    ((moduleSheafHomPrecomp S.f).app (structureModule R))
    (moduleSheafHomPrecomp_g_comp_f (structureModule R))

/-- **Dualizing a short exact sequence.** If `0 ⟶ F' ⟶ F ⟶ F'' ⟶ 0` is short exact and `F''` is
locally free of finite rank, then `0 ⟶ F''^∨ ⟶ F^∨ ⟶ F'^∨ ⟶ 0` is short exact. -/
theorem dualShortComplex_shortExact {S : ShortComplex 𝓜} (hS : S.ShortExact)
    (h₃ : IsFiniteLocallyFree S.X₃) : (dualShortComplex S).ShortExact := by
  have hepi := (sheafHom_contra_exact₃ hS (structureModule R)).epi_f
    ((isZero_sheafExt_of_isFiniteLocallyFree h₃ (structureModule R) one_pos).eq_of_tgt _ _)
  have hmono := sheafHom_contra_mono hS (structureModule R)
  exact { exact := sheafHom_contra_exact₂ hS (structureModule R) }

end Dual

end Ringed

end Hartshorne

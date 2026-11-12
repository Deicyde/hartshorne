/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.AlgebraizableFormalScheme
import Hartshorne.Scheme.FormalCompletionAffineSections
import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant

/-!
# Schemes as formal schemes

Hartshorne, *Algebraic Geometry*, II.9, Example 9.3.3 (p. 195): if a Noetherian scheme `X` is
completed along the closed subscheme `Y = X`, the completion is `X` itself; so every Noetherian
scheme is a Noetherian formal scheme.

The closed subscheme `Y = X` is cut out by the zero ideal sheaf `0 ⊆ 𝒪_X`. All the
infinitesimal neighbourhoods `Y_(n+1)`, cut out by `0 ^ (n + 1) = 0`, map isomorphically onto `X`,
so the inverse system `n ↦ 𝒪_X / 0 ^ (n + 1)` has isomorphisms as transition maps and its limit is
`𝒪_X`.

* `Hartshorne.QuasicoherentIdealSubsheaf.instBot`: the zero ideal subsheaf `⊥` of `𝒪_X`, with
  `Hartshorne.QuasicoherentIdealSubsheaf.ideal_bot` (its ideals are zero on every open).
* `Hartshorne.QuasicoherentIdealSubsheaf.isIso_infinitesimalNeighborhoodι_bot`: the closed
  immersions `Y_(n+1) ⟶ X` are isomorphisms.
* `Hartshorne.QuasicoherentIdealSubsheaf.formalCompletionCanonicalHom I`: the canonical morphism
  `X̂_Y ⟶ X` of ringed spaces, for any quasi-coherent ideal subsheaf `I`: the closed immersion
  `|Y| ⟶ |X|` on spaces and the canonical maps `Γ(U, 𝒪_X) → Γ(U ∩ |Y|, 𝒪_{X̂_Y})` on sections.
* `Hartshorne.QuasicoherentIdealSubsheaf.formalCompletionBotIso X`: the isomorphism of locally
  ringed spaces `X̂ ≅ X` from the completion of `X` along `Y = X`; its underlying morphism is the
  canonical morphism (`formalCompletionBotIso_hom_toPresheafedSpace`).
* `Hartshorne.NoetherianFormalScheme.ofScheme X`: a Noetherian scheme `X` as a Noetherian formal
  scheme, with `Hartshorne.NoetherianFormalScheme.toNoetherianFormalSchemeBotIso X`, the
  isomorphism from the completion of `X` along itself.
* `Hartshorne.NoetherianFormalScheme.fromNoetherianScheme`: the functor from Noetherian schemes to
  Noetherian formal schemes, fully faithful
  (`Hartshorne.NoetherianFormalScheme.fullyFaithfulFromNoetherianScheme`).

The isomorphism `X̂ ≅ X` is constructed for every scheme; Hartshorne states it for Noetherian `X`.
-/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Topology Opposite TopologicalSpace

open Hartshorne.ArtinReesKernelSheaf

namespace Hartshorne

universe u

namespace QuasicoherentIdealSubsheaf

variable {X : Scheme.{u}}

/-- The zero ideal subsheaf of `𝒪_X`, cutting out the closed subscheme `Y = X`: the subsheaf
corresponding to the zero ideal data. -/
instance instBot : Bot (QuasicoherentIdealSubsheaf X) :=
  ⟨quasicoherentIdealSubsheafEquiv.symm ⊥⟩

/-- The zero ideal subsheaf corresponds to the zero ideal data. -/
lemma quasicoherentIdealSubsheafEquiv_bot :
    quasicoherentIdealSubsheafEquiv (⊥ : QuasicoherentIdealSubsheaf X) = ⊥ :=
  Equiv.apply_symm_apply _ _

/-- The ideals of the zero ideal subsheaf on affine opens are zero. -/
lemma ideal_bot_affine (U : X.affineOpens) :
    (⊥ : QuasicoherentIdealSubsheaf X).ideal U = ⊥ :=
  ideal_idealSheafDataToSubsheaf ⊥ U

/-- **The zero ideal subsheaf is zero**: its ideal of sections over every open is zero. -/
theorem ideal_bot (U : X.Opens) : (⊥ : QuasicoherentIdealSubsheaf X).ideal U = ⊥ := by
  refine eq_bot_iff.mpr fun s hs => ?_
  refine TopCat.Presheaf.section_ext X.sheaf U s 0 fun x hx => ?_
  obtain ⟨V, hVU, hxV⟩ := exists_affine_le hx
  have h1 := res_mem (E := (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (⊥ : QuasicoherentIdealSubsheaf X).carrier hVU hs
  change _ ∈ (⊥ : QuasicoherentIdealSubsheaf X).ideal V at h1
  rw [ideal_bot_affine V] at h1
  have h2 : X.presheaf.map (homOfLE hVU).op s = 0 := h1
  change X.presheaf.germ U x hx s = X.presheaf.germ U x hx 0
  rw [← X.presheaf.germ_res_apply (homOfLE hVU) x hxV s, h2, map_zero, map_zero]

/-- The ideal data of `0 ^ (n + 1)` is zero. -/
lemma quasicoherentIdealSubsheafEquiv_bot_pow_succ (n : ℕ) :
    quasicoherentIdealSubsheafEquiv ((⊥ : QuasicoherentIdealSubsheaf X) ^ (n + 1)) = ⊥ := by
  rw [quasicoherentIdealSubsheafEquiv_pow, quasicoherentIdealSubsheafEquiv_bot]
  refine Scheme.IdealSheafData.ext (funext fun U => ?_)
  simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Scheme.IdealSheafData.ideal_bot,
    Pi.bot_apply]
  exact Ideal.bot_pow (Nat.succ_ne_zero n)

/-- **`Y_(n+1) = X` for `Y = X`**: the closed immersion of the `(n+1)`-st infinitesimal
neighbourhood along the zero ideal is an isomorphism. -/
instance isIso_infinitesimalNeighborhoodι_bot (n : ℕ) :
    IsIso ((⊥ : QuasicoherentIdealSubsheaf X).infinitesimalNeighborhoodι (n + 1)) :=
  (Scheme.isIso_subschemeι_iff_eq_bot _).mpr
    (quasicoherentIdealSubsheafEquiv_bot_pow_succ n)

/-- Along the zero ideal, the inclusions `Y_(n+1) ⟶ Y_(n+2)` are isomorphisms. -/
instance isIso_infinitesimalNeighborhoodSucc_bot (n : ℕ) :
    IsIso ((⊥ : QuasicoherentIdealSubsheaf X).infinitesimalNeighborhoodSucc n) := by
  have h1 := isIso_infinitesimalNeighborhoodι_bot (X := X) n
  have h2 := isIso_infinitesimalNeighborhoodι_bot (X := X) (n + 1)
  exact IsIso.of_isIso_fac_right
    ((⊥ : QuasicoherentIdealSubsheaf X).infinitesimalNeighborhoodSucc_comp_ι n)

/-- The map `f.appLE U V e` of an isomorphism of schemes is an isomorphism when `V` is the whole
preimage of `U`. -/
private lemma isIso_appLE_of_eq {A B : Scheme.{u}} (f : A ⟶ B) [IsIso f] {U : B.Opens}
    {V : A.Opens} (e : V ≤ f ⁻¹ᵁ U) (h : V = f ⁻¹ᵁ U) : IsIso (f.appLE U V e) := by
  rw [Scheme.Hom.appLE, show homOfLE e = eqToHom h from Subsingleton.elim _ _, eqToHom_op,
    eqToHom_map]
  exact IsIso.comp_isIso' inferInstance (Iso.isIso_hom (eqToIso (by rw [h])))

/-- Along the zero ideal, the image of `V` in `Y_(n+1)` is the preimage of its image in
`Y_(n+2)`. -/
private lemma preimage_infinitesimalNeighborhoodSucc_bot (n : ℕ)
    (V : Opens ((⊥ : QuasicoherentIdealSubsheaf X).infinitesimalNeighborhood 1)) :
    (⊥ : QuasicoherentIdealSubsheaf X).infinitesimalNeighborhoodSucc n ⁻¹ᵁ
        ((⊥ : QuasicoherentIdealSubsheaf X).isOpenEmbedding_infinitesimalNeighborhoodFromOne
          (n + 1)).functor.obj V =
      ((⊥ : QuasicoherentIdealSubsheaf X).isOpenEmbedding_infinitesimalNeighborhoodFromOne
        n).functor.obj V := by
  refine le_antisymm (fun z hz => ?_)
    ((⊥ : QuasicoherentIdealSubsheaf X).functor_obj_le_preimage_infinitesimalNeighborhoodSucc n V)
  obtain ⟨y, hy, hyz⟩ := hz
  refine ⟨y, hy, ?_⟩
  have hinj := ((⊥ : QuasicoherentIdealSubsheaf X).infinitesimalNeighborhoodSucc
    n).isOpenEmbedding.injective
  apply hinj
  rw [← hyz, ← Scheme.Hom.comp_apply, infinitesimalNeighborhoodFromOne_comp_succ]

/-- Along the zero ideal, the transition maps `𝒪_X / 0 ^ (n + 2) ⟶ 𝒪_X / 0 ^ (n + 1)` are
isomorphisms. -/
instance isIso_formalCompletionSheafMap_bot (n : ℕ) :
    IsIso ((⊥ : QuasicoherentIdealSubsheaf X).formalCompletionSheafMap n) := by
  have : IsIso ((⊥ : QuasicoherentIdealSubsheaf X).formalCompletionSheafMap n).hom := by
    have hV : ∀ V, IsIso (((⊥ : QuasicoherentIdealSubsheaf X).formalCompletionSheafMap
        n).hom.app V) := by
      intro V
      rw [formalCompletionSheafMap_hom_app]
      exact isIso_appLE_of_eq _ _ (preimage_infinitesimalNeighborhoodSucc_bot n V.unop).symm
    exact NatIso.isIso_of_isIso_app _
  have : IsIso ((sheafToPresheaf _ CommRingCat.{u}).map
      ((⊥ : QuasicoherentIdealSubsheaf X).formalCompletionSheafMap n)) := this
  exact isIso_of_fully_faithful (sheafToPresheaf _ _) _

/-- Along the zero ideal, all the maps of the inverse system `n ↦ 𝒪_X / 0 ^ (n + 1)` to its
first term are isomorphisms. -/
lemma isEventuallyConstantTo_formalCompletionDiagram_bot :
    (⊥ : QuasicoherentIdealSubsheaf X).formalCompletionDiagram.IsEventuallyConstantTo (op 0) := by
  have key : ∀ m : ℕ, IsIso ((⊥ : QuasicoherentIdealSubsheaf X).formalCompletionDiagram.map
      (homOfLE (Nat.zero_le m)).op) := by
    intro m
    induction m with
    | zero =>
      rw [show (homOfLE (Nat.zero_le 0)).op = 𝟙 (op 0) from Subsingleton.elim _ _,
        CategoryTheory.Functor.map_id]
      infer_instance
    | succ m ih =>
      rw [show (homOfLE (Nat.zero_le (m + 1))).op =
          (homOfLE (Nat.le_add_right m 1)).op ≫ (homOfLE (Nat.zero_le m)).op from
          Subsingleton.elim _ _, CategoryTheory.Functor.map_comp, formalCompletionDiagram,
        Functor.ofOpSequence_map_homOfLE_succ]
      exact IsIso.comp_isIso' (isIso_formalCompletionSheafMap_bot m) ih
  intro i f
  rw [show f = (homOfLE (Nat.zero_le i.unop)).op from Subsingleton.elim _ _]
  exact key i.unop

/-- Along the zero ideal, the projection `lim_n 𝒪_X / 0 ^ (n + 1) ⟶ 𝒪_X / 0` is an
isomorphism. -/
theorem isIso_limit_π_formalCompletionDiagram_bot :
    IsIso (limit.π (⊥ : QuasicoherentIdealSubsheaf X).formalCompletionDiagram (op 0)) :=
  isEventuallyConstantTo_formalCompletionDiagram_bot.isIso_π_of_isLimit (limit.isLimit _)

/-- The canonical maps `Γ(U, 𝒪_X) → Γ(U, lim_n 𝒪_X / 0 ^ (n + 1))` are isomorphisms. -/
instance isIso_formalCompletionSectionsMap_bot (U : X.Opens) :
    IsIso ((⊥ : QuasicoherentIdealSubsheaf X).formalCompletionSectionsMap U) := by
  have h0 : IsIso ((limit.π (⊥ : QuasicoherentIdealSubsheaf X).formalCompletionDiagram
      (op 0)).hom.app
        (op ((⊥ : QuasicoherentIdealSubsheaf X).infinitesimalNeighborhoodι 1 ⁻¹ᵁ U))) :=
    Iso.isIso_hom (((sheafToPresheaf _ _).mapIso
      (@asIso _ _ _ _ (limit.π (⊥ : QuasicoherentIdealSubsheaf X).formalCompletionDiagram (op 0))
        isIso_limit_π_formalCompletionDiagram_bot)).app _)
  have h1 : IsIso ((⊥ : QuasicoherentIdealSubsheaf X).formalCompletionSheafObjSectionsMap 0 U) :=
    isIso_appLE_of_eq _ _
      ((⊥ : QuasicoherentIdealSubsheaf X).functor_obj_preimage_infinitesimalNeighborhoodι 0 U)
  exact @IsIso.of_isIso_fac_right _ _ _ _ _ _ _ _ (by exact h0) (by exact h1)
    ((⊥ : QuasicoherentIdealSubsheaf X).formalCompletionSectionsMap_π U 0)

section Canonical

variable (I : QuasicoherentIdealSubsheaf X)

/-- **The canonical morphism** `X̂_Y ⟶ X` of ringed spaces from the formal completion along the
closed subscheme `Y` cut out by `I`: on spaces the closed immersion `|Y| ⟶ |X|`, on sections the
canonical maps `Γ(U, 𝒪_X) → Γ(U ∩ |Y|, lim_n 𝒪_X / I ^ (n + 1))` induced by the restrictions to the
infinitesimal neighbourhoods `Y_(n+1)`. -/
def formalCompletionCanonicalHom :
    I.formalCompletion.toPresheafedSpace ⟶ X.toPresheafedSpace where
  base := (I.infinitesimalNeighborhoodι 1).base
  c :=
    { app U := I.formalCompletionSectionsMap U.unop
      naturality _ _ f := (I.formalCompletionSectionsMap_naturality (leOfHom f.unop)).symm }

end Canonical

/-- Along the zero ideal, the canonical morphism `X̂ ⟶ X` is an isomorphism on structure
sheaves. -/
instance isIso_formalCompletionCanonicalHom_c_bot :
    IsIso (formalCompletionCanonicalHom (⊥ : QuasicoherentIdealSubsheaf X)).c :=
  @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _
    fun U => isIso_formalCompletionSectionsMap_bot (X := X) U.unop

/-- The homeomorphism `|Y| ≅ |X|` for `Y = X`, the closed immersion `Y_1 ⟶ X`. -/
private def botBaseIso :
    ((⊥ : QuasicoherentIdealSubsheaf X).infinitesimalNeighborhood 1).toTopCat ≅ X.toTopCat where
  hom := ((⊥ : QuasicoherentIdealSubsheaf X).infinitesimalNeighborhoodι 1).base
  inv := (inv ((⊥ : QuasicoherentIdealSubsheaf X).infinitesimalNeighborhoodι 1)).base
  hom_inv_id := by rw [← Scheme.Hom.comp_base, IsIso.hom_inv_id, Scheme.Hom.id_base]; rfl
  inv_hom_id := by rw [← Scheme.Hom.comp_base, IsIso.inv_hom_id, Scheme.Hom.id_base]; rfl

variable (X) in
/-- **Schemes as formal schemes** (Hartshorne II.9, Example 9.3.3, p. 195, there for Noetherian
`X`): the completion `X̂` of `X` along the closed subscheme `Y = X`, cut out by the zero ideal, is
isomorphic to `X` as a locally ringed space, by the canonical morphism `X̂ ⟶ X`
(`formalCompletionBotIso_hom_toPresheafedSpace`). Here `X` is any scheme. -/
def formalCompletionBotIso :
    (⊥ : QuasicoherentIdealSubsheaf X).formalCompletion ≅ X.toLocallyRingedSpace :=
  LocallyRingedSpace.isoOfSheafedSpaceIso (SheafedSpace.isoMk
    (PresheafedSpace.isoOfComponents botBaseIso
      (asIso (formalCompletionCanonicalHom (⊥ : QuasicoherentIdealSubsheaf X)).c).symm))

/-- The isomorphism `X̂ ≅ X` is the canonical morphism `X̂ ⟶ X`. -/
lemma formalCompletionBotIso_hom_toPresheafedSpace :
    (formalCompletionBotIso X).hom.toShHom.hom =
      formalCompletionCanonicalHom (⊥ : QuasicoherentIdealSubsheaf X) :=
  rfl

/-- On points, the isomorphism `X̂ ≅ X` is the closed immersion `Y_1 ⟶ X`. -/
lemma formalCompletionBotIso_hom_base_apply
    (y : (⊥ : QuasicoherentIdealSubsheaf X).formalCompletion) :
    (formalCompletionBotIso X).hom.base y =
      (⊥ : QuasicoherentIdealSubsheaf X).infinitesimalNeighborhoodι 1 y :=
  rfl

/-- On sections, the isomorphism `X̂ ≅ X` is the canonical map
`Γ(U, 𝒪_X) → Γ(U, lim_n 𝒪_X / 0 ^ (n + 1))`. -/
lemma formalCompletionBotIso_hom_c_app (U : X.Opens) :
    (formalCompletionBotIso X).hom.c.app (op U) =
      (⊥ : QuasicoherentIdealSubsheaf X).formalCompletionSectionsMap U :=
  rfl

end QuasicoherentIdealSubsheaf

/-- **Noetherian schemes are Noetherian formal schemes** (Hartshorne II.9, Example 9.3.3,
p. 195): a Noetherian scheme is isomorphic, as a locally ringed space, to its completion along
itself. -/
theorem isNoetherianFormalScheme_toLocallyRingedSpace (X : Scheme.{u}) [IsNoetherian X] :
    IsNoetherianFormalScheme X.toLocallyRingedSpace :=
  ((⊥ : QuasicoherentIdealSubsheaf X).isNoetherianFormalScheme_formalCompletion).of_iso
    (QuasicoherentIdealSubsheaf.formalCompletionBotIso X).symm

namespace NoetherianFormalScheme

/-- A Noetherian scheme as a Noetherian formal scheme (Hartshorne II.9, Example 9.3.3,
p. 195). -/
def ofScheme (X : Scheme.{u}) [IsNoetherian X] : NoetherianFormalScheme.{u} where
  toLocallyRingedSpace := X.toLocallyRingedSpace
  isNoetherianFormalScheme := isNoetherianFormalScheme_toLocallyRingedSpace X

/-- The completion of a Noetherian scheme `X` along `Y = X` is isomorphic, as a Noetherian formal
scheme, to `X` (Hartshorne II.9, Example 9.3.3, p. 195), by the canonical morphism. -/
def toNoetherianFormalSchemeBotIso (X : Scheme.{u}) [IsNoetherian X] :
    (⊥ : QuasicoherentIdealSubsheaf X).toNoetherianFormalScheme ≅ ofScheme X where
  hom := (QuasicoherentIdealSubsheaf.formalCompletionBotIso X).hom
  inv := (QuasicoherentIdealSubsheaf.formalCompletionBotIso X).inv
  hom_inv_id := (QuasicoherentIdealSubsheaf.formalCompletionBotIso X).hom_inv_id
  inv_hom_id := (QuasicoherentIdealSubsheaf.formalCompletionBotIso X).inv_hom_id

/-- **Noetherian schemes as Noetherian formal schemes** (Hartshorne II.9, Example 9.3.3, p. 195):
the functor from the category of Noetherian schemes to the category of Noetherian formal schemes,
sending a scheme to its underlying locally ringed space and a morphism of schemes to the
underlying morphism of locally ringed spaces. -/
@[simps]
def fromNoetherianScheme :
    ObjectProperty.FullSubcategory (fun X : Scheme.{u} => IsNoetherian X) ⥤
      NoetherianFormalScheme.{u} where
  obj X := haveI := X.property; ofScheme X.obj
  map f := Scheme.forgetToLocallyRingedSpace.map f.hom
  map_id X := Scheme.forgetToLocallyRingedSpace.map_id X.obj
  map_comp f g := Scheme.forgetToLocallyRingedSpace.map_comp f.hom g.hom

/-- **Noetherian schemes embed into Noetherian formal schemes** (Hartshorne II.9, Example 9.3.3,
p. 195): the functor `fromNoetherianScheme` is fully faithful, since schemes form a full
subcategory of locally ringed spaces. -/
def fullyFaithfulFromNoetherianScheme : fromNoetherianScheme.{u}.FullyFaithful :=
  Functor.FullyFaithful.ofCompFaithful (G := forgetToLocallyRingedSpace) (by
    exact (ObjectProperty.fullyFaithfulι _).comp Scheme.fullyFaithfulForgetToLocallyRingedSpace)

instance : fromNoetherianScheme.{u}.Full :=
  fullyFaithfulFromNoetherianScheme.full

instance : fromNoetherianScheme.{u}.Faithful :=
  fullyFaithfulFromNoetherianScheme.faithful

end NoetherianFormalScheme

end Hartshorne

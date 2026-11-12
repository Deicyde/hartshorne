/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.CoherentFormalModuleChart

/-!
# Affine thickenings of an affine Noetherian formal scheme

For an affine Noetherian formal scheme `X ≅ Spf_I(A)`, the inverse image `J` of the ideal
`ker (𝒪_{Spf_I(A)} ⟶ 𝒪_{Spec (A ⧸ I)})` is an ideal of definition of `X`, and every thickening
`(X, 𝒪_X / J ^ (n + 1))` is an affine scheme, isomorphic to `Spec (A ⧸ I ^ (n + 1))`
(Hartshorne II.9, Proposition 9.4(a), transported along the isomorphism).

Transport along an isomorphism `e : A ≅ B` of locally ringed spaces (`IdealSubsheaf` namespace):

* `Hartshorne.IdealSubsheaf.comapQuotientIso`: `𝒪_A / e⁻¹ K ≅ e⁻¹_* (𝒪_B / K)`, as sheaves of
  rings on `A`; `IdealSubsheaf.comapQuotientSheafedSpaceIso`: hence the ringed spaces
  `(B, 𝒪_B / K)` and `(A, 𝒪_A / e⁻¹ K)` are isomorphic.
* `Hartshorne.IsIdealOfDefinition.comap_of_iso`: the inverse image of an ideal of definition along
  an isomorphism of Noetherian formal schemes is an ideal of definition;
  `IsIdealOfDefinition.quotientSchemeIsoOfComap`: the two schemes of the ideals are isomorphic.

Thickenings of a completion (`QuasicoherentIdealSubsheaf` namespace):

* `Hartshorne.QuasicoherentIdealSubsheaf.isAffine_quotientScheme_pow`: if the infinitesimal
  neighbourhood `Y_(n+1)` of a closed subscheme of a Noetherian scheme `Y` is affine, so is the
  scheme `(Ŷ, 𝒪_{Ŷ} / J ^ (n + 1))` of the completion, `J = ker (𝒪_{Ŷ} ⟶ 𝒪_{Y_1})`.

* `Hartshorne.exists_isIdealOfDefinition_forall_isAffine`: an affine Noetherian formal scheme has an
  ideal of definition all of whose thickenings are affine schemes.
-/

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry Topology

namespace Hartshorne

universe u

namespace IdealSubsheaf

section Kernel

variable {T : TopCat.{u}} {R : TopCat.Sheaf CommRingCat.{u} T} (J : IdealSubsheaf R)

/-! The following private lemmas are copied from `Hartshorne.Scheme.PowersOfIdealOfDefinition`,
where they are private. -/

private lemma quotientπ_app_apply' (U : Opens T) (s : R.presheaf.obj (op U)) :
    J.quotientπ.hom.app (op U) s = (toSheafify (Opens.grothendieckTopology T)
        (idealQuotientPresheaf R J.ideal J.ideal_le_comap)).app (op U)
        (Ideal.Quotient.mk (J.ideal U) s) := by
  have h : J.quotientπ.hom = J.quotientPresheafπ ≫ toSheafify (Opens.grothendieckTopology T)
      (idealQuotientPresheaf R J.ideal J.ideal_le_comap) := by
    rw [toSheafify_naturality]
    rfl
  rw [h]
  rfl

/-- The kernel of `R(U) → (R / J)(U)` is `J(U)`. -/
private lemma quotientπ_app_eq_zero_iff' (U : Opens T) (s : R.presheaf.obj (op U)) :
    J.quotientπ.hom.app (op U) s = 0 ↔ s ∈ J.ideal U := by
  constructor
  · intro hs
    rw [quotientπ_app_apply'] at hs
    have hmem := Presheaf.equalizerSieve_mem (Opens.grothendieckTopology T)
      (toSheafify (Opens.grothendieckTopology T)
        (idealQuotientPresheaf R J.ideal J.ideal_le_comap)) (X := op U)
        (Ideal.Quotient.mk (J.ideal U) s) 0 (hs.trans (map_zero _).symm)
    refine J.mem_ideal_of_locally s fun x hx => ?_
    obtain ⟨V, f, hf, hxV⟩ := hmem x hx
    refine ⟨V, leOfHom f, hxV, ?_⟩
    have hf' : (idealQuotientPresheaf R J.ideal J.ideal_le_comap).map f.op
        (Ideal.Quotient.mk (J.ideal U) s) =
        (idealQuotientPresheaf R J.ideal J.ideal_le_comap).map f.op 0 := hf
    rw [map_zero] at hf'
    exact Ideal.Quotient.eq_zero_iff_mem.mp hf'
  · intro hs
    rw [quotientπ_app_apply', Ideal.Quotient.eq_zero_iff_mem.mpr hs]
    exact map_zero _

end Kernel

variable {A B : LocallyRingedSpace.{u}} (e : A ≅ B) (K : IdealSubsheaf B.sheaf)

/-- The map `𝒪_A ⟶ e⁻¹_* 𝒪_B ⟶ e⁻¹_* (𝒪_B / K)` for an isomorphism `e : A ≅ B` of locally ringed
spaces. -/
def comapQuotientHom :
    A.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} e.inv.base).obj K.quotient where
  hom := e.inv.c ≫ (TopCat.Presheaf.pushforward CommRingCat.{u} e.inv.base).map K.quotientπ.hom

lemma comapQuotientHom_app (V : Opens A) (s : A.presheaf.obj (op V)) :
    (comapQuotientHom e K).hom.app (op V) s =
      K.quotientπ.hom.app (op ((Opens.map e.inv.base).obj V)) (e.inv.c.app (op V) s) :=
  rfl

/-- `𝒪_A ⟶ e⁻¹_* (𝒪_B / K)` is locally surjective. -/
lemma isLocallySurjective_comapQuotientHom :
    TopCat.Presheaf.IsLocallySurjective (comapQuotientHom e K).hom := by
  refine (TopCat.Presheaf.isLocallySurjective_iff _).mpr fun V t x hx => ?_
  have hy : e.hom.base x ∈ (Opens.map e.inv.base).obj V := by
    change e.inv.base (e.hom.base x) ∈ V
    rwa [LocallyRingedSpace.iso_hom_base_inv_base_apply]
  obtain ⟨W', hW'V, ⟨s, hs⟩, hyW'⟩ := (TopCat.Presheaf.isLocallySurjective_iff _).mp
    K.isLocallySurjective_quotientπ _ t _ hy
  let W : Opens A := (Opens.map e.hom.base).obj W' ⊓ V
  have hle : (Opens.map e.inv.base).obj W ≤ W' := by
    intro z hz
    have : e.hom.base (e.inv.base z) ∈ W' := hz.1
    rwa [LocallyRingedSpace.iso_inv_base_hom_base_apply] at this
  obtain ⟨r, hr⟩ := surjective_inv_c_app e W (B.presheaf.map (homOfLE hle).op s)
  refine ⟨W, inf_le_right, ⟨r, ?_⟩, ⟨hyW', hx⟩⟩
  rw [comapQuotientHom_app, hr]
  have h1 := NatTrans.naturality_apply K.quotientπ.hom (homOfLE hle).op s
  refine h1.trans ?_
  change K.quotient.presheaf.map (homOfLE hle).op (K.quotientπ.hom.app (op W') s) = _
  rw [hs]
  exact (K.quotient.presheaf.map_comp_apply _ _ t).symm

/-- **Transport of a quotient along an isomorphism.** For an isomorphism `e : A ≅ B` of locally
ringed spaces and an ideal subsheaf `K` of `𝒪_B`, `𝒪_A / e⁻¹ K ≅ e⁻¹_* (𝒪_B / K)`. -/
def comapQuotientIso :
    (comap e.inv K).quotient ≅
      (TopCat.Sheaf.pushforward CommRingCat.{u} e.inv.base).obj K.quotient :=
  idealQuotientSheafIso _ (comapQuotientHom e K)
    (fun V => by
      ext s
      rw [RingHom.mem_ker]
      exact (quotientπ_app_eq_zero_iff' K _ _).symm)
    (isLocallySurjective_comapQuotientHom e K)

/-- For an isomorphism `e : A ≅ B` of locally ringed spaces, the ringed spaces `(B, 𝒪_B / K)` and
`(A, 𝒪_A / e⁻¹ K)` are isomorphic. -/
def comapQuotientSheafedSpaceIso :
    K.quotientSheafedSpace ≅ (comap e.inv K).quotientSheafedSpace :=
  InducedCategory.isoMk (PresheafedSpace.isoOfComponents
    ((LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forget _).mapIso e.symm)
    ((sheafToPresheaf _ _).mapIso (comapQuotientIso e K).symm))

end IdealSubsheaf

namespace IsIdealOfDefinition

open IdealSubsheaf

variable {X Y : NoetherianFormalScheme.{u}} (e : X.toLocallyRingedSpace ≅ Y.toLocallyRingedSpace)
  {K : IdealSubsheaf Y.toLocallyRingedSpace.sheaf}

/-- **Ideals of definition transport along isomorphisms.** The inverse image of an ideal of
definition along an isomorphism of Noetherian formal schemes is an ideal of definition. -/
theorem comap_of_iso (hK : IsIdealOfDefinition Y K) :
    IsIdealOfDefinition X (comap e.inv K) where
  support_eq_univ := sheafSupport_quotientAb_of_le_vanishingIdealSubsheaf
    (comap_le_vanishingIdealSubsheaf e.inv
      (fun x => ⟨e.hom.base x, LocallyRingedSpace.iso_hom_base_inv_base_apply e x⟩)
      hK.le_vanishingIdealSubsheaf)
  isNoetherianScheme := ⟨hK.noetherianScheme, inferInstance,
    ⟨hK.noetherianSchemeIso ≪≫ comapQuotientSheafedSpaceIso e K⟩⟩

/-- For an ideal of definition `J` of `X` equal to the inverse image of an ideal of definition `K`
of `Y` along an isomorphism `X ≅ Y`, the schemes `(X, 𝒪_X / J)` and `(Y, 𝒪_Y / K)` are
isomorphic. -/
def quotientSchemeIsoOfComap {J : IdealSubsheaf X.toLocallyRingedSpace.sheaf}
    (hJ : IsIdealOfDefinition X J) (hK : IsIdealOfDefinition Y K) (hJK : J = comap e.inv K) :
    hJ.quotientScheme ≅ hK.quotientScheme :=
  Scheme.fullyFaithfulForgetToLocallyRingedSpace.preimageIso
    (LocallyRingedSpace.isoOfSheafedSpaceIso
      (eqToIso (congrArg IdealSubsheaf.quotientSheafedSpace hJK) ≪≫
        (comapQuotientSheafedSpaceIso e K).symm))

/-- Affineness of the scheme of an ideal of definition transports along the isomorphism. -/
theorem isAffine_quotientScheme_of_comap {J : IdealSubsheaf X.toLocallyRingedSpace.sheaf}
    (hJ : IsIdealOfDefinition X J) (hK : IsIdealOfDefinition Y K) (hJK : J = comap e.inv K)
    [IsAffine hK.quotientScheme] : IsAffine hJ.quotientScheme :=
  IsAffine.of_isIso (quotientSchemeIsoOfComap e hJ hK hJK).hom

end IsIdealOfDefinition

/-- The restriction of a scheme `X` along an open embedding `U ⟶ X`, as a ringed space, is
`(U, G)` for any sheaf of rings `G` on `U` isomorphic to the restricted structure sheaf. (Stated
for an arbitrary scheme so that the identification of the underlying spaces is checked once.) -/
private def restrictSheafedSpaceIso (X : Scheme.{u}) {U : TopCat.{u}} {f : U ⟶ TopCat.of X}
    (h : IsOpenEmbedding f) (G : TopCat.Sheaf CommRingCat.{u} U)
    (α : h.functor.op ⋙ X.presheaf ≅ G.presheaf) :
    (X.restrict h).toSheafedSpace ≅
      { carrier := U, presheaf := G.presheaf, IsSheaf := G.property } :=
  InducedCategory.isoMk (PresheafedSpace.isoOfComponents (Iso.refl _) α)

namespace QuasicoherentIdealSubsheaf

variable {Y : Scheme.{u}} (I : QuasicoherentIdealSubsheaf Y)

/-- The scheme `Y_(n+1)` restricted along the homeomorphism `Y_1 ⟶ Y_(n+1)`: a scheme with
underlying space `|Y_1|` and structure sheaf `𝒪_{Y_(n+1)}` read on `|Y_1|`. -/
abbrev infinitesimalNeighborhoodRestrict (n : ℕ) : Scheme.{u} :=
  (I.infinitesimalNeighborhood (n + 1)).restrict
    (I.isOpenEmbedding_infinitesimalNeighborhoodFromOne n)

/-- The restriction of `Y_(n+1)` along the homeomorphism `Y_1 ⟶ Y_(n+1)` is isomorphic to
`Y_(n+1)`. -/
instance isIso_ofRestrict_infinitesimalNeighborhoodRestrict (n : ℕ) :
    IsIso (Scheme.ofRestrict _ _ :
      I.infinitesimalNeighborhoodRestrict n ⟶ I.infinitesimalNeighborhood (n + 1)) := by
  refine (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, ⟨?_⟩⟩
  change Function.Surjective (Scheme.ofRestrict _ _ :
    I.infinitesimalNeighborhoodRestrict n ⟶ I.infinitesimalNeighborhood (n + 1)).toLRSHom.base
  rw [Scheme.ofRestrict_toLRSHom_base]
  exact I.infinitesimalNeighborhoodFromOne_surjective n

/-- `(Ŷ, 𝒪_{Ŷ} / J ^ (n + 1))` is the scheme `Y_(n+1)`, as a ringed space. -/
def infinitesimalNeighborhoodRestrictIso [IsLocallyNoetherian Y] (n : ℕ) :
    (I.infinitesimalNeighborhoodRestrict n).toSheafedSpace ≅
      (I.formalCompletionIdealSubsheaf ^ (n + 1)).quotientSheafedSpace :=
  restrictSheafedSpaceIso _ _ (I.formalCompletionIdealSubsheaf ^ (n + 1)).quotient
    ((sheafToPresheaf _ _).mapIso (I.formalCompletionQuotientIso n).symm)

/-- `Y_(n+1)`, restricted to `|Y_1|`, is isomorphic to the scheme `(Ŷ, 𝒪_{Ŷ} / J ^ (n + 1))`. -/
def infinitesimalNeighborhoodRestrictSchemeIso [IsNoetherian Y] (n : ℕ) :
    I.infinitesimalNeighborhoodRestrict n ≅
      (I.isIdealOfDefinition_formalCompletionIdealSubsheaf.pow_succ n).quotientScheme :=
  Scheme.fullyFaithfulForgetToLocallyRingedSpace.preimageIso
    (LocallyRingedSpace.isoOfSheafedSpaceIso (I.infinitesimalNeighborhoodRestrictIso n))

/-- **The thickenings of a completion are affine when the infinitesimal neighbourhoods are.** For
a closed subscheme of a Noetherian scheme `Y` with `Y_(n+1)` affine, the scheme
`(Ŷ, 𝒪_{Ŷ} / J ^ (n + 1))`, `J = ker (𝒪_{Ŷ} ⟶ 𝒪_{Y_1})`, is affine: it is isomorphic to
`Y_(n+1)` (Hartshorne II.9, Proposition 9.4(a), there for `Y` affine). -/
theorem isAffine_quotientScheme_pow [IsNoetherian Y] (n : ℕ)
    [IsAffine (I.infinitesimalNeighborhood (n + 1))] :
    IsAffine (I.isIdealOfDefinition_formalCompletionIdealSubsheaf.pow_succ n).quotientScheme := by
  have : IsAffine (I.infinitesimalNeighborhoodRestrict n) :=
    IsAffine.of_isIso (Scheme.ofRestrict _ _ :
      I.infinitesimalNeighborhoodRestrict n ⟶ I.infinitesimalNeighborhood (n + 1))
  exact IsAffine.of_isIso (I.infinitesimalNeighborhoodRestrictSchemeIso n).inv

end QuasicoherentIdealSubsheaf

/-- **Affine formal schemes have affine thickenings.** An affine Noetherian formal scheme
`X ≅ Spf_I(A)` has an ideal of definition `J` such that every scheme `(X, 𝒪_X / J ^ (n + 1))` is
affine: the inverse image of `ker (𝒪_{Spf_I(A)} ⟶ 𝒪_{Spec (A ⧸ I)})`, whose thickenings are
isomorphic to `Spec (A ⧸ I ^ (n + 1))` (Hartshorne II.9, Proposition 9.4(a)). -/
theorem exists_isIdealOfDefinition_forall_isAffine {X : NoetherianFormalScheme.{u}}
    (hX : IsAffineNoetherianFormalScheme X.toLocallyRingedSpace) :
    ∃ (J : IdealSubsheaf X.toLocallyRingedSpace.sheaf) (h : IsIdealOfDefinition X J),
      ∀ n, IsAffine (h.pow_succ n).quotientScheme := by
  obtain ⟨A, _, _, I, ⟨e⟩⟩ := hX
  let I' := specIdealSubsheaf A I
  let e' : X.toLocallyRingedSpace ≅ I'.toNoetherianFormalScheme.toLocallyRingedSpace := e
  have hK := I'.isIdealOfDefinition_formalCompletionIdealSubsheaf
  refine ⟨IdealSubsheaf.comap e'.inv I'.formalCompletionIdealSubsheaf,
    IsIdealOfDefinition.comap_of_iso e' hK, fun n => ?_⟩
  have : IsAffine (I'.infinitesimalNeighborhood (n + 1)) :=
    IsAffine.of_isIso (specIdealSubsheafNeighborhoodIso A I (n + 1)).hom
  have := I'.isAffine_quotientScheme_pow n
  exact IsIdealOfDefinition.isAffine_quotientScheme_of_comap e' _ (hK.pow_succ n)
    (IdealSubsheaf.comap_pow_of_iso e' _ (n + 1)).symm

end Hartshorne

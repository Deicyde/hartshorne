/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.FormalCompletionAffineSections
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.Topology.Sheaves.Skyscraper

/-!
# The completion of a scheme at a closed point

Hartshorne, *Algebraic Geometry*, II.9, Example 9.3.4 (p. 195).

Let `P` be a closed point of a Noetherian scheme `X`. The completion of `X` along `P` (along the
reduced closed subscheme `{P}`) is the one-point locally ringed space whose ring is the completion
`Ô_P` of the local ring `𝒪_{X,P}` at its maximal ideal.

* `Hartshorne.closedPointIdealSubsheaf P hP`: the ideal sheaf of the reduced closed subscheme
  `{P}`, the vanishing ideal sheaf of the closed set `{P}`.
* `Hartshorne.onePointLocallyRingedSpace R`: for a local ring `R`, the one-point locally ringed
  space with ring `R` (the skyscraper sheaf with value `R` on the one-point space).
* `Hartshorne.isoSkyscraperPresheafPUnit`: a sheaf of rings on the one-point space is the
  skyscraper sheaf of its global sections.
* `Hartshorne.adicCompletionMap_bijective`: a ring map inducing isomorphisms
  `A ⧸ 𝔞 ^ n ≃ B ⧸ 𝔟 ^ n` for all `n` induces an isomorphism of adic completions.
* `Hartshorne.adicCompletionLocalizationEquiv`: for a maximal ideal `𝔪 ⊆ A`, completion is
  unchanged by localizing at `𝔪`: `Â ≃ (A_𝔪)^`.
* `Hartshorne.formalCompletionClosedPointSectionsEquiv`: the ring of global sections of the
  completion along `P` is `Ô_P`.
* `Hartshorne.formalCompletionClosedPointIso P hP U hPU`: the isomorphism of locally ringed
  spaces from the completion of `X` along `P` to the one-point locally ringed space with ring
  `Ô_P`, built from an affine open `U ∋ P`.
* `Hartshorne.formalCompletion_closedPoint_iso`: the statement of the example.

For an affine open `U = Spec A` containing `P`, with `𝔪 ⊆ A` the maximal ideal of `P`, the
sections of the completion over its whole (one-point) space are `lim_n A ⧸ 𝔪 ^ (n + 1)`
(`QuasicoherentIdealSubsheaf.formalCompletionAffineSectionsIso`); since `𝔪` is maximal,
`A ⧸ 𝔪 ^ n ≅ A_𝔪 ⧸ 𝔪 ^ n A_𝔪 = 𝒪_{X,P} ⧸ 𝔪_P ^ n`, so this ring is `Ô_P`.
-/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Topology Opposite TopologicalSpace IsLocalRing

namespace Hartshorne

universe u

/-! ### Adic completions and localization at a maximal ideal -/

section AdicCompletion

variable {A B : Type*} [CommRing A] [CommRing B]

/-- The induced map of adic completions is bijective as soon as all the reductions
`A ⧸ 𝔞 ^ n → B ⧸ 𝔟 ^ n` are. -/
theorem adicCompletionMap_bijective {𝔞 : Ideal A} {𝔟 : Ideal B} {φ : A →+* B}
    (h : 𝔞 ≤ 𝔟.comap φ)
    (hb : ∀ n, Function.Bijective (Ideal.quotientMap (𝔟 ^ n) φ (pow_le_comap_pow h n))) :
    Function.Bijective (adicCompletionMap 𝔞 𝔟 φ h) := by
  let e : ∀ n, A ⧸ 𝔞 ^ n ≃+* B ⧸ 𝔟 ^ n := fun n => RingEquiv.ofBijective _ (hb n)
  have he : ∀ n (a : A ⧸ 𝔞 ^ n),
      e n a = Ideal.quotientMap (𝔟 ^ n) φ (pow_le_comap_pow h n) a := fun _ _ => rfl
  have hfac : ∀ {m n : ℕ} (hle : m ≤ n) (a : A ⧸ 𝔞 ^ n),
      e m (Ideal.Quotient.factorPow 𝔞 hle a) = Ideal.Quotient.factorPow 𝔟 hle (e n a) := by
    intro m n hle a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [he, he, Ideal.Quotient.factor_mk, Ideal.quotientMap_mk, Ideal.quotientMap_mk,
      Ideal.Quotient.factor_mk]
  refine ⟨fun x y hxy => AdicCompletion.ext_evalₐ fun n => (hb n).1 ?_, fun z => ?_⟩
  · have := congrArg (AdicCompletion.evalₐ 𝔟 n) hxy
    rwa [evalₐ_adicCompletionMap, evalₐ_adicCompletionMap] at this
  · have hcompat : ∀ {m n : ℕ} (hle : m ≤ n),
        (Ideal.Quotient.factorPow 𝔞 hle).comp
            ((e n).symm.toRingHom.comp (AdicCompletion.evalₐ 𝔟 n).toRingHom) =
          (e m).symm.toRingHom.comp (AdicCompletion.evalₐ 𝔟 m).toRingHom := by
      intro m n hle
      ext w
      apply (e m).injective
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.apply_symm_apply]
      rw [hfac, RingEquiv.apply_symm_apply, factorPow_evalₐ]
    refine ⟨AdicCompletion.liftRingHom 𝔞 _ hcompat z, AdicCompletion.ext_evalₐ fun n => ?_⟩
    rw [evalₐ_adicCompletionMap, AdicCompletion.evalₐ_liftRingHom, ← he]
    exact (e n).apply_symm_apply _

variable (p : Ideal A) [p.IsMaximal] (Aₚ : Type*) [CommRing Aₚ] [Algebra A Aₚ]
  [IsLocalization.AtPrime Aₚ p] [IsLocalRing Aₚ]

/-- An ideal equal to the maximal ideal `p` maps into the maximal ideal of `A_p`. -/
lemma le_comap_maximalIdeal_of_eq {𝔞 : Ideal A} (h𝔞 : 𝔞 = p) :
    𝔞 ≤ (maximalIdeal Aₚ).comap (algebraMap A Aₚ) := by
  rw [h𝔞]
  exact (IsLocalization.AtPrime.under_maximalIdeal Aₚ p).ge

/-- For a maximal ideal `p`, the reduction `A ⧸ p ^ n → A_p ⧸ (p A_p) ^ n` of the localization
map is bijective. -/
lemma bijective_quotientMap_algebraMap_pow {𝔞 : Ideal A} (h𝔞 : 𝔞 = p) (n : ℕ) :
    Function.Bijective (Ideal.quotientMap (maximalIdeal Aₚ ^ n) (algebraMap A Aₚ)
      (pow_le_comap_pow (le_comap_maximalIdeal_of_eq p Aₚ h𝔞) n)) := by
  subst h𝔞
  have heq : ⇑(Ideal.quotientMap (maximalIdeal Aₚ ^ n) (algebraMap A Aₚ)
      (pow_le_comap_pow (le_comap_maximalIdeal_of_eq 𝔞 Aₚ rfl) n)) =
        ⇑(IsLocalization.AtPrime.equivQuotMaximalIdealPow 𝔞 Aₚ n) := by
    funext a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.quotientMap_mk, IsLocalization.AtPrime.equivQuotMaximalIdealPow_apply_mk]
  rw [heq]
  exact (IsLocalization.AtPrime.equivQuotMaximalIdealPow 𝔞 Aₚ n).bijective

/-- **Completion is unchanged by localizing at a maximal ideal.** For an ideal `𝔞` equal to a
maximal ideal `p`, the localization map induces `Â_𝔞 ≃ (A_p)^` (completion at the maximal
ideal). -/
def adicCompletionLocalizationEquiv {𝔞 : Ideal A} (h𝔞 : 𝔞 = p) :
    AdicCompletion 𝔞 A ≃+* AdicCompletion (maximalIdeal Aₚ) Aₚ :=
  RingEquiv.ofBijective (adicCompletionMap 𝔞 (maximalIdeal Aₚ) (algebraMap A Aₚ)
      (le_comap_maximalIdeal_of_eq p Aₚ h𝔞))
    (adicCompletionMap_bijective _ (bijective_quotientMap_algebraMap_pow p Aₚ h𝔞))

end AdicCompletion

/-! ### The one-point locally ringed space -/

section OnePoint

open Classical

/-- The one-point topological space. -/
abbrev onePointSpace : TopCat.{u} := TopCat.of PUnit.{u + 1}

/-- The point of the one-point space. -/
abbrev onePointSpace.pt : onePointSpace.{u} := PUnit.unit

/-- The point of the one-point space. -/
local notation "⋆" => onePointSpace.pt

/-- Every open of the one-point space containing its point is the whole space. -/
private lemma eq_top_of_mem_punit {U : Opens onePointSpace.{u}}
    (h : ⋆ ∈ U) : U = ⊤ := by
  ext x
  cases x
  simpa using h

/-- On the one-point space, every germ map is bijective. -/
private lemma bijective_germ_punit (G : TopCat.Presheaf CommRingCat.{u} (onePointSpace.{u}))
    (U : Opens (onePointSpace.{u})) (h : ⋆ ∈ U) :
    Function.Bijective (G.germ U ⋆ h) := by
  obtain rfl := eq_top_of_mem_punit h
  refine ⟨fun s t hst => ?_, fun t => ?_⟩
  · obtain ⟨W, hW, iU, iV, e⟩ := G.germ_eq ⋆ h h s t hst
    obtain rfl := eq_top_of_mem_punit hW
    rwa [Subsingleton.elim iU (𝟙 _), Subsingleton.elim iV (𝟙 _), op_id, G.map_id,
      CommRingCat.id_apply, CommRingCat.id_apply] at e
  · obtain ⟨V, hV, s, rfl⟩ := G.exists_germ_eq t
    obtain rfl := eq_top_of_mem_punit hV
    exact ⟨s, rfl⟩

private lemma isIso_germ_punit
    (G : TopCat.Presheaf CommRingCat.{u} (onePointSpace.{u}))
    (U : Opens (onePointSpace.{u})) (h : ⋆ ∈ U) :
    IsIso (G.germ U ⋆ h) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (bijective_germ_punit G U h)

/-- A morphism defined by cases is an isomorphism when both cases are. -/
private lemma isIso_dite {C : Type*} [Category C] {X Y : C} {c : Prop} [Decidable c]
    (f : c → (X ⟶ Y)) (g : ¬c → (X ⟶ Y)) (hf : ∀ h, IsIso (f h)) (hg : ∀ h, IsIso (g h)) :
    IsIso (dite c f g) := by
  by_cases h : c
  · rw [dif_pos h]
    exact hf h
  · rw [dif_neg h]
    exact hg h

/-- A sheaf of rings on the one-point space is the skyscraper sheaf of its global sections. -/
def isoSkyscraperPresheafPUnit (G : TopCat.Presheaf CommRingCat.{u} (onePointSpace.{u}))
    (hG : G.IsSheaf) {R : CommRingCat.{u}} (e : G.obj (op ⊤) ≅ R) :
    G ≅ skyscraperPresheaf ⋆ R :=
  haveI := isIso_germ_punit G ⊤ trivial
  haveI : ∀ U, IsIso ((StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf ⋆
      (inv (G.germ ⊤ ⋆ (Opens.mem_top _)) ≫ e.hom)).app U) := fun U => by
    rw [StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf_app]
    refine isIso_dite _ _ (fun h => ?_) (fun h => ?_)
    · have h1 := isIso_germ_punit G _ h
      have h2 := isIso_germ_punit G ⊤ (Opens.mem_top _)
      have h3 : IsIso (inv (G.germ ⊤ ⋆ (Opens.mem_top _)) ≫ e.hom) := inferInstance
      exact IsIso.comp_isIso' h1 (IsIso.comp_isIso' h3 (Iso.isIso_hom (eqToIso (by simp [h]))))
    · have hU : U.unop = ⊥ := by
        ext x
        cases x
        simpa using h
      exact isIso_of_isTerminal (TopCat.Sheaf.isTerminalOfEqEmpty ⟨G, hG⟩ hU)
        (isTerminalSkyscraperSheafObjObjOfNotMem (p₀ := ⋆) (A := R) h) _
  haveI := NatIso.isIso_of_isIso_app (StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf ⋆
      (inv (G.germ ⊤ ⋆ (Opens.mem_top _)) ≫ e.hom))
  asIso (StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf ⋆
    (inv (G.germ ⊤ ⋆ (Opens.mem_top _)) ≫ e.hom))

/-- **The one-point locally ringed space** with ring `R`: the one-point space with the skyscraper
sheaf of value `R`, whose only stalk is `R`. -/
def onePointLocallyRingedSpace (R : CommRingCat.{u}) [IsLocalRing R] : LocallyRingedSpace.{u} where
  carrier := onePointSpace.{u}
  presheaf := skyscraperPresheaf ⋆ R
  IsSheaf := skyscraperPresheaf_isSheaf _ _
  isLocalRing x :=
    (skyscraperPresheafStalkOfSpecializes ⋆ R
      (specializes_of_eq (Subsingleton.elim ⋆ x))).hom.hom.domain_isLocalRing

end OnePoint

/-! ### The completion along a closed point -/

section ClosedPoint

variable {X : Scheme.{u}} (P : X) (hP : IsClosed ({P} : Set X))

/-- **The ideal sheaf of a closed point** `P`: the ideal sheaf of the reduced closed subscheme
`{P}`, that is the vanishing ideal sheaf of the closed set `{P}`. -/
def closedPointIdealSubsheaf : QuasicoherentIdealSubsheaf X :=
  quasicoherentIdealSubsheafEquiv.symm (Scheme.IdealSheafData.vanishingIdeal ⟨{P}, hP⟩)

/-- The closed subscheme cut out by the ideal sheaf of `P` has support `{P}`. -/
theorem range_closedPointIdealSubsheaf_infinitesimalNeighborhoodι :
    Set.range ((closedPointIdealSubsheaf P hP).infinitesimalNeighborhoodι 1) = {P} := by
  change Set.range (quasicoherentIdealSubsheafEquiv
    (closedPointIdealSubsheaf P hP ^ 1)).subschemeι = _
  rw [Scheme.IdealSheafData.range_subschemeι, QuasicoherentIdealSubsheaf.pow_one,
    closedPointIdealSubsheaf, Equiv.apply_symm_apply]
  simp

/-- Every point of the closed subscheme `{P}` lies over `P`. -/
lemma infinitesimalNeighborhoodι_closedPointIdealSubsheaf_apply
    (y : (closedPointIdealSubsheaf P hP).infinitesimalNeighborhood 1) :
    (closedPointIdealSubsheaf P hP).infinitesimalNeighborhoodι 1 y = P := by
  have := range_closedPointIdealSubsheaf_infinitesimalNeighborhoodι P hP ▸ Set.mem_range_self y
  simpa using this

/-- The underlying space of the completion along `P` has at most one point. -/
instance subsingleton_formalCompletion_closedPointIdealSubsheaf :
    Subsingleton (closedPointIdealSubsheaf P hP).formalCompletion.carrier :=
  ⟨fun y z =>
    ((closedPointIdealSubsheaf P hP).infinitesimalNeighborhoodι 1).isClosedEmbedding.injective
      ((infinitesimalNeighborhoodι_closedPointIdealSubsheaf_apply P hP y).trans
        (infinitesimalNeighborhoodι_closedPointIdealSubsheaf_apply P hP z).symm)⟩

/-- The point of the completion along `P`, lying over `P`. -/
def formalCompletionClosedPointPt : (closedPointIdealSubsheaf P hP).formalCompletion.carrier :=
  ((range_closedPointIdealSubsheaf_infinitesimalNeighborhoodι P hP).symm ▸
    Set.mem_singleton P : P ∈ Set.range _).choose

/-- The underlying space of the completion along `P` is the one-point space. -/
def formalCompletionClosedPointCarrierIso :
    (closedPointIdealSubsheaf P hP).formalCompletion.carrier ≅ onePointSpace.{u} where
  hom := TopCat.ofHom ⟨fun _ => PUnit.unit, continuous_const⟩
  inv := TopCat.ofHom ⟨fun _ => formalCompletionClosedPointPt P hP, continuous_const⟩
  hom_inv_id := by
    ext y
    exact Subsingleton.elim _ _
  inv_hom_id := by
    ext

/-- On an affine open `U = Spec A` containing `P`, the ideal of `P` is the maximal ideal of `A`
corresponding to `P`. -/
theorem ideal_closedPointIdealSubsheaf (U : X.affineOpens) (hPU : P ∈ (U : X.Opens)) :
    (closedPointIdealSubsheaf P hP).ideal U = (U.2.primeIdealOf ⟨P, hPU⟩).asIdeal := by
  rw [closedPointIdealSubsheaf, quasicoherentIdealSubsheafEquiv_symm_ideal,
    Scheme.IdealSheafData.vanishingIdeal_ideal, ← PrimeSpectrum.vanishingIdeal_singleton]
  congr 1
  ext y
  simp only [Set.mem_singleton_iff]
  constructor
  · intro hy
    have := IsAffineOpen.isOpenImmersion_fromSpec U.2
    exact (IsAffineOpen.fromSpec U.2).isOpenEmbedding.injective
      (hy.trans (U.2.fromSpec_primeIdealOf ⟨P, hPU⟩).symm)
  · rintro rfl
    exact U.2.fromSpec_primeIdealOf _

/-- The open `U ∩ |Y|` is the whole underlying space of the completion along `P`. -/
lemma preimage_closedPointIdealSubsheaf_eq_top (U : X.Opens) (hPU : P ∈ U) :
    (closedPointIdealSubsheaf P hP).infinitesimalNeighborhoodι 1 ⁻¹ᵁ U = ⊤ := by
  refine eq_top_iff.mpr fun y _ => ?_
  change (closedPointIdealSubsheaf P hP).infinitesimalNeighborhoodι 1 y ∈ U
  rw [infinitesimalNeighborhoodι_closedPointIdealSubsheaf_apply]
  exact hPU

/-- **Global sections of the completion along a closed point.** For an affine open
`U = Spec A ∋ P`, the ring of sections of the completion along `P` over its whole space is
`lim_n A ⧸ 𝔪 ^ (n + 1) ≅ Ô_P`, the completion of `𝒪_{X,P}` at its maximal ideal. -/
def formalCompletionClosedPointSectionsEquiv (U : X.affineOpens) (hPU : P ∈ (U : X.Opens)) :
    (closedPointIdealSubsheaf P hP).formalCompletionSheaf.presheaf.obj (op ⊤) ≃+*
      AdicCompletion (maximalIdeal (X.presheaf.stalk P)) (X.presheaf.stalk P) :=
  haveI := U.2.primeIdealOf_isMaximal_of_isClosed ⟨P, hPU⟩ hP
  letI : Algebra Γ(X, U) (X.presheaf.stalk P) :=
    X.presheaf.algebra_section_stalk (U := (U : X.Opens)) ⟨P, hPU⟩
  haveI : IsLocalization.AtPrime (X.presheaf.stalk P) (U.2.primeIdealOf ⟨P, hPU⟩).asIdeal :=
    U.2.isLocalization_stalk ⟨P, hPU⟩
  ((closedPointIdealSubsheaf P hP).formalCompletionSheaf.presheaf.mapIso
      (eqToIso (preimage_closedPointIdealSubsheaf_eq_top P hP U hPU)).op).commRingCatIsoToRingEquiv
    |>.trans ((closedPointIdealSubsheaf P hP).formalCompletionAffineSectionsIso U)
    |>.trans (adicCompletionLocalizationEquiv (U.2.primeIdealOf ⟨P, hPU⟩).asIdeal
      (X.presheaf.stalk P)
      (ideal_closedPointIdealSubsheaf P hP U hPU))

variable [IsNoetherian X]

/-- **The completion of `X` at a closed point `P`** (Hartshorne II.9, Example 9.3.4, p. 195):
the isomorphism of locally ringed spaces from the completion of `X` along the reduced closed
point `P` to the one-point locally ringed space with ring `Ô_P`, the completion of the local
ring `𝒪_{X,P}` at its maximal ideal, built from an affine open `U ∋ P`. -/
def formalCompletionClosedPointIso (U : X.affineOpens) (hPU : P ∈ (U : X.Opens)) :
    (closedPointIdealSubsheaf P hP).formalCompletion ≅
      onePointLocallyRingedSpace (CommRingCat.of
        (AdicCompletion (maximalIdeal (X.presheaf.stalk P)) (X.presheaf.stalk P))) :=
  LocallyRingedSpace.isoOfSheafedSpaceIso (SheafedSpace.isoMk (PresheafedSpace.isoOfComponents
    (formalCompletionClosedPointCarrierIso P hP)
    (isoSkyscraperPresheafPUnit _
      (TopCat.Sheaf.pushforward_sheaf_of_sheaf _
        (closedPointIdealSubsheaf P hP).formalCompletionSheaf.property)
      (formalCompletionClosedPointSectionsEquiv P hP U hPU).toCommRingCatIso)))

/-- **Completion at a closed point** (Hartshorne II.9, Example 9.3.4, p. 195). Let `P` be a
closed point of a Noetherian scheme `X`. The completion of `X` along `P` (with its reduced
structure; by Remark 9.3.1 the completion depends only on the closed set `{P}`) is isomorphic, as
a locally ringed space, to the one-point locally ringed space whose ring is the completion `Ô_P`
of the local ring `𝒪_{X,P}` at its maximal ideal. -/
theorem formalCompletion_closedPoint_iso :
    Nonempty ((closedPointIdealSubsheaf P hP).formalCompletion ≅
      onePointLocallyRingedSpace (CommRingCat.of
        (AdicCompletion (maximalIdeal (X.presheaf.stalk P)) (X.presheaf.stalk P)))) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hPV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ P) isOpen_univ
  exact ⟨formalCompletionClosedPointIso P hP ⟨V, hV⟩ hPV⟩

end ClosedPoint

end Hartshorne

/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.FormalCompletion

/-!
# The project formal spectrum and affine Noetherian formal schemes

Hartshorne, *Algebraic Geometry*, II.9, affine formal schemes (p. 195).

For a Noetherian ring `A` and an ideal `I ⊆ A`, the project writes `Spf_I(A)` for the formal
completion of `Spec A` along the closed subscheme `V(I)`. Hartshorne does not introduce this
notation: it is a representation bridge for his description of affine formal schemes as
completions of affine Noetherian schemes, with no topology on the section rings and no statement
about continuous ring maps.

* `Hartshorne.specIdealSubsheaf A I`: the quasi-coherent ideal subsheaf of `𝒪_{Spec A}` attached
  to `I`, namely the ideal sheaf of the closed subscheme `Spec (A ⧸ I) ⟶ Spec A`.
* `Hartshorne.range_specIdealSubsheaf_infinitesimalNeighborhoodι`: the closed subscheme it cuts
  out has support `V(I)`.
* `Hartshorne.Spf A I`: the formal completion of `Spec A` along `V(I)`, a locally ringed space.
* `Hartshorne.spfHomeomorph A I`: its underlying space is homeomorphic to `Spec (A ⧸ I)`.
* `Hartshorne.IsAffineNoetherianFormalScheme X`: the locally ringed space `X` is isomorphic to
  `Spf_I(A)` for some Noetherian ring `A` and ideal `I`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Topology

namespace Hartshorne

universe u

variable (A : Type u) [CommRing A] (I : Ideal A)

/-- The quotient map `A → A ⧸ I` induces a closed immersion `Spec (A ⧸ I) ⟶ Spec A`. -/
instance isClosedImmersion_spec_map_quotient_mk :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- The quasi-coherent ideal subsheaf of `𝒪_{Spec A}` attached to an ideal `I ⊆ A`: the ideal
sheaf of the closed subscheme `Spec (A ⧸ I) ⟶ Spec A` (the closed subscheme of the affine scheme
`Spec A` given by `I`, Hartshorne II.3). -/
def specIdealSubsheaf : QuasicoherentIdealSubsheaf (Spec (CommRingCat.of A)) :=
  quasicoherentIdealSubsheafEquiv.symm
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker

/-- The closed subscheme cut out by the ideal sheaf attached to `I` is `Spec (A ⧸ I)`, compatibly
with the closed immersions into `Spec A`. -/
def specIdealSubsheafNeighborhoodOneIso :
    (specIdealSubsheaf A I).infinitesimalNeighborhood 1 ≅ Spec (CommRingCat.of (A ⧸ I)) :=
  infinitesimalNeighborhoodOneIso _

@[reassoc (attr := simp)]
lemma specIdealSubsheafNeighborhoodOneIso_hom_comp :
    (specIdealSubsheafNeighborhoodOneIso A I).hom ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) =
      (specIdealSubsheaf A I).infinitesimalNeighborhoodι 1 :=
  infinitesimalNeighborhoodOneIso_hom_comp _

/-- The closed subscheme cut out by the ideal sheaf attached to `I` has support `V(I)`. -/
theorem range_specIdealSubsheaf_infinitesimalNeighborhoodι :
    Set.range ((specIdealSubsheaf A I).infinitesimalNeighborhoodι 1) =
      (PrimeSpectrum.zeroLocus (I : Set A) : Set (PrimeSpectrum A)) := by
  rw [← specIdealSubsheafNeighborhoodOneIso_hom_comp]
  have hsurj : Function.Surjective (specIdealSubsheafNeighborhoodOneIso A I).hom :=
    (Scheme.homeoOfIso (specIdealSubsheafNeighborhoodOneIso A I)).surjective
  have hcomp : ⇑((specIdealSubsheafNeighborhoodOneIso A I).hom ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) =
      ⇑(Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ∘
        ⇑(specIdealSubsheafNeighborhoodOneIso A I).hom := by
    funext x
    exact Scheme.Hom.comp_apply _ _ x
  rw [hcomp, Set.range_comp, hsurj.range_eq, Set.image_univ]
  change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) = _
  rw [_root_.range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
    Ideal.mk_ker]

/-- **The project formal spectrum** `Spf_I(A)` of a Noetherian ring `A` along an ideal `I`: the
formal completion of `Spec A` along the closed subscheme `V(I)` (Hartshorne II.9, p. 195, where
affine formal schemes are such completions; Hartshorne does not use the notation `Spf`). It is the
locally ringed space with underlying space `V(I)` and structure sheaf
`lim_(n ≥ 1) (𝒪_{Spec A} / I ^ n)|_{V(I)}`, with no topology on the section rings. The
construction does not use that `A` is Noetherian; the hypothesis is kept because it is Hartshorne's
setting for formal schemes. -/
def Spf [IsNoetherianRing A] : LocallyRingedSpace.{u} :=
  (specIdealSubsheaf A I).formalCompletion

/-- The underlying space of `Spf_I(A)` is that of the closed subscheme cut out by `I`. -/
lemma Spf_carrier [IsNoetherianRing A] :
    (Spf A I).carrier = ((specIdealSubsheaf A I).infinitesimalNeighborhood 1).toTopCat :=
  rfl

/-- The underlying space of `Spf_I(A)` is homeomorphic to `Spec (A ⧸ I)`, that is to `V(I)`
(`range_specIdealSubsheaf_infinitesimalNeighborhoodι`). -/
def spfHomeomorph [IsNoetherianRing A] :
    (Spf A I).carrier ≃ₜ Spec (CommRingCat.of (A ⧸ I)) :=
  Scheme.homeoOfIso (specIdealSubsheafNeighborhoodOneIso A I)

/-- **Affine Noetherian formal schemes** (Hartshorne II.9, p. 195): a locally ringed space is an
affine Noetherian formal scheme when it is isomorphic, as a locally ringed space, to `Spf_I(A)`
for some Noetherian ring `A` and ideal `I ⊆ A`. -/
def IsAffineNoetherianFormalScheme (X : LocallyRingedSpace.{u}) : Prop :=
  ∃ (A : Type u) (_ : CommRing A) (_ : IsNoetherianRing A) (I : Ideal A), Nonempty (X ≅ Spf A I)

/-- `Spf_I(A)` is an affine Noetherian formal scheme. -/
theorem isAffineNoetherianFormalScheme_Spf [IsNoetherianRing A] :
    IsAffineNoetherianFormalScheme (Spf A I) :=
  ⟨A, inferInstance, inferInstance, I, ⟨Iso.refl _⟩⟩

/-- Being an affine Noetherian formal scheme is invariant under isomorphism. -/
theorem IsAffineNoetherianFormalScheme.of_iso {X Y : LocallyRingedSpace.{u}} (e : X ≅ Y)
    (hY : IsAffineNoetherianFormalScheme Y) : IsAffineNoetherianFormalScheme X := by
  obtain ⟨B, _, _, J, ⟨f⟩⟩ := hY
  exact ⟨B, _, inferInstance, J, ⟨e ≪≫ f⟩⟩

end Hartshorne

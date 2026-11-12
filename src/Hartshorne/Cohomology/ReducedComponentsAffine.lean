/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.SerreAffinenessCriterion
import Hartshorne.Cohomology.ClosedPushforwardCohomology
import Hartshorne.Scheme.ReducedInducedSubscheme
import Hartshorne.Scheme.ReducedInducedSmallest

/-!
# Affineness of reduced irreducible components (partial)

Hartshorne, *Algebraic Geometry*, III, Exercise 3.2 (p. 216): a reduced Noetherian scheme is
affine iff each of its irreducible components, with the reduced induced structure, is affine.

This module contains the pieces proved so far.

* Easy direction: a closed subscheme of an affine scheme is affine
  (`Hartshorne.isAffine_reducedInducedSubscheme_of_isAffine`,
  `Hartshorne.forall_irreducibleComponents_isAffine_of_isAffine`).
* Cohomology of a closed pushforward: for a closed immersion `i : Z ⟶ X` and an `𝒪_Z`-module
  `G`, `H^n(X, i_* G) ≅ H^n(Z, G)` (`ReducedComponentsAffine.pushforwardCohomologyIso`, from
  III, Lemma 2.10); if `Z` is affine Noetherian and `G` quasi-coherent, these vanish for `n > 0`
  (`ReducedComponentsAffine.isZero_H_pushforward`, by III, Theorem 3.5), and `H^1` vanishes on the
  middle term of a short exact sequence whose outer terms are such pushforwards
  (`ReducedComponentsAffine.isZero_H1_of_shortExact_pushforward`).
* Induction on the number of components: the hard direction follows from its two-piece case
  `ReducedComponentsAffine.TwoPieceAffine` (`X = A ∪ B` with `A`, `B` closed and the reduced
  induced subschemes on `A`, `B` affine) by
  `ReducedComponentsAffine.isAffine_of_forall_irreducibleComponents_of_twoPiece`. Inside the
  reduced induced subscheme on `W ⊇ A`, the reduced induced subscheme on `A` is the one taken in
  `X` (`ReducedComponentsAffine.isAffine_reducedInducedSubscheme_preimageCloseds`).

* Serre's criterion (III, Theorem 3.7) reduces the two-piece case to the sheaf-theoretic
  statement `ReducedComponentsAffine.TwoPieceSequences`
  (`ReducedComponentsAffine.twoPieceAffine_of_twoPieceSequences`), and the exercise follows from
  it (`ReducedComponentsAffine.isAffine_iff_of_twoPieceSequences`).

`TwoPieceSequences` is not yet proved: it needs that an `𝒪_Y`-module killed by the ideal of a
closed subscheme `i : Z ⟶ Y` is `i_*` of a quasi-coherent `𝒪_Z`-module.
-/

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry

namespace Hartshorne

namespace ReducedComponentsAffine

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The underlying space of the source of a closed immersion is homeomorphic to its image. -/
def rangeIso : Z.toTopCat ≅ TopCat.of (Set.range i.base) :=
  TopCat.isoOfHomeo i.isClosedEmbedding.isEmbedding.toHomeomorph

/-- The underlying map of a closed immersion is the homeomorphism onto its image followed by the
inclusion of the image. -/
theorem base_eq :
    i.base = (rangeIso i).hom ≫ closedSubspaceInclusion X.toTopCat (Set.range i.base) :=
  rfl

/-- `H^n(X, i_* G) ≅ H^n(Z, G)` (Hartshorne III, Lemma 2.10, transported along the homeomorphism
of `Z` onto its image) for a closed immersion `i : Z ⟶ X` and an `𝒪_Z`-module `G`. -/
def pushforwardCohomologyIso (G : Z.Modules) (n : ℕ) :
    SerreAffineness.H n ((Scheme.Modules.pushforward i).obj G) ≅ SerreAffineness.H n G := by
  let F := (SheafOfModules.toSheaf Z.ringCatSheaf).obj G
  let S := Set.range i.base
  have e₁ : SerreAffineness.H n ((Scheme.Modules.pushforward i).obj G) =
      (sheafCohomology X.toTopCat n).obj
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (closedSubspaceInclusion X.toTopCat S)).obj
          ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (rangeIso i).hom).obj F)) := by
    change _ = (sheafCohomology X.toTopCat n).obj
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
        ((rangeIso i).hom ≫ closedSubspaceInclusion X.toTopCat S)).obj F)
    rw [← base_eq]
    rfl
  exact eqToIso e₁ ≪≫ (closedPushforwardCohomologyIso S i.isClosedEmbedding.isClosed_range _ n).symm ≪≫
    sheafCohomologyPushforwardIsoOfIso (rangeIso i) F n

/-- For a closed immersion `i : Z ⟶ X` with `Z` affine and Noetherian and a quasi-coherent
`𝒪_Z`-module `G`, `H^n(X, i_* G) = 0` for `n > 0`. -/
theorem isZero_H_pushforward [IsAffine Z] [IsLocallyNoetherian Z] (G : Z.Modules)
    [G.IsQuasicoherent] (n : ℕ) (hn : 0 < n) :
    IsZero (SerreAffineness.H n ((Scheme.Modules.pushforward i).obj G)) :=
  (sheafCohomology_isZero_of_isQuasicoherent_of_isAffine G n hn).of_iso
    (pushforwardCohomologyIso i G n)

/-- If `0 ⟶ F' ⟶ F ⟶ F'' ⟶ 0` is a short exact sequence of `𝒪_X`-modules with `F' ≅ i₁_* G₁` and
`F'' ≅ i₂_* G₂` for closed immersions `iₖ : Zₖ ⟶ X` from affine Noetherian schemes and
quasi-coherent `Gₖ`, then `H^1(X, F) = 0`. -/
theorem isZero_H1_of_shortExact_pushforward {Z₁ Z₂ : Scheme.{u}} (i₁ : Z₁ ⟶ X) (i₂ : Z₂ ⟶ X)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsAffine Z₁] [IsAffine Z₂]
    [IsLocallyNoetherian Z₁] [IsLocallyNoetherian Z₂] {S : ShortComplex X.Modules}
    (hS : S.ShortExact) (G₁ : Z₁.Modules) (G₂ : Z₂.Modules) [G₁.IsQuasicoherent]
    [G₂.IsQuasicoherent] (e₁ : S.X₁ ≅ (Scheme.Modules.pushforward i₁).obj G₁)
    (e₃ : S.X₃ ≅ (Scheme.Modules.pushforward i₂).obj G₂) :
    IsZero (SerreAffineness.H 1 S.X₂) :=
  SerreAffineness.isZero_H1_of_shortExact hS
    ((isZero_H_pushforward i₁ G₁ 1 Nat.one_pos).of_iso
      ((sheafCohomology X.toTopCat 1).mapIso ((SheafOfModules.toSheaf X.ringCatSheaf).mapIso e₁)))
    ((isZero_H_pushforward i₂ G₂ 1 Nat.one_pos).of_iso
      ((sheafCohomology X.toTopCat 1).mapIso ((SheafOfModules.toSheaf X.ringCatSheaf).mapIso e₃)))

end ReducedComponentsAffine

/-- A closed subscheme of an affine scheme is affine; in particular the reduced induced
subscheme on a closed subset of an affine scheme is affine. -/
theorem isAffine_reducedInducedSubscheme_of_isAffine {X : Scheme.{u}} [IsAffine X]
    (Z : Closeds X) : IsAffine (reducedInducedSubscheme Z) :=
  isAffine_of_isAffineHom (reducedInducedSubschemeι Z)

/-- The easy direction of Hartshorne III, Ex. 3.2: if `X` is affine, each irreducible component
of `X` with its reduced induced structure is affine. -/
theorem forall_irreducibleComponents_isAffine_of_isAffine (X : Scheme.{u}) [IsAffine X] :
    ∀ (Z : Set X) (hZ : Z ∈ irreducibleComponents X),
      IsAffine (reducedInducedSubscheme ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩) :=
  fun Z hZ => isAffine_reducedInducedSubscheme_of_isAffine
    ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩

namespace ReducedComponentsAffine

variable {X : Scheme.{u}}

/-- A closed subscheme of a Noetherian scheme is Noetherian. -/
instance isNoetherian_reducedInducedSubscheme [IsNoetherian X] (W : Closeds X) :
    IsNoetherian (reducedInducedSubscheme W) :=
  have := LocallyOfFiniteType.isLocallyNoetherian (reducedInducedSubschemeι W)
  have : CompactSpace (reducedInducedSubscheme W) :=
    (reducedInducedSubschemeι W).isClosedEmbedding.compactSpace
  {}

/-- The preimage of a closed subset `A` in the reduced induced subscheme on `W`. -/
def preimageCloseds (W A : Closeds X) : Closeds (reducedInducedSubscheme W) :=
  ⟨reducedInducedSubschemeι W ⁻¹' A, A.isClosed.preimage (reducedInducedSubschemeι W).continuous⟩

/-- For closed `A ⊆ W`, the reduced induced subscheme on `A` inside the reduced induced subscheme
on `W` is isomorphic to the reduced induced subscheme on `A` in `X`: both are reduced closed
subschemes of `X` supported on `A`. -/
theorem isAffine_reducedInducedSubscheme_preimageCloseds {W A : Closeds X} (hAW : A ≤ W)
    [IsAffine (reducedInducedSubscheme A)] :
    IsAffine (reducedInducedSubscheme (preimageCloseds W A)) := by
  set j := reducedInducedSubschemeι (preimageCloseds W A) ≫ reducedInducedSubschemeι W
  have hj : Set.range j = (A : Set X) := by
    simp only [j, Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.coe_comp, Set.range_comp]
    rw [range_reducedInducedSubschemeι]
    change reducedInducedSubschemeι W '' (reducedInducedSubschemeι W ⁻¹' A) = _
    rw [Set.image_preimage_eq_inter_range, range_reducedInducedSubschemeι]
    exact Set.inter_eq_left.2 hAW
  obtain ⟨g, hg, -⟩ := existsUnique_reducedInducedSubschemeι_factorization A j hj
  have : IsClosedImmersion g := by
    have : IsClosedImmersion (g ≫ j) := by rw [hg]; infer_instance
    exact IsClosedImmersion.of_comp_isClosedImmersion g j
  have : Surjective g := by
    refine ⟨fun y => ?_⟩
    have hy : j y ∈ Set.range (reducedInducedSubschemeι A) := by
      rw [range_reducedInducedSubschemeι, ← hj]
      exact ⟨y, rfl⟩
    obtain ⟨x, hx⟩ := hy
    refine ⟨x, j.isClosedEmbedding.injective ?_⟩
    rw [← hx, ← hg]
    rfl
  have := isIso_of_isClosedImmersion_of_surjective g
  exact IsAffine.of_isIso (inv g)

/-- The two-piece case of Hartshorne III, Ex. 3.2, as a statement: a reduced Noetherian scheme
which is the union of two closed subsets whose reduced induced subschemes are affine is
affine. -/
def TwoPieceAffine : Prop :=
  ∀ (Y : Scheme.{u}) [IsReduced Y] [IsNoetherian Y] (A B : Closeds Y), A ⊔ B = ⊤ →
    IsAffine (reducedInducedSubscheme A) → IsAffine (reducedInducedSubscheme B) → IsAffine Y

/-- The remaining sheaf-theoretic input for the two-piece case: on a reduced Noetherian `Y = A ∪ B`,
every quasi-coherent ideal sheaf `J` sits in a short exact sequence `0 ⟶ F' ⟶ J ⟶ F'' ⟶ 0` with
`F'` the pushforward of a quasi-coherent module on the reduced induced subscheme on `B` and `F''`
that of one on the reduced induced subscheme on `A` (in the book's argument, `F' = I_A J`, killed
by `I_B`, and `F'' = J / I_A J`, killed by `I_A`). -/
def TwoPieceSequences : Prop :=
  ∀ (Y : Scheme.{u}) [IsReduced Y] [IsNoetherian Y] (A B : Closeds Y), A ⊔ B = ⊤ →
    ∀ J : QuasicoherentIdealSubsheaf Y, ∃ (S : ShortComplex Y.Modules) (_ : S.ShortExact)
      (_ : S.X₂ ≅ J.toModules) (G₁ : (reducedInducedSubscheme B).Modules)
      (G₂ : (reducedInducedSubscheme A).Modules) (_ : G₁.IsQuasicoherent)
      (_ : G₂.IsQuasicoherent),
      Nonempty (S.X₁ ≅ (Scheme.Modules.pushforward (reducedInducedSubschemeι B)).obj G₁) ∧
        Nonempty (S.X₃ ≅ (Scheme.Modules.pushforward (reducedInducedSubschemeι A)).obj G₂)

/-- Serre's criterion (Hartshorne III, Theorem 3.7, (iii) ⇒ (i)) reduces the two-piece case to
`TwoPieceSequences`. -/
theorem twoPieceAffine_of_twoPieceSequences (h : TwoPieceSequences.{u}) : TwoPieceAffine.{u} := by
  intro Y _ _ A B hAB hA hB
  refine ((isAffine_tfae_sheafCohomology Y).out 2 0).mp fun J _ => ?_
  obtain ⟨S, hS, e, G₁, G₂, _, _, ⟨e₁⟩, ⟨e₃⟩⟩ := h Y A B hAB J
  exact (isZero_H1_of_shortExact_pushforward _ _ hS G₁ G₂ e₁ e₃).of_iso
    ((sheafCohomology Y.toTopCat 1).mapIso ((SheafOfModules.toSheaf Y.ringCatSheaf).mapIso e.symm))

/-- From the two-piece case: if the reduced induced subschemes on closed `A` and `B` are affine,
so is the one on `A ∪ B`. -/
theorem isAffine_reducedInducedSubscheme_sup (h2 : TwoPieceAffine.{u}) [IsNoetherian X]
    {A B : Closeds X} (hA : IsAffine (reducedInducedSubscheme A))
    (hB : IsAffine (reducedInducedSubscheme B)) : IsAffine (reducedInducedSubscheme (A ⊔ B)) := by
  refine h2 _ (preimageCloseds (A ⊔ B) A) (preimageCloseds (A ⊔ B) B) ?_
    (isAffine_reducedInducedSubscheme_preimageCloseds le_sup_left)
    (isAffine_reducedInducedSubscheme_preimageCloseds le_sup_right)
  refine eq_top_iff.2 fun y _ => ?_
  have hy : reducedInducedSubschemeι (A ⊔ B) y ∈ ((A ⊔ B : Closeds X) : Set X) := by
    rw [← range_reducedInducedSubschemeι]
    exact ⟨y, rfl⟩
  exact hy

/-- From the two-piece case: finite unions of closed subsets with affine reduced induced
subschemes have affine reduced induced subschemes. -/
theorem isAffine_reducedInducedSubscheme_finset_sup (h2 : TwoPieceAffine.{u}) [IsNoetherian X]
    {ι : Type*} (f : ι → Closeds X) (S : Finset ι)
    (hS : ∀ c ∈ S, IsAffine (reducedInducedSubscheme (f c))) :
    IsAffine (reducedInducedSubscheme (S.sup f)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have : IsEmpty (reducedInducedSubscheme (⊥ : Closeds X)) := by
      refine ⟨fun y => ?_⟩
      have hy : reducedInducedSubschemeι (⊥ : Closeds X) y ∈ ((⊥ : Closeds X) : Set X) := by
        rw [← range_reducedInducedSubschemeι]
        exact ⟨y, rfl⟩
      exact hy
    rw [Finset.sup_empty]
    exact isAffine_of_isEmpty
  | insert a S ha ih =>
    rw [Finset.sup_insert]
    exact isAffine_reducedInducedSubscheme_sup h2 (hS a (Finset.mem_insert_self a S))
      (ih fun c hc => hS c (Finset.mem_insert_of_mem hc))

/-- A reduced scheme is isomorphic to the reduced induced subscheme on its whole space. -/
theorem isAffine_of_isAffine_reducedInducedSubscheme_top [IsReduced X]
    (h : IsAffine (reducedInducedSubscheme (⊤ : Closeds X))) : IsAffine X := by
  have : Surjective (reducedInducedSubschemeι (⊤ : Closeds X)) := by
    refine ⟨fun x => ?_⟩
    have hx : x ∈ Set.range (reducedInducedSubschemeι (⊤ : Closeds X)) := by
      rw [range_reducedInducedSubschemeι]
      trivial
    exact hx
  have := isIso_of_isClosedImmersion_of_surjective (reducedInducedSubschemeι (⊤ : Closeds X))
  exact IsAffine.of_isIso (inv (reducedInducedSubschemeι (⊤ : Closeds X)))

/-- The hard direction of Hartshorne III, Ex. 3.2, from the two-piece case. -/
theorem isAffine_of_forall_irreducibleComponents_of_twoPiece (h2 : TwoPieceAffine.{u})
    (X : Scheme.{u}) [IsReduced X] [IsNoetherian X]
    (h : ∀ (Z : Set X) (hZ : Z ∈ irreducibleComponents X),
      IsAffine (reducedInducedSubscheme ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩)) :
    IsAffine X := by
  classical
  have hfin := finite_irreducibleComponents_of_isNoetherian (X := X)
  let f : Set X → Closeds X := fun Z => Closeds.closure Z
  refine isAffine_of_isAffine_reducedInducedSubscheme_top ?_
  have htop : hfin.toFinset.sup f = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    have hx : x ∈ ⋃₀ irreducibleComponents X := by
      rw [sUnion_irreducibleComponents]; trivial
    obtain ⟨Z, hZ, hxZ⟩ := hx
    have hle : f Z ≤ hfin.toFinset.sup f := Finset.le_sup (hfin.mem_toFinset.2 hZ)
    exact hle (subset_closure hxZ)
  rw [← htop]
  refine isAffine_reducedInducedSubscheme_finset_sup h2 f _ fun Z hZ => ?_
  have hZ' := hfin.mem_toFinset.1 hZ
  have hf : f Z = ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ'⟩ :=
    Closeds.ext (isClosed_of_mem_irreducibleComponents Z hZ').closure_eq
  rw [hf]
  exact h Z hZ'

end ReducedComponentsAffine

namespace ReducedComponentsAffine

/-- Hartshorne III, Ex. 3.2, conditional on the remaining input `TwoPieceSequences`: a reduced
Noetherian scheme is affine iff each irreducible component with its reduced induced structure is
affine. -/
theorem isAffine_iff_of_twoPieceSequences (h : TwoPieceSequences.{u}) (X : Scheme.{u})
    [IsReduced X] [IsNoetherian X] :
    IsAffine X ↔ ∀ (Z : Set X) (hZ : Z ∈ irreducibleComponents X),
      IsAffine (reducedInducedSubscheme ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩) :=
  ⟨fun _ => forall_irreducibleComponents_isAffine_of_isAffine X,
    isAffine_of_forall_irreducibleComponents_of_twoPiece (twoPieceAffine_of_twoPieceSequences h) X⟩

end ReducedComponentsAffine

end Hartshorne

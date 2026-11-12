/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.SerreAffinenessCriterion
import Hartshorne.Cohomology.ClosedPushforwardCohomology
import Hartshorne.Scheme.ReducedInducedSubscheme
import Hartshorne.Scheme.ReducedInducedSmallest
import Hartshorne.Cohomology.ReductionAffineIff

/-!
# Affineness of reduced irreducible components

Hartshorne, *Algebraic Geometry*, III, Exercise 3.2 (p. 216): a reduced Noetherian scheme is
affine iff each of its irreducible components, with the reduced induced structure, is affine
(`Hartshorne.isAffine_iff_forall_irreducibleComponents_isAffine`).

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
* Modules killed by the ideal of a closed subscheme: if `I` cuts out `i : Z ⟶ Y` and the
  quasi-coherent `𝒪_Y`-module `Q` is killed by `I`, then `Q ≅ i_* G` for a quasi-coherent
  `𝒪_Z`-module `G` (`ReducedComponentsAffine.ClosedDescent.exists_isQuasicoherent_iso_pushforward`).
  Here `G(V) = Q(up V)`, where `up V` is the largest open of `Y` meeting `Z` in `V`; a section of
  `𝒪_Z` acts by gluing the actions of local lifts to `𝒪_Y` over affine opens.
* `TwoPieceSequences` (`ReducedComponentsAffine.twoPieceSequences`): on a reduced `Y = A ∪ B`,
  `I_B I_A ⊆ I_A ∩ I_B = 0`, so for a quasi-coherent ideal sheaf `J` the sequence
  `0 ⟶ I_A J ⟶ J ⟶ J / I_A J ⟶ 0` has its first term killed by `I_B` and its last by `I_A`.
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
  exact eqToIso e₁ ≪≫
    (closedPushforwardCohomologyIso S i.isClosedEmbedding.isClosed_range _ n).symm ≪≫
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

/-- The sheaf-theoretic input for the two-piece case: on a reduced Noetherian `Y = A ∪ B`,
every quasi-coherent ideal sheaf `J` sits in a short exact sequence `0 ⟶ F' ⟶ J ⟶ F'' ⟶ 0` with
`F'` the pushforward of a quasi-coherent module on the reduced induced subscheme on `B` and `F''`
that of one on the reduced induced subscheme on `A` (in `twoPieceSequences`, `F' = I_A J`, killed
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

/-! ### Modules killed by the ideal of a closed subscheme -/

namespace ClosedDescent

open Opposite ArtinReesKernelSheaf

variable {Y : Scheme.{u}} (I : Y.IdealSheafData)

/-- For an open `V` of the closed subscheme `Z` cut out by `I`, the largest open of `Y` meeting
`Z` in `V`: the complement of the image of `Z ∖ V`. -/
def up (V : I.subscheme.Opens) : Y.Opens :=
  ⟨(I.subschemeι '' (V : Set I.subscheme)ᶜ)ᶜ,
    (I.subschemeι.isClosedEmbedding.isClosedMap _ V.isOpen.isClosed_compl).isOpen_compl⟩

variable {I}

theorem mem_up {V : I.subscheme.Opens} {y : Y} :
    y ∈ up I V ↔ ∀ z, I.subschemeι z = y → z ∈ V := by
  change y ∉ I.subschemeι '' (V : Set I.subscheme)ᶜ ↔ _
  constructor
  · intro h z hz
    by_contra hzV
    exact h ⟨z, hzV, hz⟩
  · rintro h ⟨z, hzV, hz⟩
    exact hzV (h z hz)

theorem up_mono {V V' : I.subscheme.Opens} (h : V ≤ V') : up I V ≤ up I V' :=
  fun _ hy => mem_up.2 fun z hz => h (mem_up.1 hy z hz)

theorem preimage_le_of_le_up {V : I.subscheme.Opens} {W : Y.Opens} (h : W ≤ up I V) :
    I.subschemeι ⁻¹ᵁ W ≤ V :=
  fun z hz => mem_up.1 (h hz) z rfl

theorem le_up_preimage (U : Y.Opens) : U ≤ up I (I.subschemeι ⁻¹ᵁ U) :=
  fun _ hy => mem_up.2 fun _ hz => by
    subst hz
    exact hy

theorem up_le_sup (U : Y.Opens) {V : I.subscheme.Opens} (h : V ≤ I.subschemeι ⁻¹ᵁ U) :
    up I V ≤ U ⊔ up I ⊥ := by
  intro y hy
  by_cases hy' : ∃ z, I.subschemeι z = y
  · obtain ⟨z, rfl⟩ := hy'
    exact Opens.mem_sup.2 (Or.inl (h (mem_up.1 hy z rfl)))
  · exact Opens.mem_sup.2 (Or.inr (mem_up.2 fun z hz => (hy' ⟨z, hz⟩).elim))

theorem up_inf_le (V V' : I.subscheme.Opens) : up I V ⊓ up I V' ≤ up I (V ⊓ V') :=
  fun _ hy => mem_up.2 fun z hz =>
    Opens.mem_inf.2 ⟨mem_up.1 (Opens.mem_inf.1 hy).1 z hz, mem_up.1 (Opens.mem_inf.1 hy).2 z hz⟩

theorem up_iSup_le {ι : Type*} (V : ι → I.subscheme.Opens) :
    up I (iSup V) ≤ up I ⊥ ⊔ ⨆ k, up I (V k) := by
  intro y hy
  by_cases hy' : ∃ z, I.subschemeι z = y
  · obtain ⟨z, rfl⟩ := hy'
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (mem_up.1 hy z rfl)
    refine Opens.mem_sup.2 (Or.inr (Opens.mem_iSup.2 ⟨k, mem_up.2 fun z' hz' => ?_⟩))
    rwa [I.subschemeι.isClosedEmbedding.injective hz']
  · exact Opens.mem_sup.2 (Or.inl (mem_up.2 fun z hz => (hy' ⟨z, hz⟩).elim))

theorem subschemeι_app_res {U W : Y.Opens} (h : W ≤ U) (c : Γ(Y, U)) :
    I.subschemeι.app W (Y.presheaf.map (homOfLE h).op c) =
      I.subscheme.presheaf.map
        (homOfLE (fun _ hz => h hz : I.subschemeι ⁻¹ᵁ W ≤ I.subschemeι ⁻¹ᵁ U)).op
        (I.subschemeι.app U c) :=
  congrArg (fun φ => φ.hom c) (I.subschemeι.naturality (homOfLE h).op)

variable {Q : Y.Modules}
  (hQ : ∀ (U : Y.affineOpens) (c : Γ(Y, U)), c ∈ I.ideal U → ∀ s : Γ(Q, U), c • s = 0)

include hQ in
/-- Sections of `𝒪_Y` vanishing on the closed subscheme kill `Q`. -/
theorem smul_eq_zero_of_app_eq_zero {U : Y.Opens} (c : Γ(Y, U))
    (hc : I.subschemeι.app U c = 0) (s : Γ(Q, U)) : c • s = 0 := by
  apply ReductionAffine.eq_zero_of_locally _ (c • s)
  intro x hx
  obtain ⟨W, hWU, hxW⟩ := exists_affine_le hx
  refine ⟨W, hWU, hxW, ?_⟩
  rw [LinearMap.map_smulₛₗ]
  refine hQ W _ ?_ _
  have h1 : I.subschemeι.app W (Y.presheaf.map (homOfLE hWU).op c) = 0 := by
    rw [subschemeι_app_res, hc, map_zero]
  have h2 : Y.presheaf.map (homOfLE hWU).op c ∈ RingHom.ker (I.subschemeι.app W).hom := h1
  rwa [Scheme.IdealSheafData.ker_subschemeι_app] at h2

include hQ in
/-- `Q` has no sections over opens disjoint from the closed subscheme. -/
theorem eq_zero_of_le_up_bot {W : Y.Opens} (hW : W ≤ up I ⊥) (s : Γ(Q, W)) : s = 0 := by
  have h0 : I.subschemeι ⁻¹ᵁ W = ⊥ := le_bot_iff.1 (preimage_le_of_le_up hW)
  have : Subsingleton Γ(I.subscheme, I.subschemeι ⁻¹ᵁ W) := by rw [h0]; infer_instance
  rw [← one_smul Γ(Y, W) s]
  exact smul_eq_zero_of_app_eq_zero hQ 1 (Subsingleton.elim _ _) s

include hQ in
theorem res_injective_of_le_sup {U U' : Y.Opens} (h : U ≤ U') (h' : U' ≤ U ⊔ up I ⊥) :
    Function.Injective (res Q h) := by
  refine (injective_iff_map_eq_zero (res Q h)).2 fun s hs => ?_
  apply ReductionAffine.eq_zero_of_locally Q s
  intro x hx
  rcases Opens.mem_sup.1 (h' hx) with hxU | hxB
  · exact ⟨U, h, hxU, hs⟩
  · exact ⟨U' ⊓ up I ⊥, inf_le_left, Opens.mem_inf.2 ⟨hx, hxB⟩,
      eq_zero_of_le_up_bot hQ inf_le_right _⟩

include hQ in
theorem res_surjective_of_le_sup {U U' : Y.Opens} (h : U ≤ U') (h' : U' ≤ U ⊔ up I ⊥) :
    Function.Surjective (res Q h) := by
  intro t
  let M' : TopCat.Sheaf AddCommGrpCat.{u} Y := ⟨Q.val.presheaf, Q.isSheaf⟩
  let W : Bool → Y.Opens := fun b => bif b then U else U' ⊓ up I ⊥
  let sf : ∀ b : Bool, ToType (M'.1.obj (op (W b))) := fun b =>
    match b with
    | true => t
    | false => 0
  have hsf : TopCat.Presheaf.IsCompatible M'.1 W sf := by
    rintro (_ | _) (_ | _)
    · exact (eq_zero_of_le_up_bot hQ (inf_le_left.trans inf_le_right) _).trans
        (eq_zero_of_le_up_bot hQ (inf_le_left.trans inf_le_right) _).symm
    · exact (eq_zero_of_le_up_bot hQ (inf_le_left.trans inf_le_right) _).trans
        (eq_zero_of_le_up_bot hQ (inf_le_left.trans inf_le_right) _).symm
    · exact (eq_zero_of_le_up_bot hQ (inf_le_right.trans inf_le_right) _).trans
        (eq_zero_of_le_up_bot hQ (inf_le_right.trans inf_le_right) _).symm
    · rfl
  have hcover : U' ≤ iSup W := fun x hx => by
    rcases Opens.mem_sup.1 (h' hx) with hxU | hxB
    · exact Opens.mem_iSup.2 ⟨true, hxU⟩
    · exact Opens.mem_iSup.2 ⟨false, Opens.mem_inf.2 ⟨hx, hxB⟩⟩
  obtain ⟨s, hs, -⟩ := M'.existsUnique_gluing' W U'
    (fun b => homOfLE (by cases b; exacts [inf_le_left, h])) hcover sf hsf
  exact ⟨s, hs true⟩

variable (I) in
/-- `V ↦ up V` as a functor. -/
def upFunctor : I.subscheme.Opens ⥤ Y.Opens :=
  Monotone.functor (f := up I) fun _ _ h => up_mono h

variable (I) in
/-- The presheaf `V ↦ Q(up V)` on the closed subscheme. -/
abbrev upPresheaf (Q : Y.Modules) : (Opens I.subscheme.toTopCat)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (upFunctor I).op ⋙ Q.presheaf

include hQ in
theorem isSheaf_upPresheaf : TopCat.Presheaf.IsSheaf (upPresheaf I Q) := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι V sf hsf
  let M' : TopCat.Sheaf AddCommGrpCat.{u} Y := ⟨Q.val.presheaf, Q.isSheaf⟩
  let W : Option ι → Y.Opens := fun k => k.elim (up I ⊥) fun k => up I (V k)
  let tf : ∀ k : Option ι, ToType (M'.1.obj (op (W k))) := fun k =>
    match k with
    | none => 0
    | some k => sf k
  have htf : TopCat.Presheaf.IsCompatible M'.1 W tf := by
    rintro (_ | k) (_ | l)
    · exact (eq_zero_of_le_up_bot hQ inf_le_left _).trans
        (eq_zero_of_le_up_bot hQ inf_le_left _).symm
    · exact (eq_zero_of_le_up_bot hQ inf_le_left _).trans
        (eq_zero_of_le_up_bot hQ inf_le_left _).symm
    · exact (eq_zero_of_le_up_bot hQ inf_le_right _).trans
        (eq_zero_of_le_up_bot hQ inf_le_right _).symm
    · have h := congrArg (res Q (up_inf_le (V k) (V l))) (hsf k l)
      change res Q _ (res Q (up_mono inf_le_left) (sf k)) =
        res Q _ (res Q (up_mono inf_le_right) (sf l)) at h
      change res Q (inf_le_left : up I (V k) ⊓ up I (V l) ≤ up I (V k)) (sf k) =
        res Q (inf_le_right : up I (V k) ⊓ up I (V l) ≤ up I (V l)) (sf l)
      exact (res_res Q _ _ _).symm.trans (h.trans (res_res Q _ _ _))
  have hcover : up I (iSup V) ≤ iSup W :=
    (up_iSup_le V).trans (sup_le (le_iSup W none) (iSup_le fun k => le_iSup W (some k)))
  obtain ⟨t, ht, ht'⟩ := M'.existsUnique_gluing' W (up I (iSup V))
    (fun k => homOfLE (by rcases k with _ | k; exacts [up_mono bot_le, up_mono (le_iSup V k)]))
    hcover tf htf
  refine ⟨t, fun k => ht (some k), fun t' ht'' => ht' t' ?_⟩
  rintro (_ | k)
  · exact (eq_zero_of_le_up_bot hQ le_rfl _).trans (eq_zero_of_le_up_bot hQ le_rfl _).symm
  · exact ht'' k

/-- `b` lifts `a` over `W`. -/
def IsLift {V : I.subscheme.Opens} (a : Γ(I.subscheme, V)) {W : Y.Opens} (hW : W ≤ up I V)
    (b : Γ(Y, W)) : Prop :=
  I.subschemeι.app W b = I.subscheme.presheaf.map (homOfLE (preimage_le_of_le_up hW)).op a

theorem exists_isLift {V : I.subscheme.Opens} (a : Γ(I.subscheme, V)) (W : Y.affineOpens)
    (hW : (W : Y.Opens) ≤ up I V) : ∃ b : Γ(Y, W), IsLift a hW b :=
  I.subschemeι_app_surjective W _

theorem IsLift.res {V : I.subscheme.Opens} {a : Γ(I.subscheme, V)} {W : Y.Opens}
    {hW : W ≤ up I V} {b : Γ(Y, W)} (hb : IsLift a hW b) {W' : Y.Opens} (h : W' ≤ W) :
    IsLift a (h.trans hW) (Y.presheaf.map (homOfLE h).op b) := by
  unfold IsLift at hb ⊢
  rw [subschemeι_app_res, hb, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

include hQ in
theorem IsLift.smul_eq {V : I.subscheme.Opens} {a : Γ(I.subscheme, V)} {W : Y.Opens}
    {hW : W ≤ up I V} {b b' : Γ(Y, W)} (hb : IsLift a hW b) (hb' : IsLift a hW b')
    (s : Γ(Q, W)) : b • s = b' • s := by
  rw [← sub_eq_zero, ← sub_smul]
  refine smul_eq_zero_of_app_eq_zero hQ _ ?_ s
  rw [map_sub]
  exact sub_eq_zero.mpr (hb.trans hb'.symm)

theorem isLift_self (U : Y.Opens) (r : Γ(Y, U)) :
    IsLift (I.subschemeι.app U r) (le_up_preimage U) r := by
  unfold IsLift
  change _ = I.subscheme.presheaf.map (𝟙 (op (I.subschemeι ⁻¹ᵁ U))) _
  rw [CategoryTheory.Functor.map_id]
  rfl

include hQ in
theorem exists_glue (V : I.subscheme.Opens) (a : Γ(I.subscheme, V)) (s : Γ(Q, up I V)) :
    ∃ t : Γ(Q, up I V), ∀ (W : Y.Opens) (hW : W ≤ up I V) (b : Γ(Y, W)),
      IsLift a hW b → res Q hW t = b • res Q hW s := by
  let ι := {W : Y.affineOpens // (W : Y.Opens) ≤ up I V}
  let Wf : ι → Y.Opens := fun W => W.1
  choose b hb using fun W : ι => exists_isLift a W.1 W.2
  let M' : TopCat.Sheaf AddCommGrpCat.{u} Y := ⟨Q.val.presheaf, Q.isSheaf⟩
  have hcover : up I V ≤ iSup Wf := fun x hx => by
    obtain ⟨W, hWU, hxW⟩ := exists_affine_le hx
    exact Opens.mem_iSup.mpr ⟨⟨W, hWU⟩, hxW⟩
  let sf : ∀ W : ι, ToType (M'.1.obj (op (Wf W))) := fun W => b W • res Q W.2 s
  have hsf : TopCat.Presheaf.IsCompatible M'.1 Wf sf := by
    intro W₁ W₂
    have h₁ := (hb W₁).res (inf_le_left : (W₁.1 : Y.Opens) ⊓ W₂.1 ≤ W₁.1)
    have h₂ := (hb W₂).res (inf_le_right : (W₁.1 : Y.Opens) ⊓ W₂.1 ≤ W₂.1)
    change res Q inf_le_left (b W₁ • res Q W₁.2 s) = res Q inf_le_right (b W₂ • res Q W₂.2 s)
    rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, res_res, res_res]
    exact h₁.smul_eq hQ h₂ _
  obtain ⟨t₀, ht, -⟩ := M'.existsUnique_gluing' Wf (up I V)
    (fun W => CategoryTheory.homOfLE W.2) hcover sf hsf
  let t : Γ(Q, up I V) := t₀
  refine ⟨t, fun W hW c hc => ?_⟩
  refine ReductionAffine.ext_of_affine Q fun W' hW' => ?_
  rw [res_res, LinearMap.map_smulₛₗ, res_res]
  have e1 : res Q (hW'.trans hW) t = b ⟨W', hW'.trans hW⟩ • res Q (hW'.trans hW) s :=
    ht ⟨W', hW'.trans hW⟩
  rw [e1]
  exact (hb ⟨W', hW'.trans hW⟩).smul_eq hQ (hc.res hW') _

/-- The action of `Γ(Z, V)` on `Γ(Q, up V)`. -/
def upSMul (V : I.subscheme.Opens) (a : Γ(I.subscheme, V)) (s : Γ(Q, up I V)) :
    Γ(Q, up I V) :=
  (exists_glue hQ V a s).choose

theorem upSMul_spec (V : I.subscheme.Opens) (a : Γ(I.subscheme, V)) (s : Γ(Q, up I V))
    {W : Y.Opens} (hW : W ≤ up I V) {b : Γ(Y, W)} (hb : IsLift a hW b) :
    res Q hW (upSMul hQ V a s) = b • res Q hW s :=
  (exists_glue hQ V a s).choose_spec W hW b hb

theorem isLift_one (V : I.subscheme.Opens) {W : Y.Opens} (hW : W ≤ up I V) :
    IsLift (1 : Γ(I.subscheme, V)) hW 1 := by
  unfold IsLift
  rw [map_one, map_one]

theorem IsLift.mul {V : I.subscheme.Opens} {a a' : Γ(I.subscheme, V)} {W : Y.Opens}
    {hW : W ≤ up I V} {b b' : Γ(Y, W)} (hb : IsLift a hW b) (hb' : IsLift a' hW b') :
    IsLift (a * a') hW (b * b') := by
  unfold IsLift at *
  rw [map_mul, map_mul, hb, hb']

theorem IsLift.add {V : I.subscheme.Opens} {a a' : Γ(I.subscheme, V)} {W : Y.Opens}
    {hW : W ≤ up I V} {b b' : Γ(Y, W)} (hb : IsLift a hW b) (hb' : IsLift a' hW b') :
    IsLift (a + a') hW (b + b') := by
  unfold IsLift at *
  rw [map_add, map_add, hb, hb']

theorem isLift_zero (V : I.subscheme.Opens) {W : Y.Opens} (hW : W ≤ up I V) :
    IsLift (0 : Γ(I.subscheme, V)) hW 0 := by
  unfold IsLift
  rw [map_zero, map_zero]

/-- `Γ(Q, up V)` as a `Γ(Z, V)`-module. -/
@[instance_reducible]
def upModule (V : I.subscheme.Opens) : Module Γ(I.subscheme, V) Γ(Q, up I V) where
  smul := upSMul hQ V
  one_smul s := ReductionAffine.ext_of_affine Q fun W hW =>
    (upSMul_spec hQ V 1 s hW (isLift_one V hW)).trans (one_smul _ _)
  mul_smul a a' s := ReductionAffine.ext_of_affine Q fun W hW => by
    obtain ⟨b, hb⟩ := exists_isLift a W hW
    obtain ⟨b', hb'⟩ := exists_isLift a' W hW
    change res Q hW (upSMul hQ V (a * a') s) = res Q hW (upSMul hQ V a (upSMul hQ V a' s))
    rw [upSMul_spec hQ V _ s hW (hb.mul hb'), upSMul_spec hQ V a _ hW hb,
      upSMul_spec hQ V a' s hW hb', mul_smul]
  smul_zero a := ReductionAffine.ext_of_affine Q fun W hW => by
    obtain ⟨b, hb⟩ := exists_isLift a W hW
    change res Q hW (upSMul hQ V a 0) = res Q hW 0
    rw [upSMul_spec hQ V a 0 hW hb, map_zero, smul_zero]
  smul_add a s s' := ReductionAffine.ext_of_affine Q fun W hW => by
    obtain ⟨b, hb⟩ := exists_isLift a W hW
    change res Q hW (upSMul hQ V a (s + s')) =
      res Q hW (upSMul hQ V a s + upSMul hQ V a s')
    rw [upSMul_spec hQ V a _ hW hb, map_add, map_add, smul_add, upSMul_spec hQ V a s hW hb,
      upSMul_spec hQ V a s' hW hb]
  add_smul a a' s := ReductionAffine.ext_of_affine Q fun W hW => by
    obtain ⟨b, hb⟩ := exists_isLift a W hW
    obtain ⟨b', hb'⟩ := exists_isLift a' W hW
    change res Q hW (upSMul hQ V (a + a') s) =
      res Q hW (upSMul hQ V a s + upSMul hQ V a' s)
    rw [upSMul_spec hQ V _ s hW (hb.add hb'), map_add, add_smul, upSMul_spec hQ V a s hW hb,
      upSMul_spec hQ V a' s hW hb']
  zero_smul s := ReductionAffine.ext_of_affine Q fun W hW => by
    change res Q hW (upSMul hQ V 0 s) = res Q hW 0
    rw [upSMul_spec hQ V 0 s hW (isLift_zero V hW), zero_smul, map_zero]

/-- The action of `Γ(Z, -)` is compatible with restriction. -/
theorem upSMul_res {V V' : I.subscheme.Opens} (h : V' ≤ V) (a : Γ(I.subscheme, V))
    (s : Γ(Q, up I V)) :
    res Q (up_mono h) (upSMul hQ V a s) =
      upSMul hQ V' (I.subscheme.presheaf.map (homOfLE h).op a) (res Q (up_mono h) s) := by
  refine ReductionAffine.ext_of_affine Q fun W hW => ?_
  obtain ⟨b, hb⟩ := exists_isLift a W (hW.trans (up_mono h))
  have hb' : IsLift (I.subscheme.presheaf.map (homOfLE h).op a) hW b := by
    unfold IsLift at hb ⊢
    rw [hb, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  rw [res_res, upSMul_spec hQ V a s _ hb, upSMul_spec hQ V' _ _ hW hb', res_res]

/-- An `𝒪_Y`-module killed by `I`, as an `𝒪_Z`-module on the closed subscheme `Z` cut out by
`I`: its sections over `V` are those of `Q` over the largest open of `Y` meeting `Z` in `V`. -/
def descent : I.subscheme.Modules where
  val :=
    letI : ∀ V : (Opens I.subscheme.toTopCat)ᵒᵖ,
        Module (I.subscheme.ringCatSheaf.obj.obj V) ((upPresheaf I Q).obj V) :=
      fun V => upModule hQ V.unop
    PresheafOfModules.ofPresheaf (upPresheaf I Q)
      (fun _ _ f a s => upSMul_res hQ (leOfHom f.unop) a s)
  isSheaf := isSheaf_upPresheaf hQ

theorem presheaf_map_map {X : Scheme.{u}} {A B C : X.Opens} (h : B ≤ A) (h' : C ≤ B)
    (h'' : C ≤ A) (x : Γ(X, A)) :
    X.presheaf.map (homOfLE h').op (X.presheaf.map (homOfLE h).op x) =
      X.presheaf.map (homOfLE h'').op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Two composites of restriction maps with the same source and target agree. -/
theorem presheaf_map_comp_eq (Q : Y.Modules) {A B B' C : Y.Opensᵒᵖ} (f : A ⟶ B) (g : B ⟶ C)
    (f' : A ⟶ B') (g' : B' ⟶ C) :
    Q.presheaf.map f ≫ Q.presheaf.map g = Q.presheaf.map f' ≫ Q.presheaf.map g' := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

/-- The comparison `i_* (descent Q) ⟶ Q`, given by restriction `Q(up (i⁻¹ U)) ⟶ Q(U)`. -/
def descentHom : (Scheme.Modules.pushforward I.subschemeι).obj (descent hQ) ⟶ Q :=
  ⟨PresheafOfModules.homMk
    { app := fun U => Q.presheaf.map (homOfLE (le_up_preimage U.unop)).op
      naturality := fun U U' f => by
        change Q.presheaf.map _ ≫ Q.presheaf.map _ = Q.presheaf.map _ ≫ Q.presheaf.map _
        exact presheaf_map_comp_eq Q _ _ _ _ }
    fun U r m => upSMul_spec hQ _ _ m (le_up_preimage U.unop) (isLift_self U.unop r)⟩

include hQ in
theorem isIso_descentHom : IsIso (descentHom hQ) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro U
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ⟨res_injective_of_le_sup hQ (le_up_preimage U) (up_le_sup U le_rfl),
    res_surjective_of_le_sup hQ (le_up_preimage U) (up_le_sup U le_rfl)⟩

variable (I) in
/-- The affine open `i⁻¹ U` of the closed subscheme. -/
abbrev preimageAffine (U : Y.affineOpens) : I.subscheme.affineOpens :=
  ⟨I.subschemeι ⁻¹ᵁ (U : Y.Opens), U.2.preimage _⟩

theorem iSup_preimageAffine : (⨆ U : Y.affineOpens, ((preimageAffine I U :
    I.subscheme.affineOpens) : I.subscheme.Opens)) = ⊤ := by
  rw [eq_top_iff]
  intro z _
  obtain ⟨U, -, hU⟩ := exists_affine_le (show I.subschemeι z ∈ (⊤ : Y.Opens) from trivial)
  exact Opens.mem_iSup.mpr ⟨U, hU⟩

theorem isIso_fromTildeΓ_descent [Q.IsQuasicoherent] (U : Y.affineOpens) :
    IsIso (specRestriction (descent hQ) (preimageAffine I U)).fromTildeΓ := by
  have hU := up_le_sup (I := I) (U : Y.Opens) le_rfl
  refine isIso_fromTildeΓ_of_pow_smul _ _ (fun g s hs => ?_) (fun g t => ?_)
  · obtain ⟨g', rfl⟩ := I.subschemeι_app_surjective U g
    have hD : I.subscheme.basicOpen (I.subschemeι.app U g') =
        I.subschemeι ⁻¹ᵁ Y.basicOpen g' := (Scheme.preimage_basicOpen I.subschemeι g').symm
    have h1 : Y.basicOpen g' ≤ up I (I.subscheme.basicOpen (I.subschemeι.app U g')) :=
      hD ▸ le_up_preimage _
    have hs' : res Q (up_mono (I.subscheme.basicOpen_le _)) s = 0 := hs
    have hs₀ : Q.presheaf.map (homOfLE (Y.basicOpen_le g')).op
        (res Q (le_up_preimage (U : Y.Opens)) s) = 0 :=
      (res_res Q _ _ s).trans ((res_res Q _ h1 s).symm.trans
        ((congrArg (res Q h1) hs').trans (map_zero _)))
    obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_isAffineOpen Q U.2 g' _ hs₀
    refine ⟨n, res_injective_of_le_sup hQ (le_up_preimage (U : Y.Opens)) hU ?_⟩
    have hb := isLift_self (I := I) (U : Y.Opens) (g' ^ n)
    rw [map_pow] at hb
    change res Q _ (upSMul hQ (I.subschemeι ⁻¹ᵁ (U : Y.Opens)) ((I.subschemeι.app U g') ^ n) s) =
      res Q _ 0
    exact (upSMul_spec hQ _ _ s _ hb).trans (hn.trans (map_zero _).symm)
  · obtain ⟨g', rfl⟩ := I.subschemeι_app_surjective U g
    have hD : I.subscheme.basicOpen (I.subschemeι.app U g') =
        I.subschemeι ⁻¹ᵁ Y.basicOpen g' := (Scheme.preimage_basicOpen I.subschemeι g').symm
    have h1 : Y.basicOpen g' ≤ up I (I.subscheme.basicOpen (I.subschemeι.app U g')) :=
      hD ▸ le_up_preimage _
    have h2 := up_le_sup (I := I) (Y.basicOpen g') hD.le
    obtain ⟨n, s₀, hs₀⟩ := exists_pow_smul_extension_of_isAffineOpen Q U.2 g' (res Q h1 t)
    obtain ⟨s, rfl⟩ := res_surjective_of_le_sup hQ (le_up_preimage (U : Y.Opens)) hU s₀
    refine ⟨n, s, res_injective_of_le_sup hQ h1 h2 ?_⟩
    have hb : IsLift ((I.subscheme.presheaf.map (homOfLE (I.subscheme.basicOpen_le _)).op
        (I.subschemeι.app U g')) ^ n) h1
        ((Y.presheaf.map (homOfLE (Y.basicOpen_le g')).op g') ^ n) := by
      unfold IsLift
      rw [map_pow, map_pow, subschemeι_app_res, presheaf_map_map]
      exact fun _ hz => Y.basicOpen_le g' hz
    change res Q h1 (res Q (up_mono (I.subscheme.basicOpen_le _)) s) =
      res Q h1 (upSMul hQ _ _ t)
    refine (res_res Q _ h1 s).trans ?_
    refine Eq.trans ?_ (upSMul_spec hQ _ _ t h1 hb).symm
    exact (res_res Q _ _ s).symm.trans hs₀

theorem isQuasicoherent_descent [Q.IsQuasicoherent] : (descent hQ).IsQuasicoherent := by
  have h : HasAffineTildeCover (descent hQ) :=
    ⟨Y.affineOpens, preimageAffine I, iSup_preimageAffine, fun U =>
      ⟨_, ⟨@asIso _ _ _ _ (specRestriction (descent hQ) (preimageAffine I U)).fromTildeΓ
        (isIso_fromTildeΓ_descent hQ U)⟩⟩⟩
  exact ((quasicoherent_affine_local_tfae _).out 1 0).mp h

include hQ in
/-- **Modules killed by the ideal of a closed subscheme.** If `I` is a quasi-coherent ideal sheaf
on a scheme `Y`, cutting out the closed subscheme `i : Z ⟶ Y`, then every quasi-coherent
`𝒪_Y`-module `Q` killed by `I` is `i_* G` for a quasi-coherent `𝒪_Z`-module `G`. -/
theorem exists_isQuasicoherent_iso_pushforward [Q.IsQuasicoherent] :
    ∃ (G : I.subscheme.Modules) (_ : G.IsQuasicoherent),
      Nonempty (Q ≅ (Scheme.Modules.pushforward I.subschemeι).obj G) :=
  have := isIso_descentHom hQ
  ⟨descent hQ, isQuasicoherent_descent hQ, ⟨(asIso (descentHom hQ)).symm⟩⟩

end ClosedDescent

/-! ### The two-piece exact sequence -/

section TwoPiece

open ArtinReesKernelSheaf

variable {Y : Scheme.{u}}

/-- If `I' I = 0`, then `I'` kills the product `I N`. -/
theorem smul_eq_zero_of_mem_powSmul_one {E : Y.Modules} (I I' : Y.IdealSheafData)
    (hII' : ∀ U : Y.affineOpens, I'.ideal U * I.ideal U = ⊥) (N : E.val.Submodule)
    {U : Y.affineOpens} (c : Γ(Y, U)) (hc : c ∈ I'.ideal U) (s : Γ(E, U))
    (hs : s ∈ sub (powSmul I 1 N) U) : c • s = 0 := by
  apply ReductionAffine.eq_zero_of_locally E (c • s)
  intro x hx
  obtain ⟨V, hVU, hxV, hV⟩ := hs x hx
  refine ⟨V, hVU, hxV, ?_⟩
  rw [LinearMap.map_smulₛₗ]
  have hc' : (Y.presheaf.map (homOfLE hVU).op).hom c ∈ I'.ideal V :=
    I'.ideal_le_comap_ideal (U := V) (V := U) hVU hc
  change res E hVU s ∈ I.ideal V ^ 1 • sub N V at hV
  rw [pow_one] at hV
  have h := Submodule.smul_mem_smul hc' hV
  rw [← Submodule.mul_smul, hII', Submodule.bot_smul] at h
  exact (Submodule.mem_bot _).1 h

/-- A section of `I` times a section of `N` lies in `I N`. -/
theorem smul_mem_powSmul_one {E : Y.Modules} (I : Y.IdealSheafData) (N : E.val.Submodule)
    {U : Y.affineOpens} {V : Y.Opens} (hVU : V ≤ U) (c : Γ(Y, U)) (hc : c ∈ I.ideal U)
    {s : Γ(E, V)} (hs : s ∈ sub N V) :
    (Y.presheaf.map (homOfLE hVU).op).hom c • s ∈ sub (powSmul I 1 N) V := by
  intro y hy
  obtain ⟨W, hWV, hyW⟩ := exists_affine_le hy
  refine ⟨W, hWV, hyW, ?_⟩
  change res E hWV (_ • s) ∈ I.ideal W ^ 1 • sub N W
  rw [LinearMap.map_smulₛₗ, pow_one]
  refine Submodule.smul_mem_smul ?_ (res_mem N hWV hs)
  have h := I.ideal_le_comap_ideal (U := W) (V := U) (hWV.trans hVU) hc
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  exact h

variable (I : Y.IdealSheafData) (J : QuasicoherentIdealSubsheaf Y)

/-- The product `I J` of an ideal sheaf with a quasi-coherent ideal subsheaf. -/
abbrev prodIdeal : Y.Modules :=
  toModules (powSmul I 1 J.carrier) (isLocal_powSmul _ _ _)

/-- The inclusion `I J ⟶ J`. -/
abbrev prodι : prodIdeal I J ⟶ J.toModules :=
  inclusion _ J.isLocal (powSmul_le J.isLocal)

instance : Mono (prodι I J) := by
  have : Mono ((SheafOfModules.forget Y.ringCatSheaf).map (prodι I J)) :=
    inferInstanceAs (Mono (PresheafOfModules.Submodule.homOfLE _))
  exact (SheafOfModules.forget Y.ringCatSheaf).mono_of_mono_map this

/-- The short exact sequence `0 ⟶ I J ⟶ J ⟶ J / I J ⟶ 0`. -/
abbrev prodSC : ShortComplex Y.Modules :=
  ShortComplex.mk (prodι I J) (cokernel.π (prodι I J)) (cokernel.condition _)

theorem prodSC_shortExact : (prodSC I J).ShortExact :=
  ShortComplex.ShortExact.mk' ((prodSC I J).exact_of_g_is_cokernel (cokernelIsCokernel _))
    inferInstance inferInstance

instance isQuasicoherent_prodIdeal : (prodIdeal I J).IsQuasicoherent := by
  have := J.isQuasicoherent
  exact isQuasicoherent_powSmul I 1 J.isLocal

instance isQuasicoherent_cokernel_prodι : (cokernel (prodι I J)).IsQuasicoherent := by
  have := J.isQuasicoherent
  exact isQuasicoherent_cokernel _

/-- `I` kills `J / I J`. -/
theorem smul_eq_zero_cokernel_prodι {U : Y.affineOpens} (c : Γ(Y, U)) (hc : c ∈ I.ideal U)
    (s : Γ(cokernel (prodι I J), U)) : c • s = 0 := by
  apply ReductionAffine.eq_zero_of_locally _ (c • s)
  intro x hx
  obtain ⟨V, hVU, hxV, t, ht⟩ := modules_exists_local_lift (cokernel.π (prodι I J)) s hx
  refine ⟨V, hVU, hxV, ?_⟩
  set a' := (Y.presheaf.map (homOfLE hVU).op).hom c
  have hmem := smul_mem_powSmul_one I J.carrier hVU c hc (t : sub J.carrier V).2
  let t' : Γ(prodIdeal I J, V) := ⟨_, hmem⟩
  have ht' : (prodι I J).app V t' = a' • t := Subtype.ext rfl
  have h0 : (cokernel.π (prodι I J)).app V ((prodι I J).app V t') = 0 := by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, cokernel.condition]
    rfl
  rw [res_apply, Scheme.Modules.map_smul, ← ht, ← Scheme.Modules.Hom.app_smul, ← ht', h0]

end TwoPiece

/-- On a reduced scheme `Y = A ∪ B`, the vanishing ideals satisfy `I_B I_A = 0`. -/
theorem vanishingIdeal_mul_eq_bot {Y : Scheme.{u}} [IsReduced Y] {A B : Closeds Y}
    (hAB : A ⊔ B = ⊤) (U : Y.affineOpens) :
    (Scheme.IdealSheafData.vanishingIdeal B).ideal U *
      (Scheme.IdealSheafData.vanishingIdeal A).ideal U = ⊥ := by
  refine le_bot_iff.1 (Ideal.mul_le_inf.trans fun x hx => ?_)
  have hx' : x ∈ (Scheme.IdealSheafData.vanishingIdeal B ⊓
      Scheme.IdealSheafData.vanishingIdeal A).ideal U := hx
  rw [← Scheme.IdealSheafData.vanishingIdeal_sup, sup_comm, hAB,
    Scheme.IdealSheafData.vanishingIdeal_top] at hx'
  simp only [Scheme.nilradical, Scheme.IdealSheafData.radical_ideal,
    Scheme.IdealSheafData.ideal_bot, Pi.bot_apply] at hx'
  exact (Submodule.mem_bot _).2 (IsReduced.eq_zero x (mem_nilradical.1 hx'))

/-- The sheaf-theoretic input of the two-piece case of Hartshorne III, Ex. 3.2: for a
quasi-coherent ideal sheaf `J` on a reduced Noetherian `Y = A ∪ B`, the sequence
`0 ⟶ I_A J ⟶ J ⟶ J / I_A J ⟶ 0` has `I_A J` killed by `I_B` and `J / I_A J` killed by `I_A`,
so its outer terms are pushforwards from the reduced induced subschemes on `B` and `A`. -/
theorem twoPieceSequences : TwoPieceSequences.{u} := by
  intro Y _ _ A B hAB J
  have hQ₁ : ∀ (U : Y.affineOpens) (c : Γ(Y, U)),
      c ∈ (Scheme.IdealSheafData.vanishingIdeal B).ideal U →
        ∀ s : Γ(prodIdeal (Scheme.IdealSheafData.vanishingIdeal A) J, U), c • s = 0 :=
    fun U c hc s => Subtype.ext (smul_eq_zero_of_mem_powSmul_one _ _
      (vanishingIdeal_mul_eq_bot hAB) J.carrier c hc _
      (s : ArtinReesKernelSheaf.sub (ArtinReesKernelSheaf.powSmul _ 1 J.carrier) U).2)
  have hQ₃ : ∀ (U : Y.affineOpens) (c : Γ(Y, U)),
      c ∈ (Scheme.IdealSheafData.vanishingIdeal A).ideal U →
        ∀ s : Γ(cokernel (prodι (Scheme.IdealSheafData.vanishingIdeal A) J), U), c • s = 0 :=
    fun U c hc s => smul_eq_zero_cokernel_prodι _ J c hc s
  obtain ⟨G₁, hG₁, ⟨e₁⟩⟩ := ClosedDescent.exists_isQuasicoherent_iso_pushforward hQ₁
  obtain ⟨G₂, hG₂, ⟨e₂⟩⟩ := ClosedDescent.exists_isQuasicoherent_iso_pushforward hQ₃
  exact ⟨prodSC _ J, prodSC_shortExact _ J, Iso.refl _, G₁, G₂, hG₁, hG₂, ⟨e₁⟩, ⟨e₂⟩⟩

end ReducedComponentsAffine

/-- **Hartshorne III, Exercise 3.2.** A reduced Noetherian scheme is affine if and only if each of
its irreducible components, with its reduced induced structure, is affine. -/
theorem isAffine_iff_forall_irreducibleComponents_isAffine (X : Scheme.{u}) [IsReduced X]
    [IsNoetherian X] :
    IsAffine X ↔ ∀ (Z : Set X) (hZ : Z ∈ irreducibleComponents X),
      IsAffine (reducedInducedSubscheme ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩) :=
  ReducedComponentsAffine.isAffine_iff_of_twoPieceSequences
    ReducedComponentsAffine.twoPieceSequences X

end Hartshorne

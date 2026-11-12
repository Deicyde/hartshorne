/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.InfinitesimalNeighborhoods
import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# The formal completion as a locally ringed space

Hartshorne, *Algebraic Geometry*, II.9, definition of the formal completion (p. 194).

Let `I` be a quasi-coherent ideal subsheaf of `𝒪_X`, cutting out the closed subscheme
`Y = Y_1`, and let `Y_n` be the infinitesimal neighbourhoods cut out by `I ^ n`. All the `Y_n`
for `n ≥ 1` have the same support as `Y`: the inclusion `Y ⟶ Y_n` is a homeomorphism. Through it
the structure sheaf of `Y_n`, that is `(𝒪_X / I ^ n)|_Y`, becomes a sheaf of rings on `|Y|`.

* `Hartshorne.QuasicoherentIdealSubsheaf.formalCompletionDiagram I`: the inverse system
  `n ↦ 𝒪_{Y_(n+1)}` of sheaves of rings on `|Y|`, indexed from `0` (so it runs through
  Hartshorne's `n ≥ 1`), with transition maps restriction along `Y_(n+1) ⟶ Y_(n+2)`.
* `Hartshorne.QuasicoherentIdealSubsheaf.formalCompletionSheaf I`: its inverse limit, the sheaf
  `lim_(n ≥ 1) (𝒪_X / I ^ n)|_Y` of rings on `|Y|`, with no topology on the section rings.
* `Hartshorne.QuasicoherentIdealSubsheaf.isUnit_formalCompletionSheaf_iff`: a section is a unit
  if and only if its image in `𝒪_Y` is.
* `Hartshorne.QuasicoherentIdealSubsheaf.isLocalRing_stalk_formalCompletionSheaf`: every stalk
  is a local ring.
* `Hartshorne.QuasicoherentIdealSubsheaf.formalCompletion I`: the formal completion `X̂_Y` as a
  locally ringed space.

Hartshorne works over a Noetherian scheme `X`; the construction uses no finiteness, so it is made
for every scheme.
-/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Topology Opposite TopologicalSpace

namespace Hartshorne

universe u

/-- A section of `𝒪_B` over `U` is a unit as soon as its pullback along `f : A ⟶ B` to an open
`W` mapping onto `U` is a unit: the stalk maps of `f` are local. -/
lemma Scheme.Hom.isUnit_of_isUnit_appLE {A B : Scheme.{u}} (f : A ⟶ B) {U : B.Opens}
    {W : A.Opens} (e : W ≤ f ⁻¹ᵁ U) (hW : ∀ b ∈ U, ∃ a ∈ W, f a = b) (s : Γ(B, U))
    (hs : IsUnit (f.appLE U W e s)) : IsUnit s := by
  apply B.toRingedSpace.isUnit_of_isUnit_germ U s
  intro b hb
  obtain ⟨a, ha, rfl⟩ := hW b hb
  have h1 : IsUnit (A.presheaf.germ W a ha (f.appLE U W e s)) := hs.map _
  have h2 : A.presheaf.germ W a ha (f.appLE U W e s) =
      f.stalkMap a (B.presheaf.germ U (f a) hb s) := by
    rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appLE, CommRingCat.comp_apply,
      TopCat.Presheaf.germ_res_apply]
  rw [h2] at h1
  exact (isUnit_map_iff (f.stalkMap a).hom _).mp h1

/-- In a limit of commutative rings, an element is a unit as soon as all its projections are. -/
lemma isUnit_of_isLimit {J : Type} [SmallCategory J] {F : J ⥤ CommRingCat.{u}} {c : Cone F}
    (hc : IsLimit c) (s : c.pt) (h : ∀ j, IsUnit (c.π.app j s)) : IsUnit s := by
  have hc' := isLimitOfPreserves (forget CommRingCat.{u}) hc
  have hw : ∀ {j j'} (f : j ⟶ j'), F.map f (c.π.app j s) = c.π.app j' s := fun f => by
    rw [← CommRingCat.comp_apply, c.w f]
  let t : c.pt := (Types.isLimitEquivSections hc').symm
    ⟨fun j => (((h j).unit⁻¹ : (F.obj j)ˣ) : F.obj j), fun {j j'} f => by
      change F.map f _ = _
      apply Units.eq_inv_of_mul_eq_one_left
      rw [IsUnit.unit_spec, ← hw f, ← (h j).unit_spec, ← map_mul]
      simp⟩
  refine IsUnit.of_mul_eq_one t (Concrete.isLimit_ext F hc _ _ fun j => ?_)
  have ht : c.π.app j t = (((h j).unit⁻¹ : (F.obj j)ˣ) : F.obj j) :=
    Types.isLimitEquivSections_symm_apply hc' _ j
  rw [map_mul, map_one, ht]
  exact (h j).mul_val_inv

namespace QuasicoherentIdealSubsheaf

variable {X : Scheme.{u}} (I : QuasicoherentIdealSubsheaf X)

/-- The ideal data of `I ^ (n + 1)` is contained in that of `I ^ n`. -/
lemma quasicoherentIdealSubsheafEquiv_pow_succ_le (n : ℕ) :
    quasicoherentIdealSubsheafEquiv (I ^ (n + 1)) ≤ quasicoherentIdealSubsheafEquiv (I ^ n) := by
  rw [quasicoherentIdealSubsheafEquiv_pow, quasicoherentIdealSubsheafEquiv_pow]
  intro U
  simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply]
  exact Ideal.pow_le_pow_right (Nat.le_succ n)

/-- The ideal data of `I ^ (n + 1)` is contained in that of `I`. -/
lemma quasicoherentIdealSubsheafEquiv_pow_succ_le_one (n : ℕ) :
    quasicoherentIdealSubsheafEquiv (I ^ (n + 1)) ≤ quasicoherentIdealSubsheafEquiv (I ^ 1) := by
  rw [quasicoherentIdealSubsheafEquiv_pow, quasicoherentIdealSubsheafEquiv_pow]
  intro U
  simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply]
  exact Ideal.pow_le_pow_right (Nat.le_add_left 1 n)

/-- The closed immersion `Y_(n+1) ⟶ Y_(n+2)` between consecutive infinitesimal
neighbourhoods. -/
def infinitesimalNeighborhoodSucc (n : ℕ) :
    I.infinitesimalNeighborhood (n + 1) ⟶ I.infinitesimalNeighborhood (n + 2) :=
  Scheme.IdealSheafData.inclusion (I.quasicoherentIdealSubsheafEquiv_pow_succ_le (n + 1))

/-- The closed immersion `Y = Y_1 ⟶ Y_(n+1)`. -/
def infinitesimalNeighborhoodFromOne (n : ℕ) :
    I.infinitesimalNeighborhood 1 ⟶ I.infinitesimalNeighborhood (n + 1) :=
  Scheme.IdealSheafData.inclusion (I.quasicoherentIdealSubsheafEquiv_pow_succ_le_one n)

@[reassoc (attr := simp)]
lemma infinitesimalNeighborhoodFromOne_comp_succ (n : ℕ) :
    I.infinitesimalNeighborhoodFromOne n ≫ I.infinitesimalNeighborhoodSucc n =
      I.infinitesimalNeighborhoodFromOne (n + 1) :=
  Scheme.IdealSheafData.inclusion_comp _ _

@[reassoc (attr := simp)]
lemma infinitesimalNeighborhoodFromOne_comp_ι (n : ℕ) :
    I.infinitesimalNeighborhoodFromOne n ≫ I.infinitesimalNeighborhoodι (n + 1) =
      I.infinitesimalNeighborhoodι 1 :=
  Scheme.IdealSheafData.inclusion_subschemeι _

/-- `Y_(n+1)` has the same support as `Y`: the inclusion `Y ⟶ Y_(n+1)` is surjective. -/
lemma infinitesimalNeighborhoodFromOne_surjective (n : ℕ) :
    Function.Surjective (I.infinitesimalNeighborhoodFromOne n) := by
  intro z
  have hsupp : (quasicoherentIdealSubsheafEquiv (I ^ (n + 1))).support =
      (quasicoherentIdealSubsheafEquiv (I ^ 1)).support := by
    rw [quasicoherentIdealSubsheafEquiv_pow, quasicoherentIdealSubsheafEquiv_pow]
    rfl
  have hz : I.infinitesimalNeighborhoodι (n + 1) z ∈
      Set.range (I.infinitesimalNeighborhoodι 1) := by
    change _ ∈ Set.range (quasicoherentIdealSubsheafEquiv (I ^ 1)).subschemeι
    rw [Scheme.IdealSheafData.range_subschemeι, ← hsupp,
      ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨z, rfl⟩
  obtain ⟨y, hy⟩ := hz
  refine ⟨y, (I.infinitesimalNeighborhoodι (n + 1)).isClosedEmbedding.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, infinitesimalNeighborhoodFromOne_comp_ι, hy]

/-- The inclusion `Y ⟶ Y_(n+1)` is a homeomorphism, in particular an open embedding. -/
lemma isOpenEmbedding_infinitesimalNeighborhoodFromOne (n : ℕ) :
    IsOpenEmbedding (I.infinitesimalNeighborhoodFromOne n) := by
  have h1 : IsEmbedding (I.infinitesimalNeighborhoodι (n + 1) ∘
      I.infinitesimalNeighborhoodFromOne n) := by
    have h := (I.infinitesimalNeighborhoodι 1).isClosedEmbedding.isEmbedding
    convert h using 1
    funext y
    rw [Function.comp_apply, ← Scheme.Hom.comp_apply, infinitesimalNeighborhoodFromOne_comp_ι]
  refine ⟨(IsEmbedding.of_comp_iff
    (I.infinitesimalNeighborhoodι (n + 1)).isClosedEmbedding.isEmbedding).mp h1, ?_⟩
  rw [(I.infinitesimalNeighborhoodFromOne_surjective n).range_eq]
  exact isOpen_univ

/-- `𝒪_{Y_(n+1)}`, that is `(𝒪_X / I ^ (n + 1))|_Y`, as a sheaf of rings on `|Y|`, transported
along the homeomorphism `Y ⟶ Y_(n+1)`. -/
def formalCompletionSheafObj (n : ℕ) :
    TopCat.Sheaf CommRingCat.{u} (I.infinitesimalNeighborhood 1) where
  obj := (I.isOpenEmbedding_infinitesimalNeighborhoodFromOne n).functor.op ⋙
    (I.infinitesimalNeighborhood (n + 1)).presheaf
  property := TopCat.Presheaf.isSheaf_of_isOpenEmbedding
    (I.isOpenEmbedding_infinitesimalNeighborhoodFromOne n)
    (I.infinitesimalNeighborhood (n + 1)).IsSheaf

/-- The image of `V` in `Y_(n+1)` lies in the preimage of its image in `Y_(n+2)`. -/
lemma functor_obj_le_preimage_infinitesimalNeighborhoodSucc (n : ℕ)
    (V : Opens (I.infinitesimalNeighborhood 1)) :
    (I.isOpenEmbedding_infinitesimalNeighborhoodFromOne n).functor.obj V ≤
      I.infinitesimalNeighborhoodSucc n ⁻¹ᵁ
        (I.isOpenEmbedding_infinitesimalNeighborhoodFromOne (n + 1)).functor.obj V := by
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨y, hy, by rw [← Scheme.Hom.comp_apply, infinitesimalNeighborhoodFromOne_comp_succ]⟩

/-- The transition map `𝒪_{Y_(n+2)} ⟶ 𝒪_{Y_(n+1)}` on `|Y|`, restriction of sections along
`Y_(n+1) ⟶ Y_(n+2)`. -/
def formalCompletionSheafMap (n : ℕ) :
    I.formalCompletionSheafObj (n + 1) ⟶ I.formalCompletionSheafObj n where
  hom :=
    { app V := (I.infinitesimalNeighborhoodSucc n).appLE _ _
        (I.functor_obj_le_preimage_infinitesimalNeighborhoodSucc n V.unop)
      naturality V V' i := by
        change (I.infinitesimalNeighborhood (n + 2)).presheaf.map _ ≫
            (I.infinitesimalNeighborhoodSucc n).appLE _ _ _ =
          (I.infinitesimalNeighborhoodSucc n).appLE _ _ _ ≫
            (I.infinitesimalNeighborhood (n + 1)).presheaf.map _
        rw [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map] }

/-- The transition map is restriction of sections along `Y_(n+1) ⟶ Y_(n+2)`. -/
lemma formalCompletionSheafMap_hom_app (n : ℕ) (V : (Opens (I.infinitesimalNeighborhood 1))ᵒᵖ) :
    (I.formalCompletionSheafMap n).hom.app V = (I.infinitesimalNeighborhoodSucc n).appLE _ _
        (I.functor_obj_le_preimage_infinitesimalNeighborhoodSucc n V.unop) :=
  rfl

/-- **The inverse system of the formal completion**: `n ↦ 𝒪_{Y_(n+1)}`, the sheaves
`(𝒪_X / I ^ (n + 1))|_Y` of rings on `|Y|`, for `n ≥ 0`, that is Hartshorne's
`(𝒪_X / I ^ n)|_Y` for `n ≥ 1`. -/
def formalCompletionDiagram :
    ℕᵒᵖ ⥤ TopCat.Sheaf CommRingCat.{u} (I.infinitesimalNeighborhood 1) :=
  CategoryTheory.Functor.ofOpSequence I.formalCompletionSheafMap

/-- **The structure sheaf of the formal completion** (Hartshorne II.9, p. 194):
`𝒪_{X̂_Y} = lim_(n ≥ 1) (𝒪_X / I ^ n)|_Y`, an inverse limit of sheaves of rings on `|Y|`. -/
def formalCompletionSheaf : TopCat.Sheaf CommRingCat.{u} (I.infinitesimalNeighborhood 1) :=
  limit I.formalCompletionDiagram

/-- The transition maps reflect units: a section of `𝒪_{Y_(n+2)}` is a unit as soon as its
restriction to `Y_(n+1)` is. -/
lemma isUnit_of_isUnit_formalCompletionSheafMap (n : ℕ) (V : Opens (I.infinitesimalNeighborhood 1))
    (x : (I.formalCompletionSheafObj (n + 1)).presheaf.obj (op V))
    (hx : IsUnit ((I.formalCompletionSheafMap n).hom.app (op V) x)) : IsUnit x := by
  refine Scheme.Hom.isUnit_of_isUnit_appLE (I.infinitesimalNeighborhoodSucc n)
    (I.functor_obj_le_preimage_infinitesimalNeighborhoodSucc n V) ?_ x hx
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨_, ⟨y, hy, rfl⟩, by rw [← Scheme.Hom.comp_apply,
    infinitesimalNeighborhoodFromOne_comp_succ]⟩

/-- **Units of the formal completion.** A section of `𝒪_{X̂_Y}` is a unit if and only if its
image in `𝒪_Y = 𝒪_X / I` is a unit. -/
theorem isUnit_formalCompletionSheaf_iff (V : Opens (I.infinitesimalNeighborhood 1))
    (s : I.formalCompletionSheaf.presheaf.obj (op V)) :
    IsUnit s ↔ IsUnit ((limit.π I.formalCompletionDiagram (op 0)).hom.app (op V) s) := by
  refine ⟨fun hs => hs.map _, fun hs => ?_⟩
  have key : ∀ n : ℕ, IsUnit ((limit.π I.formalCompletionDiagram (op n)).hom.app (op V) s) := by
    intro n
    induction n with
    | zero => exact hs
    | succ n ih =>
      have hw := limit.w I.formalCompletionDiagram (homOfLE (Nat.le_add_right n 1)).op
      have hmap : I.formalCompletionDiagram.map (homOfLE (Nat.le_add_right n 1)).op =
          I.formalCompletionSheafMap n :=
        CategoryTheory.Functor.ofOpSequence_map_homOfLE_succ _ n
      rw [hmap] at hw
      have he : (limit.π I.formalCompletionDiagram (op n)).hom.app (op V) s =
          (I.formalCompletionSheafMap n).hom.app (op V)
            ((limit.π I.formalCompletionDiagram (op (n + 1))).hom.app (op V) s) := by
        rw [← hw]
        rfl
      rw [he] at ih
      exact I.isUnit_of_isUnit_formalCompletionSheafMap n V _ ih
  have hpres : PreservesLimitsOfShape ℕᵒᵖ (sheafToPresheaf
      (Opens.grothendieckTopology (I.infinitesimalNeighborhood 1 : TopCat)) CommRingCat.{u}) :=
    inferInstance
  obtain ⟨hlim⟩ := (hpres.preservesLimit (K := I.formalCompletionDiagram)).preserves
    (limit.isLimit I.formalCompletionDiagram)
  exact isUnit_of_isLimit (isLimitOfPreserves ((evaluation _ CommRingCat.{u}).obj (op V)) hlim)
    s fun n => key n.unop

/-- **The stalks of the formal completion are local rings** (Hartshorne II.9, p. 194). A germ is a
unit as soon as its image in the local ring `𝒪_{Y,y}` is: the non-units are the preimage of the
maximal ideal of `𝒪_{Y,y}`. -/
instance isLocalRing_stalk_formalCompletionSheaf (y : I.infinitesimalNeighborhood 1) :
    IsLocalRing (I.formalCompletionSheaf.presheaf.stalk y) := by
  let L := (I.infinitesimalNeighborhood 1).toLocallyRingedSpace.restrict
    (I.isOpenEmbedding_infinitesimalNeighborhoodFromOne 0)
  let π₀ := limit.π I.formalCompletionDiagram (op 0)
  let p : I.formalCompletionSheaf.presheaf.stalk y ⟶ L.presheaf.stalk y :=
    (TopCat.Presheaf.stalkFunctor CommRingCat y).map π₀.hom
  have : IsLocalHom p.hom := by
    refine ⟨fun a ha => ?_⟩
    obtain ⟨U, hyU, s, rfl⟩ := I.formalCompletionSheaf.presheaf.exists_germ_eq a
    have h1 : p (I.formalCompletionSheaf.presheaf.germ U y hyU s) =
        L.presheaf.germ U y hyU (π₀.hom.app (op U) s) :=
      TopCat.Presheaf.stalkFunctor_map_germ_apply U y hyU π₀.hom s
    rw [h1] at ha
    obtain ⟨V, i, hyV, hV⟩ := L.toRingedSpace.isUnit_res_of_isUnit_germ U _ y hyU ha
    have h2 : L.presheaf.map i.op (π₀.hom.app (op U) s) =
        π₀.hom.app (op V) (I.formalCompletionSheaf.presheaf.map i.op s) :=
      (NatTrans.naturality_apply π₀.hom i.op s).symm
    rw [h2] at hV
    replace hV := (I.isUnit_formalCompletionSheaf_iff V _).mpr hV
    have h3 := TopCat.Presheaf.germ_res_apply I.formalCompletionSheaf.presheaf i y hyV s
    have h4 : IsUnit (I.formalCompletionSheaf.presheaf.germ V y hyV
        (I.formalCompletionSheaf.presheaf.map i.op s)) := hV.map _
    exact (congrArg IsUnit h3).mp h4
  have := L.isLocalRing y
  exact p.hom.domain_isLocalRing

/-- **The formal completion** `X̂_Y` of `X` along the closed subscheme `Y` cut out by `I`
(Hartshorne II.9, p. 194): the locally ringed space with underlying space `|Y|` and structure
sheaf `lim_(n ≥ 1) (𝒪_X / I ^ n)|_Y`. -/
def formalCompletion : LocallyRingedSpace.{u} where
  carrier := (I.infinitesimalNeighborhood 1).toTopCat
  presheaf := I.formalCompletionSheaf.presheaf
  IsSheaf := I.formalCompletionSheaf.property
  isLocalRing := I.isLocalRing_stalk_formalCompletionSheaf

/-- The underlying space of the formal completion is `|Y|`. -/
lemma formalCompletion_carrier :
    I.formalCompletion.carrier = (I.infinitesimalNeighborhood 1).toTopCat :=
  rfl

/-- The structure sheaf of the formal completion is `lim_(n ≥ 1) (𝒪_X / I ^ n)|_Y`. -/
lemma formalCompletion_presheaf :
    I.formalCompletion.presheaf = I.formalCompletionSheaf.presheaf :=
  rfl

end QuasicoherentIdealSubsheaf

end Hartshorne

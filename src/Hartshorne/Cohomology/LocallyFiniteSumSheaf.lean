/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ConstantSheaf
import Hartshorne.Scheme.ClosedExtensionByZero
import Mathlib.Topology.Sheaves.LocalPredicate
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Compactness.LocallyFinite

/-!
# Direct sums of skyscraper sheaves

Supporting construction for Hartshorne, *Algebraic Geometry*, II.1, Exercise 1.21(d)
(p. 68), adopted for III, Exercise 2.2 (p. 212).

For a family of abelian groups `A x` indexed by the points of a space `X`, the sections of
`⨁_{P ∈ X} i_{P,*}(A_P)` over an open set `U` are the families `(s_x)_{x ∈ U}` with `s_x ∈ A_x`
whose support is locally finite. Locally finite support is a local condition, so these families
form a sheaf of abelian groups for every space; on a Noetherian space every open set is compact
and locally finite support means finite support, so the sections over `U` are
`⨁_{P ∈ U} A_P`.

Here `i_{P,*}(A)` is the direct image, along the inclusion of the subspace `{P}`, of the constant
sheaf `A` on that one-point space. The point inclusions into the locally finite sum form a cofan,
and on a Noetherian space this cofan is a coproduct in the category of sheaves of abelian groups:
a family of morphisms out of the skyscrapers is summed over the finite support of a section.

## Main definitions

* `Hartshorne.locallyFiniteSumSheaf`: the sheaf of locally finitely supported families.
* `Hartshorne.pointSheaf`: the skyscraper `i_{P,*}(A)`.
* `Hartshorne.pointToLocallyFiniteSum`: the inclusion of the `P`-th summand.

## Main results

* `Hartshorne.isColimitLocallyFiniteSumCofan`: on a Noetherian space the locally finite sum is
  the coproduct of the skyscrapers.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace Hartshorne

open scoped Classical

universe u

variable {X : TopCat.{u}} (A : X → AddCommGrpCat.{u})

/-- Local finiteness of the support of a family of elements `s_x ∈ A_x`, `x ∈ U`: every point of
`U` has an open neighbourhood containing only finitely many points of the support. -/
def LocallyFiniteSupport {U : Opens X} (f : ∀ x : U, A x) : Prop :=
  ∀ x : U, ∃ V : Opens X, x.1 ∈ V ∧ {y : U | y.1 ∈ V ∧ f y ≠ 0}.Finite

/-- Locally finite support, as a local predicate. -/
def locallyFiniteSupportLocalPredicate :
    TopCat.LocalPredicate (fun x : X => (A x : Type u)) where
  pred {U} f := LocallyFiniteSupport (U := U) A f
  res {U V} i f hf := by
    intro x
    obtain ⟨W, hxW, hW⟩ := hf ⟨x.1, i.le x.2⟩
    refine ⟨W, hxW, ?_⟩
    refine (hW.preimage (f := fun y : U => (⟨y.1, i.le y.2⟩ : V)) ?_).subset ?_
    · intro a _ b _ hab
      exact Subtype.ext (congrArg (fun z : V => z.1) hab)
    · intro y hy
      exact hy
  locality {U} f hf := by
    intro x
    obtain ⟨V, hxV, i, hV⟩ := hf x
    obtain ⟨W, hxW, hW⟩ := hV ⟨x.1, hxV⟩
    refine ⟨V ⊓ W, ⟨hxV, hxW⟩, ?_⟩
    refine (hW.image (fun y : V => (⟨y.1, i.le y.2⟩ : U))).subset ?_
    rintro y ⟨⟨hyV, hyW⟩, hy⟩
    exact ⟨⟨y.1, hyV⟩, ⟨hyW, hy⟩, rfl⟩

/-- The families over `U` with locally finite support form a subgroup of all families. -/
def locallyFiniteSections (U : Opens X) : AddSubgroup (∀ x : U, A x) where
  carrier := {f | LocallyFiniteSupport A f}
  zero_mem' := fun _ => ⟨⊤, trivial, by simp⟩
  add_mem' {f g} hf hg := by
    intro x
    obtain ⟨V, hxV, hV⟩ := hf x
    obtain ⟨W, hxW, hW⟩ := hg x
    refine ⟨V ⊓ W, ⟨hxV, hxW⟩, (hV.union hW).subset ?_⟩
    rintro y ⟨⟨hyV, hyW⟩, hy⟩
    by_contra hc
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_and, not_not] at hc
    exact hy (by simp [hc.1 hyV, hc.2 hyW])
  neg_mem' {f} hf := by
    intro x
    obtain ⟨V, hxV, hV⟩ := hf x
    exact ⟨V, hxV, by simpa using hV⟩

/-- The presheaf of locally finitely supported families. -/
def locallyFiniteSumPresheaf : X.Presheaf AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of (locallyFiniteSections A U.unop)
  map i := AddCommGrpCat.ofHom
    { toFun := fun f => ⟨fun x => f.1 (i.unop x),
        (locallyFiniteSupportLocalPredicate A).res i.unop f.1 f.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

theorem locallyFiniteSumPresheaf_comp_forget :
    locallyFiniteSumPresheaf A ⋙ forget AddCommGrpCat =
      TopCat.subpresheafToTypes (locallyFiniteSupportLocalPredicate A).toPrelocalPredicate :=
  rfl

/-- **The locally finite sum of the skyscrapers**: sections over `U` are the families
`(s_x)_{x ∈ U}`, `s_x ∈ A_x`, with locally finite support. On a Noetherian space this is the direct
sum `⨁_{P} i_{P,*}(A_P)` (`isColimitLocallyFiniteSumCofan`). -/
def locallyFiniteSumSheaf : X.Sheaf AddCommGrpCat.{u} := by
  refine ⟨locallyFiniteSumPresheaf A, ?_⟩
  apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp' (forget AddCommGrpCat)
    (locallyFiniteSumPresheaf A)).mpr
  rw [locallyFiniteSumPresheaf_comp_forget A]
  exact TopCat.subpresheafToTypes.isSheaf (locallyFiniteSupportLocalPredicate A)


/-- The skyscraper sheaf `i_{P,*}(B)`: the direct image, along the inclusion of the subspace
`{P}`, of the constant sheaf `B` on that one-point space. -/
def pointSheaf (P : X) (B : AddCommGrpCat.{u}) : X.Sheaf AddCommGrpCat.{u} :=
  (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (closedSubspaceInclusion X {P})).obj
    (constantSheaf (TopCat.of ({P} : Set X)) B)

/-- The point `P` of the preimage of an open set containing `P`. -/
def pointSheafPoint {P : X} {U : Opens X} (hPU : P ∈ U) :
    (Opens.map (closedSubspaceInclusion X {P})).obj U :=
  ⟨⟨P, Set.mem_singleton P⟩, hPU⟩

/-- A section of `i_{P,*}(B)` over `U` is a locally constant function on `{P} ∩ U`. -/
theorem pointSheaf_obj (P : X) (B : AddCommGrpCat.{u}) (U : Opens X) :
    (pointSheaf P B).presheaf.obj (op U) =
      AddCommGrpCat.of (LocallyConstant ((Opens.map (closedSubspaceInclusion X {P})).obj U) B) :=
  rfl


/-- The family over `U` with value `a` at `P` and zero elsewhere. -/
def pointFamily (P : X) (U : Opens X) (a : A P) : ∀ x : U, A x :=
  fun x => if h : x.1 = P then cast (congrArg (fun y => (A y : Type u)) h.symm) a else 0

theorem pointFamily_self (P : X) (U : Opens X) (hPU : P ∈ U) (a : A P) :
    pointFamily A P U a ⟨P, hPU⟩ = a := by
  simp [pointFamily]

theorem pointFamily_of_ne (P : X) (U : Opens X) (a : A P) (x : U) (hx : x.1 ≠ P) :
    pointFamily A P U a x = 0 := by
  simp only [pointFamily, dif_neg hx]

theorem pointFamily_add (P : X) (U : Opens X) (a b : A P) :
    pointFamily A P U (a + b) = pointFamily A P U a + pointFamily A P U b := by
  funext x
  obtain ⟨x, hx⟩ := x
  by_cases h : x = P
  · subst h
    simp [pointFamily]
  · simp [pointFamily, h]

theorem pointFamily_zero (P : X) (U : Opens X) : pointFamily A P U 0 = 0 := by
  funext x
  obtain ⟨x, hx⟩ := x
  by_cases h : x = P
  · subst h
    simp [pointFamily]
  · simp [pointFamily, h]

theorem locallyFiniteSupport_pointFamily (P : X) (U : Opens X) (a : A P) :
    LocallyFiniteSupport A (pointFamily A P U a) := by
  intro x
  refine ⟨⊤, trivial, Set.Subsingleton.finite ?_⟩
  intro y hy z hz
  have hy' : y.1 = P := by
    by_contra h
    exact hy.2 (pointFamily_of_ne A P U a y h)
  have hz' : z.1 = P := by
    by_contra h
    exact hz.2 (pointFamily_of_ne A P U a z h)
  exact Subtype.ext (hy'.trans hz'.symm)

/-- The value at `P` of a section of `i_{P,*}(B)` over an open set containing `P`; zero if the
open set misses `P`. -/
def pointSheafValue (P : X) {B : AddCommGrpCat.{u}} (U : Opens X)
    (s : LocallyConstant ((Opens.map (closedSubspaceInclusion X {P})).obj U) B) : B :=
  if hPU : P ∈ U then s (pointSheafPoint hPU) else 0

/-- **The inclusion of the `P`-th summand** `i_{P,*}(A_P) → ⨁_{Q} i_{Q,*}(A_Q)`. -/
def pointToLocallyFiniteSum (P : X) : pointSheaf P (A P) ⟶ locallyFiniteSumSheaf A :=
  ObjectProperty.homMk
    { app U := AddCommGrpCat.ofHom
        { toFun := fun s => ⟨pointFamily A P U.unop (pointSheafValue P U.unop s),
            locallyFiniteSupport_pointFamily A P U.unop _⟩
          map_zero' := by
            apply Subtype.ext
            change pointFamily A P U.unop (pointSheafValue P U.unop 0) = 0
            simp only [pointSheafValue, LocallyConstant.coe_zero, Pi.zero_apply, dite_eq_ite,
              ite_self]
            exact pointFamily_zero A P U.unop
          map_add' := fun s t => by
            apply Subtype.ext
            change pointFamily A P U.unop (pointSheafValue P U.unop (s + t)) =
              pointFamily A P U.unop (pointSheafValue P U.unop s) +
                pointFamily A P U.unop (pointSheafValue P U.unop t)
            rw [← pointFamily_add]
            congr 1
            unfold pointSheafValue
            split_ifs <;> simp }
      naturality := fun U V i => by
        ext s
        apply Subtype.ext
        funext x
        obtain ⟨x, hx⟩ := x
        by_cases h : x = P
        · subst h
          change pointFamily A x V.unop (pointSheafValue x V.unop _) ⟨x, hx⟩ =
            pointFamily A x U.unop (pointSheafValue x U.unop s) ⟨x, i.unop.le hx⟩
          rw [pointFamily_self, pointFamily_self]
          simp only [pointSheafValue, dif_pos hx, dif_pos (i.unop.le hx)]
          rfl
        · change pointFamily A P V.unop _ ⟨x, hx⟩ =
            pointFamily A P U.unop _ ⟨x, i.unop.le hx⟩
          rw [pointFamily_of_ne A P _ _ _ h, pointFamily_of_ne A P _ _ _ h] }


/-- The cofan of summand inclusions into the locally finite sum. -/
def locallyFiniteSumCofan : Cofan (fun P : X => pointSheaf P (A P)) :=
  Cofan.mk (locallyFiniteSumSheaf A) (pointToLocallyFiniteSum A)

section Noetherian

variable [NoetherianSpace X]

/-- On a Noetherian space a locally finite support is finite, since every open set is
compact. -/
theorem LocallyFiniteSupport.finite {U : Opens X} {f : ∀ x : U, A x}
    (hf : LocallyFiniteSupport A f) : {x : U | f x ≠ 0}.Finite := by
  have : CompactSpace U :=
    isCompact_iff_compactSpace.mp (NoetherianSpace.isCompact (U : Set X))
  let g : {x : U // f x ≠ 0} → Set U := fun y => {y.1}
  have hg : LocallyFinite g := by
    intro x
    obtain ⟨V, hxV, hV⟩ := hf x
    refine ⟨Subtype.val ⁻¹' (V : Set X),
      (V.isOpen.preimage continuous_subtype_val).mem_nhds hxV, ?_⟩
    refine (hV.preimage (f := fun y : {x : U // f x ≠ 0} => y.1)
      (fun a _ b _ hab => Subtype.ext hab)).subset ?_
    rintro y ⟨z, hz, hzV⟩
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨hzV, y.2⟩
  have hfin := hg.finite_nonempty_of_compact
  have huniv : {i | (g i).Nonempty} = Set.univ :=
    Set.eq_univ_of_forall fun i => Set.singleton_nonempty _
  rw [huniv, Set.finite_univ_iff] at hfin
  exact Set.finite_coe_iff.mp hfin

/-- The finite support of a section of the locally finite sum. -/
def locallyFiniteSectionSupport {U : Opens X} (s : locallyFiniteSections A U) : Finset U :=
  (LocallyFiniteSupport.finite A s.2).toFinset

theorem mem_locallyFiniteSectionSupport {U : Opens X} (s : locallyFiniteSections A U) (x : U) :
    x ∈ locallyFiniteSectionSupport A s ↔ s.1 x ≠ 0 := by
  simp [locallyFiniteSectionSupport]

variable {A}

/-- The `x`-th component of the morphism out of the sum determined by a cofan. -/
def locallyFiniteSumTerm (t : Cofan (fun P : X => pointSheaf P (A P))) (U : Opens X) (x : U) :
    A x →+ t.pt.presheaf.obj (op U) :=
  ((t.inj x.1).hom.app (op U)).hom.comp (LocallyConstant.constAddMonoidHom)

/-- The sum, over the support, of the components determined by a cofan. -/
def locallyFiniteSumSum (t : Cofan (fun P : X => pointSheaf P (A P))) (U : Opens X)
    (s : locallyFiniteSections A U) : t.pt.presheaf.obj (op U) :=
  ∑ x ∈ locallyFiniteSectionSupport A s, locallyFiniteSumTerm t U x (s.1 x)

theorem locallyFiniteSumSum_eq (t : Cofan (fun P : X => pointSheaf P (A P))) (U : Opens X)
    (s : locallyFiniteSections A U) (S : Finset U) (hS : ∀ x, s.1 x ≠ 0 → x ∈ S) :
    locallyFiniteSumSum t U s = ∑ x ∈ S, locallyFiniteSumTerm t U x (s.1 x) := by
  refine Finset.sum_subset (fun x hx => hS x ((mem_locallyFiniteSectionSupport A s x).1 hx)) ?_
  intro x _ hx
  rw [mem_locallyFiniteSectionSupport, not_not] at hx
  rw [hx, map_zero]

omit [NoetherianSpace X] in
/-- A component vanishes on an open set missing its point. -/
theorem locallyFiniteSumTerm_eq_zero (t : Cofan (fun P : X => pointSheaf P (A P))) (U : Opens X)
    (P : X) (hP : P ∉ U) (a : A P) :
    ((t.inj P).hom.app (op U)) (LocallyConstant.const _ a) = 0 := by
  have hempty : IsEmpty ((Opens.map (closedSubspaceInclusion X {P})).obj U) := by
    refine ⟨fun z => hP ?_⟩
    have hz := z.2
    have hzP : z.1.1 = P := z.1.2
    change z.1.1 ∈ U at hz
    rwa [hzP] at hz
  have hc : (LocallyConstant.const ((Opens.map (closedSubspaceInclusion X {P})).obj U) a) = 0 :=
    LocallyConstant.ext fun z => isEmptyElim z
  calc ((t.inj P).hom.app (op U)) (LocallyConstant.const _ a)
      = ((t.inj P).hom.app (op U)) 0 := congrArg _ hc
    _ = 0 := map_zero _

/-- Restriction of a locally finitely supported family to a smaller open set. -/
def restrictLocallyFiniteSections {U V : Opens X} (h : V ≤ U) (s : locallyFiniteSections A U) :
    locallyFiniteSections A V :=
  ⟨fun x => s.1 ⟨x.1, h x.2⟩, (locallyFiniteSupportLocalPredicate A).res (homOfLE h) s.1 s.2⟩

/-- The sum determined by a cofan commutes with restriction. -/
theorem locallyFiniteSumSum_restrict (t : Cofan (fun P : X => pointSheaf P (A P))) {U V : Opens X}
    (h : V ≤ U) (s : locallyFiniteSections A U) :
    t.pt.presheaf.map (homOfLE h).op (locallyFiniteSumSum t U s) =
      locallyFiniteSumSum t V (restrictLocallyFiniteSections h s) := by
  have hinj : Set.InjOn (fun y : V => (⟨y.1, h y.2⟩ : U))
      ((fun y : V => (⟨y.1, h y.2⟩ : U)) ⁻¹' ↑(locallyFiniteSectionSupport A s)) :=
    fun a _ b _ hab => Subtype.ext (congrArg (fun z : U => z.1) hab)
  rw [locallyFiniteSumSum_eq t V _ ((locallyFiniteSectionSupport A s).preimage _ hinj)]
  · rw [locallyFiniteSumSum, map_sum]
    symm
    refine (Finset.sum_preimage (fun y : V => (⟨y.1, h y.2⟩ : U))
      (locallyFiniteSectionSupport A s) hinj
      (fun x => ((t.inj x.1).hom.app (op V)) (LocallyConstant.const _ (s.1 x))) ?_).trans ?_
    · intro x _ hx
      apply locallyFiniteSumTerm_eq_zero
      intro hxV
      exact hx ⟨⟨x.1, hxV⟩, rfl⟩
    · refine Finset.sum_congr rfl fun x _ => ?_
      change _ = ((t.inj x.1).hom.app (op U) ≫ t.pt.presheaf.map (homOfLE h).op) _
      rw [← (t.inj x.1).hom.naturality]
      rfl
  · intro x hx
    rw [Finset.mem_preimage, mem_locallyFiniteSectionSupport]
    exact hx

/-- The morphism out of the locally finite sum determined by a cofan. -/
def locallyFiniteSumDesc (t : Cofan (fun P : X => pointSheaf P (A P))) :
    locallyFiniteSumSheaf A ⟶ t.pt :=
  ObjectProperty.homMk
    { app U := AddCommGrpCat.ofHom
        { toFun := locallyFiniteSumSum t U.unop
          map_zero' := by
            rw [locallyFiniteSumSum_eq t U.unop 0 ∅ (fun x hx => (hx rfl).elim)]
            rfl
          map_add' := fun s s' => by
            let S := locallyFiniteSectionSupport A s ∪ locallyFiniteSectionSupport A s'
            have hS : ∀ x, s.1 x ≠ 0 → x ∈ S := fun x hx =>
              Finset.mem_union_left _ ((mem_locallyFiniteSectionSupport A s x).2 hx)
            have hS' : ∀ x, s'.1 x ≠ 0 → x ∈ S := fun x hx =>
              Finset.mem_union_right _ ((mem_locallyFiniteSectionSupport A s' x).2 hx)
            have hSS : ∀ x, (s + s').1 x ≠ 0 → x ∈ S := by
              intro x hx
              by_contra hxS
              apply hx
              have h1 : s.1 x = 0 := by
                by_contra h
                exact hxS (hS x h)
              have h2 : s'.1 x = 0 := by
                by_contra h
                exact hxS (hS' x h)
              change s.1 x + s'.1 x = 0
              rw [h1, h2, add_zero]
            rw [locallyFiniteSumSum_eq t U.unop s S hS, locallyFiniteSumSum_eq t U.unop s' S hS',
              locallyFiniteSumSum_eq t U.unop (s + s') S hSS, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [← map_add]
            rfl }
      naturality := fun U V i => by
        ext s
        exact (locallyFiniteSumSum_restrict t i.unop.le s).symm }

omit [NoetherianSpace X] in
/-- A section of `i_{P,*}(B)` over an open set containing `P` is constant. -/
theorem pointSheaf_section_eq_const {P : X} {B : AddCommGrpCat.{u}} {U : Opens X} (hPU : P ∈ U)
    (s : LocallyConstant ((Opens.map (closedSubspaceInclusion X {P})).obj U) B) :
    s = LocallyConstant.const _ (s (pointSheafPoint hPU)) := by
  ext z
  change s z = s (pointSheafPoint hPU)
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  exact z.1.2

omit [NoetherianSpace X] in
/-- A section of `i_{P,*}(B)` over an open set missing `P` is zero. -/
theorem pointSheaf_section_eq_zero {P : X} {B : AddCommGrpCat.{u}} {U : Opens X} (hPU : P ∉ U)
    (s : LocallyConstant ((Opens.map (closedSubspaceInclusion X {P})).obj U) B) : s = 0 := by
  ext z
  refine (hPU ?_).elim
  have hz := z.2
  have hzP : z.1.1 = P := z.1.2
  change z.1.1 ∈ U at hz
  rwa [hzP] at hz

theorem locallyFiniteSumDesc_fac (t : Cofan (fun P : X => pointSheaf P (A P))) (P : X) :
    pointToLocallyFiniteSum A P ≫ locallyFiniteSumDesc t = t.inj P := by
  apply ObjectProperty.hom_ext
  ext U s
  change locallyFiniteSumSum t U.unop ⟨pointFamily A P U.unop (pointSheafValue P U.unop s), _⟩ =
    (t.inj P).hom.app U s
  by_cases hPU : P ∈ U.unop
  · rw [locallyFiniteSumSum_eq t U.unop _ {⟨P, hPU⟩}, Finset.sum_singleton]
    · change ((t.inj P).hom.app U) (LocallyConstant.const _
        (pointFamily A P U.unop (pointSheafValue P U.unop s) ⟨P, hPU⟩)) = _
      rw [pointFamily_self]
      simp only [pointSheafValue, dif_pos hPU]
      exact congrArg _ (pointSheaf_section_eq_const hPU s).symm
    · intro x hx
      rw [Finset.mem_singleton]
      by_contra hxP
      apply hx
      apply pointFamily_of_ne
      intro h
      exact hxP (Subtype.ext h)
  · rw [locallyFiniteSumSum_eq t U.unop _ ∅, Finset.sum_empty, pointSheaf_section_eq_zero hPU s]
    · exact (map_zero _).symm
    intro x hx
    exfalso
    apply hx
    apply pointFamily_of_ne
    intro h
    exact hPU (h ▸ x.2)

/-- A locally finitely supported family is the sum of its components over its support. -/
theorem locallyFiniteSection_eq_sum (U : Opens X) (s : locallyFiniteSections A U) :
    s = ∑ x ∈ locallyFiniteSectionSupport A s, (⟨pointFamily A x.1 U (s.1 x),
      locallyFiniteSupport_pointFamily A x.1 U _⟩ : locallyFiniteSections A U) := by
  apply Subtype.ext
  funext y
  rw [AddSubgroup.val_finsetSum, Finset.sum_apply]
  by_cases hy : s.1 y = 0
  · rw [hy]
    refine (Finset.sum_eq_zero fun x hx => ?_).symm
    apply pointFamily_of_ne
    intro h
    apply (mem_locallyFiniteSectionSupport A s x).1 hx
    have hxy : x = y := Subtype.ext h.symm
    rw [hxy, hy]
  · rw [Finset.sum_eq_single y]
    · exact (pointFamily_self A y.1 U y.2 _).symm
    · intro x _ hxy
      apply pointFamily_of_ne
      intro h
      exact hxy (Subtype.ext h.symm)
    · intro hy'
      exact (hy' ((mem_locallyFiniteSectionSupport A s y).2 hy)).elim

theorem locallyFiniteSumDesc_uniq (t : Cofan (fun P : X => pointSheaf P (A P)))
    (m : locallyFiniteSumSheaf A ⟶ t.pt)
    (hm : ∀ P : X, pointToLocallyFiniteSum A P ≫ m = t.inj P) :
    m = locallyFiniteSumDesc t := by
  apply ObjectProperty.hom_ext
  ext U s
  change m.hom.app U s = locallyFiniteSumSum t U.unop s
  have key : ∀ x : U.unop,
      (pointToLocallyFiniteSum A x.1).hom.app U (LocallyConstant.const _ (s.1 x)) =
        (⟨pointFamily A x.1 U.unop (s.1 x), locallyFiniteSupport_pointFamily A x.1 U.unop _⟩ :
          locallyFiniteSections A U.unop) := by
    intro x
    apply Subtype.ext
    change pointFamily A x.1 U.unop (pointSheafValue x.1 U.unop _) = _
    simp only [pointSheafValue, dif_pos x.2]
    rfl
  calc m.hom.app U s
      = m.hom.app U (∑ x ∈ locallyFiniteSectionSupport A s, (⟨pointFamily A x.1 U.unop (s.1 x),
          locallyFiniteSupport_pointFamily A x.1 U.unop _⟩ : locallyFiniteSections A U.unop)) :=
        congrArg _ (locallyFiniteSection_eq_sum U.unop s)
    _ = ∑ x ∈ locallyFiniteSectionSupport A s, m.hom.app U (⟨pointFamily A x.1 U.unop (s.1 x),
          locallyFiniteSupport_pointFamily A x.1 U.unop _⟩ : locallyFiniteSections A U.unop) :=
        map_sum _ _ _
    _ = ∑ x ∈ locallyFiniteSectionSupport A s, locallyFiniteSumTerm t U.unop x (s.1 x) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← key x]
        change ((pointToLocallyFiniteSum A x.1 ≫ m).hom.app U) _ = _
        rw [hm]
        rfl
    _ = locallyFiniteSumSum t U.unop s := rfl

/-- **On a Noetherian space, the locally finite sum is the coproduct** `⨁_{P} i_{P,*}(A_P)` of the
skyscraper sheaves in the category of sheaves of abelian groups, with the summand inclusions as
coprojections. -/
def isColimitLocallyFiniteSumCofan : IsColimit (locallyFiniteSumCofan A) :=
  Cofan.IsColimit.mk _ locallyFiniteSumDesc locallyFiniteSumDesc_fac locallyFiniteSumDesc_uniq

end Noetherian

end Hartshorne

/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.InverseSystemMittagLefflerStableImage

/-!
# Exact inverse limits under the Mittag--Leffler condition

Hartshorne, *Algebraic Geometry*, II.9, Proposition 9.1(b) (p. 192).

A levelwise short exact sequence of sequential inverse systems remains exact on inverse limits
when the kernel system satisfies the Mittag--Leffler condition. Inverse limits are represented
concretely by compatible sections of the underlying Type-valued functors.
-/

noncomputable section

open CategoryTheory Set

namespace Hartshorne.InverseSystem

universe u

private abbrev underlying (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) : ℕᵒᵖ ⥤ Type u :=
  A ⋙ forget AddCommGrpCat

private def transition {n m : ℕ} (h : n ≤ m) :
    (Opposite.op m : ℕᵒᵖ) ⟶ Opposite.op n :=
  (homOfLE h).op

private def succTransition (n : ℕ) :
    (Opposite.op (n + 1) : ℕᵒᵖ) ⟶ Opposite.op n :=
  transition (Nat.le_succ n)

/-- A sequential inverse system of nonempty types with surjective transition maps has a
compatible section. -/
private lemma nonempty_sections_of_surjective
    (F : ℕᵒᵖ ⥤ Type u)
    (hne : ∀ n, Nonempty (F.obj (Opposite.op n)))
    (hsur : ∀ ⦃i j⦄ (f : i ⟶ j), Function.Surjective (F.map f)) :
    Nonempty F.sections := by
  let x : ∀ n : ℕ, F.obj (Opposite.op n) := fun n =>
    Nat.rec (Classical.choice (hne 0))
      (fun m xm => Classical.choose (hsur (succTransition m) xm)) n
  have hx (n : ℕ) : F.map (succTransition n) (x (n + 1)) = x n := by
    dsimp [x]
    exact Classical.choose_spec (hsur (succTransition n) _)
  have compat : ∀ (m n : ℕ) (h : n ≤ m),
      F.map (transition h) (x m) = x n := by
    intro m
    induction m with
    | zero =>
        intro n h
        have hn : n = 0 := Nat.eq_zero_of_le_zero h
        subst n
        rw [show transition h = 𝟙 _ from Subsingleton.elim _ _, F.map_id]
        rfl
    | succ m ih =>
        intro n h
        rcases Nat.eq_or_lt_of_le h with rfl | hlt
        · rw [show transition h = 𝟙 _ from Subsingleton.elim _ _, F.map_id]
          rfl
        · have hnm : n ≤ m := Nat.le_of_lt_succ hlt
          let p : (Opposite.op (m + 1) : ℕᵒᵖ) ⟶ Opposite.op m := succTransition m
          let q : (Opposite.op m : ℕᵒᵖ) ⟶ Opposite.op n := transition hnm
          have hpq : transition h = p ≫ q := Subsingleton.elim _ _
          rw [hpq, F.map_comp]
          change F.map q (F.map p (x (m + 1))) = x n
          rw [show F.map p (x (m + 1)) = x m from hx m]
          exact ih n hnm
  refine ⟨⟨fun j => x j.unop, ?_⟩⟩
  intro i j f
  let h : j.unop ≤ i.unop := leOfHom f.unop
  have hf : f = transition h := Subsingleton.elim _ _
  rw [hf]
  exact compat i.unop j.unop h

/-- A nonempty sequential Mittag--Leffler system of types has a compatible section. -/
private lemma nonempty_sections_of_mittagLeffler
    (F : ℕᵒᵖ ⥤ Type u) (hF : F.IsMittagLeffler)
    (hne : ∀ n, Nonempty (F.obj (Opposite.op n))) : Nonempty F.sections := by
  let _ : ∀ j, Nonempty (F.obj j) := fun j => hne j.unop
  let E := F.toEventualRanges
  have hneE : ∀ n, Nonempty (E.obj (Opposite.op n)) := fun n =>
    F.toEventualRanges_nonempty hF (Opposite.op n)
  obtain ⟨s⟩ := nonempty_sections_of_surjective E hneE
    (fun {i j} f => F.surjective_toEventualRanges hF (i := i) (j := j) f)
  exact ⟨F.toEventualRangesSectionsEquiv s⟩

/-- A natural transformation of inverse systems induces an additive map on compatible
sections. -/
def sectionsMap {A B : ℕᵒᵖ ⥤ AddCommGrpCat.{u}} (f : A ⟶ B) :
    (A ⋙ forget AddCommGrpCat).sections →+
      (B ⋙ forget AddCommGrpCat).sections where
  toFun s := ⟨fun j => f.app j (s.1 j), by
    intro i j p
    change B.map p (f.app i (s.1 i)) = f.app j (s.1 j)
    rw [← NatTrans.naturality_apply]
    have hs := s.2 p
    change A.map p (s.1 i) = s.1 j at hs
    rw [hs]⟩
  map_zero' := by
    apply Subtype.ext
    funext j
    exact (f.app j).hom.map_zero
  map_add' x y := by
    apply Subtype.ext
    funext j
    exact (f.app j).hom.map_add _ _

private def fiberSystem {B C : ℕᵒᵖ ⥤ AddCommGrpCat.{u}} (g : B ⟶ C)
    (c : (underlying C).sections) : ℕᵒᵖ ⥤ Type u where
  obj j := { b : B.obj j // g.app j b = c.1 j }
  map {i j} p := ↾ fun b => ⟨B.map p b.1, by
    rw [← AddCommGrpCat.comp_apply, g.naturality p, AddCommGrpCat.comp_apply, b.2]
    have hc := c.2 p
    change C.map p (c.1 i) = c.1 j at hc
    rw [hc]⟩
  map_id j := by
    ext b
    change B.map (𝟙 j) b.1 = b.1
    simp
  map_comp p q := by
    ext b
    change B.map (p ≫ q) b.1 = B.map q (B.map p b.1)
    rw [B.map_comp]
    rfl

private lemma fiberSystem_nonempty {B C : ℕᵒᵖ ⥤ AddCommGrpCat.{u}} (g : B ⟶ C)
    (hg : ∀ j, Function.Surjective (g.app j)) (c : (underlying C).sections) (n : ℕ) :
    Nonempty ((fiberSystem g c).obj (Opposite.op n)) := by
  obtain ⟨b, hb⟩ := hg _ (c.1 (Opposite.op n))
  exact ⟨⟨b, hb⟩⟩

private lemma fiberSystem_isMittagLeffler
    {A B C : ℕᵒᵖ ⥤ AddCommGrpCat.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (hexact : ∀ j, Function.Exact (f.app j) (g.app j))
    (hg : ∀ j, Function.Surjective (g.app j))
    (hA : (underlying A).IsMittagLeffler) (c : (underlying C).sections) :
    (fiberSystem g c).IsMittagLeffler := by
  intro j
  obtain ⟨i, p, hp⟩ := hA j
  refine ⟨i, p, ?_⟩
  intro k q
  rintro _ ⟨bi, rfl⟩
  obtain ⟨l, r, s, hrs⟩ := CategoryTheory.IsCofiltered.cospan p q
  obtain ⟨yl, hyl⟩ := hg l (c.1 l)
  have hdker : g.app i (bi.1 - B.map r yl) = 0 := by
    rw [(g.app i).hom.map_sub, bi.2]
    have hnat := ConcreteCategory.congr_hom (g.naturality r) yl
    rw [AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply] at hnat
    rw [hnat, hyl]
    have hc := c.2 r
    change C.map r (c.1 l) = c.1 i at hc
    rw [hc, sub_self]
  obtain ⟨ai, hai⟩ := (hexact i (bi.1 - B.map r yl)).mp hdker
  obtain ⟨ak, hak⟩ := hp q ⟨ai, rfl⟩
  have hak' : A.map q ak = A.map p ai := hak
  let bk : B.obj k := B.map s yl + f.app k ak
  have hbk : g.app k bk = c.1 k := by
    dsimp [bk]
    rw [(g.app k).hom.map_add]
    have hnat := ConcreteCategory.congr_hom (g.naturality s) yl
    rw [AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply] at hnat
    rw [hnat, hyl]
    have hc := c.2 s
    change C.map s (c.1 l) = c.1 k at hc
    rw [hc]
    have hzero : g.app k (f.app k ak) = 0 :=
      (hexact k (f.app k ak)).mpr ⟨ak, rfl⟩
    rw [hzero, add_zero]
  refine ⟨⟨bk, hbk⟩, Subtype.ext ?_⟩
  change B.map q bk = B.map p bi.1
  dsimp [bk]
  rw [(B.map q).hom.map_add]
  have hnat := ConcreteCategory.congr_hom (f.naturality q) ak
  rw [AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply] at hnat
  rw [← hnat, hak']
  rw [← AddCommGrpCat.comp_apply, ← B.map_comp, ← hrs, B.map_comp,
    AddCommGrpCat.comp_apply]
  have hnatp := ConcreteCategory.congr_hom (f.naturality p) ai
  rw [AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply] at hnatp
  rw [hnatp, ← (B.map p).hom.map_add, hai]
  simp

/-- **Hartshorne II.9, Proposition 9.1(b).** A levelwise short exact sequence of sequential
inverse systems remains short exact on compatible sections when its kernel system satisfies the
Mittag--Leffler condition. -/
theorem inverseLimit_exact_of_isMittagLeffler
    {A B C : ℕᵒᵖ ⥤ AddCommGrpCat.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (hlevel : ∀ j, Function.Injective (f.app j) ∧
      Function.Exact (f.app j) (g.app j) ∧ Function.Surjective (g.app j))
    (hA : IsMittagLeffler A) :
    Function.Injective (sectionsMap f) ∧
      Function.Exact (sectionsMap f) (sectionsMap g) ∧
      Function.Surjective (sectionsMap g) := by
  have hf : ∀ j, Function.Injective (f.app j) := fun j => (hlevel j).1
  have hexact : ∀ j, Function.Exact (f.app j) (g.app j) := fun j => (hlevel j).2.1
  have hg : ∀ j, Function.Surjective (g.app j) := fun j => (hlevel j).2.2
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    funext j
    apply hf j
    exact congrArg (fun s => s.1 j) hxy
  · intro b
    constructor
    · intro hgb
      have hk : ∀ j, g.app j (b.1 j) = 0 := fun j => by
        have h := congrArg (fun s => s.1 j) hgb
        change g.app j (b.1 j) = 0 at h
        exact h
      choose a ha using fun j => (hexact j (b.1 j)).mp (hk j)
      let as : (underlying A).sections := ⟨a, by
        intro i j p
        apply hf j
        change f.app j (A.map p (a i)) = f.app j (a j)
        have hnat := ConcreteCategory.congr_hom (f.naturality p) (a i)
        rw [AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply] at hnat
        rw [hnat, ha i, ha j]
        have hb := b.2 p
        change B.map p (b.1 i) = b.1 j at hb
        exact hb⟩
      refine ⟨as, ?_⟩
      apply Subtype.ext
      funext j
      exact ha j
    · rintro ⟨a, rfl⟩
      apply Subtype.ext
      funext j
      exact (hexact j (f.app j (a.1 j))).mpr ⟨a.1 j, rfl⟩
  · intro c
    have hFib : (fiberSystem g c).IsMittagLeffler :=
      fiberSystem_isMittagLeffler f g hexact hg hA c
    obtain ⟨s⟩ := nonempty_sections_of_mittagLeffler (fiberSystem g c) hFib
      (fiberSystem_nonempty g hg c)
    let b : (underlying B).sections := ⟨fun j => (s.1 j).1, by
      intro i j p
      have hs := s.2 p
      exact congrArg Subtype.val hs⟩
    refine ⟨b, ?_⟩
    apply Subtype.ext
    funext j
    exact (s.1 j).2

end Hartshorne.InverseSystem

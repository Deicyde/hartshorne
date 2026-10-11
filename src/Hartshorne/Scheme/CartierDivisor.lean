/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.QuotientSheafStalks
import Hartshorne.Scheme.TotalQuotientSheaf
import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# Cartier divisors

Hartshorne, *Algebraic Geometry*, II.6 (p. 141).

For an arbitrary scheme `X`, a Cartier divisor is a global section of the quotient sheaf
`K_X^* / O_X^*`.  We transport the multiplicative unit sheaves to additive commutative groups
before taking their cokernel, so divisors and divisor classes use the additive notation of the
source.  We also give the equivalent local-equation interface without choosing a canonical cover.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Scheme

noncomputable local instance : CommGrpCat.toAddCommGrp.{u}.IsRightAdjoint :=
  commGroupAddCommGroupEquivalence.{u}.symm.isRightAdjoint_inverse

private abbrev additivizeCommGrpSheaf (X : Scheme.{u}) :
    TopCat.Sheaf CommGrpCat.{u} X ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
  sheafCompose (Opens.grothendieckTopology X) CommGrpCat.toAddCommGrp.{u}

/-- The structure-unit sheaf, with its multiplicative group written additively. -/
noncomputable abbrev structureUnitsAddSheaf (X : Scheme.{u}) :
    TopCat.Sheaf AddCommGrpCat.{u} X :=
  (additivizeCommGrpSheaf X).obj X.structureUnitsSheaf

/-- The total-quotient-unit sheaf, with its multiplicative group written additively. -/
noncomputable abbrev totalQuotientUnitsAddSheaf (X : Scheme.{u}) :
    TopCat.Sheaf AddCommGrpCat.{u} X :=
  (additivizeCommGrpSheaf X).obj X.totalQuotientUnitsSheaf

/-- The additive form of the inclusion `O_X^* ⟶ K_X^*`. -/
noncomputable abbrev structureUnitsToTotalQuotientUnitsAdd (X : Scheme.{u}) :
    X.structureUnitsAddSheaf ⟶ X.totalQuotientUnitsAddSheaf :=
  (additivizeCommGrpSheaf X).map X.structureUnitsToTotalQuotientUnits

@[simp]
theorem structureUnitsToTotalQuotientUnitsAdd_apply
    (X : Scheme.{u}) (U : X.Opens)
    (f : X.structureUnitsSheaf.obj.obj (.op U)) :
    X.structureUnitsToTotalQuotientUnitsAdd.hom.app (.op U) (Additive.ofMul f) =
      Additive.ofMul (X.structureUnitsToTotalQuotientUnits.hom.app (.op U) f) :=
  rfl

@[simp]
theorem structureUnitsToTotalQuotientUnitsAdd_toMul_apply
    (X : Scheme.{u}) (U : X.Opens)
    (f : X.structureUnitsAddSheaf.obj.obj (.op U)) :
    (X.structureUnitsToTotalQuotientUnitsAdd.hom.app (.op U) f).toMul =
      X.structureUnitsToTotalQuotientUnits.hom.app (.op U) f.toMul :=
  rfl

@[simp]
theorem totalQuotientUnitsAddSheaf_map_ofMul
    (X : Scheme.{u}) {U V : X.Opens} (h : V ≤ U)
    (f : X.totalQuotientUnitsSheaf.obj.obj (.op U)) :
    X.totalQuotientUnitsAddSheaf.obj.map (homOfLE h).op (Additive.ofMul f) =
      Additive.ofMul
        (X.totalQuotientUnitsSheaf.obj.map (homOfLE h).op f) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
instance structureUnitsToTotalQuotientUnitsAdd_mono (X : Scheme.{u}) :
    Mono X.structureUnitsToTotalQuotientUnitsAdd := by
  apply CategoryTheory.Sheaf.mono_of_injective
  intro U
  change Function.Injective
    (Units.map (X.toTotalQuotientSheaf.hom.app U).hom.toMonoidHom)
  apply Units.map_injective
  let _ : Mono X.toTotalQuotientSheaf := totalQuotientSheaf_mono X
  have h₁ : Mono X.toTotalQuotientSheaf.hom :=
    CategoryTheory.presheaf_mono_of_mono
      (Opens.grothendieckTopology X) CommRingCat X.toTotalQuotientSheaf
  have h₂ : Mono (X.toTotalQuotientSheaf.hom.app U) :=
    (NatTrans.mono_iff_mono_app X.toTotalQuotientSheaf.hom).mp h₁ U
  exact (ConcreteCategory.mono_iff_injective_of_preservesPullback _).mp h₂

/-- The quotient sheaf `K_X^* / O_X^*`, in additive notation. -/
noncomputable abbrev cartierDivisorSheaf (X : Scheme.{u}) :
    TopCat.Sheaf AddCommGrpCat.{u} X :=
  cokernel X.structureUnitsToTotalQuotientUnitsAdd

/-- The quotient projection `K_X^* ⟶ K_X^* / O_X^*`, in additive notation. -/
noncomputable abbrev toCartierDivisorSheaf (X : Scheme.{u}) :
    X.totalQuotientUnitsAddSheaf ⟶ X.cartierDivisorSheaf :=
  cokernel.π X.structureUnitsToTotalQuotientUnitsAdd

instance toCartierDivisorSheaf_epi (X : Scheme.{u}) :
    Epi X.toCartierDivisorSheaf := by
  change Epi (coequalizer.π X.structureUnitsToTotalQuotientUnitsAdd 0)
  infer_instance

@[reassoc (attr := simp)]
theorem structureUnitsToTotalQuotientUnitsAdd_comp_toCartierDivisorSheaf
    (X : Scheme.{u}) :
    X.structureUnitsToTotalQuotientUnitsAdd ≫ X.toCartierDivisorSheaf = 0 :=
  cokernel.condition _

/-- The categorical quotient sheaf agrees with the explicit sheafification of the pointwise
cokernel used by the quotient-sheaf API. -/
noncomputable def cartierDivisorSheafIsoSheafifiedCokernel (X : Scheme.{u}) :
    X.cartierDivisorSheaf ≅
      Hartshorne.abelianSheafCokernel X.structureUnitsToTotalQuotientUnitsAdd :=
  Hartshorne.abelianSheafCokernelIso _

/-- The additive group of Cartier divisors, `Γ(X, K_X^* / O_X^*)`. -/
noncomputable abbrev CartierDivisor (X : Scheme.{u}) : Type u :=
  X.cartierDivisorSheaf.obj.obj (.op ⊤)

namespace CartierDivisor

/-- Restrict a global Cartier divisor to an open subset. -/
def restrict {X : Scheme.{u}} (D : X.CartierDivisor) (U : X.Opens) :
    X.cartierDivisorSheaf.obj.obj (.op U) :=
  X.cartierDivisorSheaf.obj.map (homOfLE le_top).op D

@[simp]
theorem restrict_restrict {X : Scheme.{u}} (D : X.CartierDivisor)
    {U V : X.Opens} (h : V ≤ U) :
    X.cartierDivisorSheaf.obj.map (homOfLE h).op (D.restrict U) =
      D.restrict V := by
  simp only [restrict, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

end CartierDivisor

@[simp]
theorem toCartierDivisorSheaf_naturality_apply_add
    (X : Scheme.{u}) {U V : X.Opens} (h : V ≤ U)
    (f : X.totalQuotientUnitsAddSheaf.obj.obj (.op U)) :
    X.cartierDivisorSheaf.obj.map (homOfLE h).op
        (X.toCartierDivisorSheaf.hom.app (.op U) f) =
      X.toCartierDivisorSheaf.hom.app (.op V)
        (X.totalQuotientUnitsAddSheaf.obj.map (homOfLE h).op f) := by
  exact ConcreteCategory.congr_hom
    (X.toCartierDivisorSheaf.hom.naturality (homOfLE h).op).symm f

@[simp]
theorem toCartierDivisorSheaf_naturality_apply
    (X : Scheme.{u}) {U V : X.Opens} (h : V ≤ U)
    (f : X.totalQuotientUnitsSheaf.obj.obj (.op U)) :
    X.cartierDivisorSheaf.obj.map (homOfLE h).op
        (X.toCartierDivisorSheaf.hom.app (.op U) (Additive.ofMul f)) =
      X.toCartierDivisorSheaf.hom.app (.op V)
        (Additive.ofMul
          (X.totalQuotientUnitsSheaf.obj.map (homOfLE h).op f)) := by
  convert X.toCartierDivisorSheaf_naturality_apply_add h (Additive.ofMul f) using 1
  all_goals rfl

/-- Two local total-quotient units have the same quotient section exactly when their ratio is a
regular unit on the whole open set. -/
theorem toCartierDivisorSheaf_apply_eq_iff_ratio
    (X : Scheme.{u}) (U : X.Opens)
    (f g : X.totalQuotientUnitsSheaf.obj.obj (.op U)) :
    X.toCartierDivisorSheaf.hom.app (.op U) (Additive.ofMul f) =
        X.toCartierDivisorSheaf.hom.app (.op U) (Additive.ofMul g) ↔
      ∃ a : X.structureUnitsSheaf.obj.obj (.op U),
        X.structureUnitsToTotalQuotientUnits.hom.app (.op U) a = f / g := by
  let i := X.structureUnitsToTotalQuotientUnitsAdd
  let q := X.toCartierDivisorSheaf
  constructor
  · intro h
    have hz : q.hom.app (.op U) (Additive.ofMul f - Additive.ofMul g) = 0 := by
      calc
        q.hom.app (.op U) (Additive.ofMul f - Additive.ofMul g) =
            q.hom.app (.op U) (Additive.ofMul f) -
              q.hom.app (.op U) (Additive.ofMul g) :=
          (q.hom.app (.op U)).hom.map_sub _ _
        _ = 0 := sub_eq_zero.mpr h
    let S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) :=
      ShortComplex.mk i q (cokernel.condition i)
    have hS : S.Exact := ShortComplex.exact_cokernel i
    obtain ⟨t, ht⟩ := TopCat.Sheaf.sections_exact_of_left_exact hS
      (show Mono S.f from structureUnitsToTotalQuotientUnitsAdd_mono X)
      (Additive.ofMul f - Additive.ofMul g) hz
    refine ⟨t.toMul, ?_⟩
    change Additive.ofMul
        (X.structureUnitsToTotalQuotientUnits.hom.app (.op U) t.toMul) =
      Additive.ofMul (f / g) at ht
    exact Additive.ofMul.injective ht
  · rintro ⟨a, ha⟩
    apply sub_eq_zero.mp
    change q.hom.app (.op U) (Additive.ofMul f) -
      q.hom.app (.op U) (Additive.ofMul g) = 0
    rw [← (q.hom.app (.op U)).hom.map_sub]
    have ha' :
        i.hom.app (.op U) (Additive.ofMul a) =
          Additive.ofMul f - Additive.ofMul g := by
      simpa only [i, structureUnitsToTotalQuotientUnitsAdd_apply,
        ← ofMul_div] using congrArg Additive.ofMul ha
    have hc : i.hom ≫ q.hom = 0 :=
      congrArg (fun k ↦ k.hom) (cokernel.condition i)
    have hzero : q.hom.app (.op U) (i.hom.app (.op U) (Additive.ofMul a)) = 0 := by
      have hca :=
        ConcreteCategory.congr_hom (NatTrans.congr_app hc (.op U)) (Additive.ofMul a)
      change q.hom.app (.op U) (i.hom.app (.op U) (Additive.ofMul a)) = 0 at hca
      exact hca
    exact (congrArg (q.hom.app (.op U)) ha'.symm).trans hzero

/-- Local equations for a Cartier divisor. Transition units are asserted on every full pairwise
overlap; no further refinement is hidden in the definition. -/
structure CartierLocalEquations (X : Scheme.{u}) (I : Type u) where
  U : I → X.Opens
  cover : (⊤ : X.Opens) ≤ ⨆ i, U i
  f : ∀ i, X.totalQuotientUnitsSheaf.obj.obj (.op (U i))
  transition : ∀ i j, ∃ a : X.structureUnitsSheaf.obj.obj (.op (U i ⊓ U j)),
    X.structureUnitsToTotalQuotientUnits.hom.app (.op (U i ⊓ U j)) a =
      X.totalQuotientUnitsSheaf.obj.map (Opens.infLELeft (U i) (U j)).op (f i) /
        X.totalQuotientUnitsSheaf.obj.map (Opens.infLERight (U i) (U j)).op (f j)

namespace CartierLocalEquations

/-- The quotient section represented by one local equation. -/
def quotientSection {X : Scheme.{u}} {I : Type u}
    (E : X.CartierLocalEquations I) (i : I) :
    X.cartierDivisorSheaf.obj.obj (.op (E.U i)) :=
  X.toCartierDivisorSheaf.hom.app (.op (E.U i)) (Additive.ofMul (E.f i))

/-- A local-equation presentation represents a global Cartier divisor when its quotient sections
are the restrictions of that divisor. -/
def Represents {X : Scheme.{u}} {I : Type u}
    (E : X.CartierLocalEquations I) (D : X.CartierDivisor) : Prop :=
  ∀ i, D.restrict (E.U i) = E.quotientSection i

theorem quotientSection_isCompatible {X : Scheme.{u}} {I : Type u}
    (E : X.CartierLocalEquations I) :
    TopCat.Presheaf.IsCompatible X.cartierDivisorSheaf.obj E.U E.quotientSection := by
  intro i j
  change X.cartierDivisorSheaf.obj.map (Opens.infLELeft (E.U i) (E.U j)).op
      (X.toCartierDivisorSheaf.hom.app (.op (E.U i)) (Additive.ofMul (E.f i))) =
    X.cartierDivisorSheaf.obj.map (Opens.infLERight (E.U i) (E.U j)).op
      (X.toCartierDivisorSheaf.hom.app (.op (E.U j)) (Additive.ofMul (E.f j)))
  calc
    _ = X.toCartierDivisorSheaf.hom.app (.op (E.U i ⊓ E.U j))
        (Additive.ofMul (X.totalQuotientUnitsSheaf.obj.map
          (Opens.infLELeft (E.U i) (E.U j)).op (E.f i))) :=
      X.toCartierDivisorSheaf_naturality_apply _ _
    _ = X.toCartierDivisorSheaf.hom.app (.op (E.U i ⊓ E.U j))
        (Additive.ofMul (X.totalQuotientUnitsSheaf.obj.map
          (Opens.infLERight (E.U i) (E.U j)).op (E.f j))) :=
      (X.toCartierDivisorSheaf_apply_eq_iff_ratio _ _ _).2 (E.transition i j)
    _ = _ := (X.toCartierDivisorSheaf_naturality_apply _ _).symm

/-- Compatible local equations glue to a unique global Cartier divisor. -/
theorem existsUnique_represents {X : Scheme.{u}} {I : Type u}
    (E : X.CartierLocalEquations I) :
    ∃! D : X.CartierDivisor, E.Represents D := by
  simpa only [Represents, CartierDivisor.restrict] using
    X.cartierDivisorSheaf.existsUnique_gluing' E.U ⊤
      (fun i ↦ homOfLE le_top) E.cover E.quotientSection E.quotientSection_isCompatible

/-- Build local equations from a cover and local lifts of one fixed global divisor. -/
def ofRepresentingFamily {X : Scheme.{u}} {I : Type u}
    (D : X.CartierDivisor) (U : I → X.Opens) (cover : (⊤ : X.Opens) ≤ ⨆ i, U i)
    (f : ∀ i, X.totalQuotientUnitsSheaf.obj.obj (.op (U i)))
    (hf : ∀ i, D.restrict (U i) =
      X.toCartierDivisorSheaf.hom.app (.op (U i)) (Additive.ofMul (f i))) :
    X.CartierLocalEquations I where
  U := U
  cover := cover
  f := f
  transition i j := by
    apply (X.toCartierDivisorSheaf_apply_eq_iff_ratio (U i ⊓ U j) _ _).1
    calc
      _ = X.cartierDivisorSheaf.obj.map (Opens.infLELeft (U i) (U j)).op
          (X.toCartierDivisorSheaf.hom.app (.op (U i)) (Additive.ofMul (f i))) :=
        (X.toCartierDivisorSheaf_naturality_apply _ _).symm
      _ = X.cartierDivisorSheaf.obj.map (Opens.infLELeft (U i) (U j)).op
          (D.restrict (U i)) := congrArg _ (hf i).symm
      _ = D.restrict (U i ⊓ U j) := D.restrict_restrict _
      _ = X.cartierDivisorSheaf.obj.map (Opens.infLERight (U i) (U j)).op
          (D.restrict (U j)) := (D.restrict_restrict _).symm
      _ = X.cartierDivisorSheaf.obj.map (Opens.infLERight (U i) (U j)).op
          (X.toCartierDivisorSheaf.hom.app (.op (U j)) (Additive.ofMul (f j))) :=
        congrArg _ (hf j)
      _ = _ := X.toCartierDivisorSheaf_naturality_apply _ _

@[simp]
theorem ofRepresentingFamily_represents {X : Scheme.{u}} {I : Type u}
    (D : X.CartierDivisor) (U : I → X.Opens) (cover : (⊤ : X.Opens) ≤ ⨆ i, U i)
    (f : ∀ i, X.totalQuotientUnitsSheaf.obj.obj (.op (U i)))
    (hf : ∀ i, D.restrict (U i) =
      X.toCartierDivisorSheaf.hom.app (.op (U i)) (Additive.ofMul (f i))) :
    (ofRepresentingFamily D U cover f hf).Represents D :=
  hf

/-- Every Cartier divisor admits local equations on an open cover. -/
theorem exists_localEquations {X : Scheme.{u}} (D : X.CartierDivisor) :
    ∃ E : X.CartierLocalEquations X, E.Represents D := by
  classical
  have hloc : TopCat.Presheaf.IsLocallySurjective X.toCartierDivisorSheaf.hom :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi X.toCartierDivisorSheaf).2
      (toCartierDivisorSheaf_epi X)
  have hsections :=
    (TopCat.Presheaf.isLocallySurjective_iff X.toCartierDivisorSheaf.hom).1 hloc ⊤ D
  choose U hU data hx using fun x : X ↦ hsections x trivial
  choose s hs using data
  have cover : (⊤ : X.Opens) ≤ ⨆ x, U x := by
    intro x _
    simp only [Opens.mem_iSup]
    exact ⟨x, hx x⟩
  let f : ∀ x, X.totalQuotientUnitsSheaf.obj.obj (.op (U x)) :=
    fun x ↦ (s x).toMul
  have hrep : ∀ x, D.restrict (U x) =
      X.toCartierDivisorSheaf.hom.app (.op (U x)) (Additive.ofMul (f x)) := by
    intro x
    have hs' := hs x
    change X.toCartierDivisorSheaf.hom.app (.op (U x)) (s x) =
      D.restrict (U x) at hs'
    simpa [f] using hs'.symm
  exact ⟨ofRepresentingFamily D U cover f hrep,
    ofRepresentingFamily_represents D U cover f hrep⟩

/-- `F.Refines E` means that the cover of `F` refines that of `E` and its equations differ from
the restricted equations of `E` by regular units. -/
def Refines {X : Scheme.{u}} {I J : Type u}
    (F : X.CartierLocalEquations J) (E : X.CartierLocalEquations I) : Prop :=
  ∃ a : J → I, ∃ h : ∀ j, F.U j ≤ E.U (a j),
    ∀ j, ∃ b : X.structureUnitsSheaf.obj.obj (.op (F.U j)),
      X.structureUnitsToTotalQuotientUnits.hom.app (.op (F.U j)) b =
        F.f j / X.totalQuotientUnitsSheaf.obj.map (homOfLE (h j)).op (E.f (a j))

theorem refines_refl {X : Scheme.{u}} {I : Type u}
    (E : X.CartierLocalEquations I) : E.Refines E := by
  refine ⟨id, fun _ ↦ le_rfl, fun i ↦ ⟨1, ?_⟩⟩
  simp

/-- Refinement preserves the represented Cartier divisor. -/
theorem Refines.represents {X : Scheme.{u}} {I J : Type u}
    {F : X.CartierLocalEquations J} {E : X.CartierLocalEquations I}
    (hFE : F.Refines E) {D : X.CartierDivisor} (hD : E.Represents D) :
    F.Represents D := by
  obtain ⟨a, h, unit⟩ := hFE
  intro j
  rw [← D.restrict_restrict (h j), hD (a j), quotientSection,
    toCartierDivisorSheaf_naturality_apply, quotientSection]
  symm
  exact (X.toCartierDivisorSheaf_apply_eq_iff_ratio _ _ _).2 (unit j)

/-- Two presentations are equivalent when they represent one common global Cartier divisor. -/
def SameDivisor {X : Scheme.{u}} {I J : Type u}
    (E : X.CartierLocalEquations I) (F : X.CartierLocalEquations J) : Prop :=
  ∃ D : X.CartierDivisor, E.Represents D ∧ F.Represents D

theorem sameDivisor_refl {X : Scheme.{u}} {I : Type u}
    (E : X.CartierLocalEquations I) : E.SameDivisor E := by
  obtain ⟨D, hD, -⟩ := E.existsUnique_represents
  exact ⟨D, hD, hD⟩

theorem SameDivisor.symm {X : Scheme.{u}} {I J : Type u}
    {E : X.CartierLocalEquations I} {F : X.CartierLocalEquations J}
    (h : E.SameDivisor F) : F.SameDivisor E := by
  obtain ⟨D, hE, hF⟩ := h
  exact ⟨D, hF, hE⟩

theorem SameDivisor.trans {X : Scheme.{u}} {I J K : Type u}
    {E : X.CartierLocalEquations I} {F : X.CartierLocalEquations J}
    {G : X.CartierLocalEquations K}
    (hEF : E.SameDivisor F) (hFG : F.SameDivisor G) : E.SameDivisor G := by
  obtain ⟨D, hE, hF⟩ := hEF
  obtain ⟨D', hF', hG⟩ := hFG
  obtain ⟨_, -, huniq⟩ := F.existsUnique_represents
  have hDD' : D = D' := (huniq D hF).trans (huniq D' hF').symm
  exact ⟨D, hE, hDD'.symm ▸ hG⟩

/-- Two presentations have a common refinement when a third local-equation presentation refines
both of them. -/
def HaveCommonRefinement {X : Scheme.{u}} {I J : Type u}
    (E : X.CartierLocalEquations I) (F : X.CartierLocalEquations J) : Prop :=
  ∃ (K : Type u) (R : X.CartierLocalEquations K), R.Refines E ∧ R.Refines F

private theorem commonRefinement_of_sameDivisor {X : Scheme.{u}} {I J : Type u}
    (E : X.CartierLocalEquations I) (F : X.CartierLocalEquations J)
    (h : E.SameDivisor F) : E.HaveCommonRefinement F := by
  obtain ⟨D, hE, hF⟩ := h
  let U : I × J → X.Opens := fun p ↦ E.U p.1 ⊓ F.U p.2
  have cover : (⊤ : X.Opens) ≤ ⨆ p, U p := by
    intro x _
    have hxE := E.cover (show x ∈ (⊤ : X.Opens) from trivial)
    have hxF := F.cover (show x ∈ (⊤ : X.Opens) from trivial)
    simp only [Opens.mem_iSup] at hxE hxF ⊢
    obtain ⟨i, hi⟩ := hxE
    obtain ⟨j, hj⟩ := hxF
    exact ⟨⟨i, j⟩, hi, hj⟩
  let f : ∀ p : I × J,
      X.totalQuotientUnitsSheaf.obj.obj (.op (U p)) :=
    fun p ↦ X.totalQuotientUnitsSheaf.obj.map
      (Opens.infLELeft (E.U p.1) (F.U p.2)).op (E.f p.1)
  have hrep : ∀ p, D.restrict (U p) =
      X.toCartierDivisorSheaf.hom.app (.op (U p)) (Additive.ofMul (f p)) := by
    intro p
    rw [← D.restrict_restrict (inf_le_left : U p ≤ E.U p.1),
      hE p.1, quotientSection, toCartierDivisorSheaf_naturality_apply]
    rfl
  let R : X.CartierLocalEquations (I × J) :=
    ofRepresentingFamily D U cover f hrep
  refine ⟨I × J, R, ?_, ?_⟩
  · refine ⟨Prod.fst, fun p ↦ inf_le_left, fun p ↦ ?_⟩
    apply (X.toCartierDivisorSheaf_apply_eq_iff_ratio (R.U p) _ _).1
    rfl
  · refine ⟨Prod.snd, fun p ↦ inf_le_right, fun p ↦ ?_⟩
    apply (X.toCartierDivisorSheaf_apply_eq_iff_ratio (R.U p) _ _).1
    change X.toCartierDivisorSheaf.hom.app (.op (U p)) (Additive.ofMul (f p)) =
      X.toCartierDivisorSheaf.hom.app (.op (U p))
        (Additive.ofMul
          (X.totalQuotientUnitsSheaf.obj.map
            (homOfLE (inf_le_right : U p ≤ F.U p.2)).op (F.f p.2)))
    have hF' := hF p.2
    change D.restrict (F.U p.2) =
      X.toCartierDivisorSheaf.hom.app (.op (F.U p.2))
        (Additive.ofMul (F.f p.2)) at hF'
    rw [← hrep p, ← X.toCartierDivisorSheaf_naturality_apply,
      ← hF', D.restrict_restrict]

private theorem sameDivisor_of_commonRefinement {X : Scheme.{u}} {I J : Type u}
    (E : X.CartierLocalEquations I) (F : X.CartierLocalEquations J)
    (h : E.HaveCommonRefinement F) : E.SameDivisor F := by
  obtain ⟨K, R, hRE, hRF⟩ := h
  obtain ⟨DE, hDE, -⟩ := E.existsUnique_represents
  obtain ⟨DF, hDF, -⟩ := F.existsUnique_represents
  have hRDE := hRE.represents hDE
  have hRDF := hRF.represents hDF
  obtain ⟨_, -, huniq⟩ := R.existsUnique_represents
  have hEq : DE = DF := (huniq DE hRDE).trans (huniq DF hRDF).symm
  exact ⟨DE, hDE, hEq.symm ▸ hDF⟩

/-- Two local-equation presentations represent the same Cartier divisor exactly when they have a
common refinement. -/
theorem sameDivisor_iff_commonRefinement {X : Scheme.{u}} {I J : Type u}
    (E : X.CartierLocalEquations I) (F : X.CartierLocalEquations J) :
    E.SameDivisor F ↔ E.HaveCommonRefinement F :=
  ⟨commonRefinement_of_sameDivisor E F, sameDivisor_of_commonRefinement E F⟩

end CartierLocalEquations

/-- Principal Cartier divisors form the image of global total-quotient units in the Cartier
divisor group. -/
noncomputable def principalCartierDivisorHom (X : Scheme.{u}) :
    (X.totalQuotientUnitsAddSheaf.obj.obj (.op ⊤) : Type u) →+ X.CartierDivisor :=
  (X.toCartierDivisorSheaf.hom.app (.op ⊤)).hom

/-- The principal Cartier divisor of a global total-quotient unit. -/
noncomputable def principalCartierDivisor (X : Scheme.{u})
    (f : X.totalQuotientUnitsSheaf.obj.obj (.op ⊤)) : X.CartierDivisor :=
  X.principalCartierDivisorHom (Additive.ofMul f)

/-- The subgroup of principal Cartier divisors. -/
noncomputable def principalCartierDivisorSubgroup (X : Scheme.{u}) :
    AddSubgroup X.CartierDivisor :=
  X.principalCartierDivisorHom.range

/-- Linear equivalence of Cartier divisors. -/
def CartierDivisor.LinearEquivalent {X : Scheme.{u}} (D E : X.CartierDivisor) : Prop :=
  D - E ∈ X.principalCartierDivisorSubgroup

/-- The Cartier divisor class group `CaCl X`. -/
noncomputable abbrev CartierClassGroup (X : Scheme.{u}) :=
  X.CartierDivisor ⧸ X.principalCartierDivisorSubgroup

/-- The quotient homomorphism from Cartier divisors to Cartier divisor classes. -/
noncomputable def cartierDivisorClassHom (X : Scheme.{u}) :
    X.CartierDivisor →+ X.CartierClassGroup :=
  QuotientAddGroup.mk' X.principalCartierDivisorSubgroup

theorem CartierDivisor.linearEquivalent_iff {X : Scheme.{u}}
    (D E : X.CartierDivisor) :
    D.LinearEquivalent E ↔
      ∃ f : X.totalQuotientUnitsSheaf.obj.obj (.op ⊤),
        D - E = X.principalCartierDivisor f := by
  constructor
  · intro h
    change D - E ∈ X.principalCartierDivisorHom.range at h
    obtain ⟨f, hf⟩ := AddMonoidHom.mem_range.mp h
    exact ⟨f.toMul, hf.symm⟩
  · rintro ⟨f, hf⟩
    change D - E ∈ X.principalCartierDivisorHom.range
    exact AddMonoidHom.mem_range.mpr ⟨Additive.ofMul f, hf.symm⟩

/-- Equality in the Cartier class group is linear equivalence. -/
theorem cartierDivisorClass_eq_iff {X : Scheme.{u}} (D E : X.CartierDivisor) :
    X.cartierDivisorClassHom D = X.cartierDivisorClassHom E ↔
      D.LinearEquivalent E := by
  change ((D : X.CartierClassGroup) = E) ↔
    D - E ∈ X.principalCartierDivisorSubgroup
  exact QuotientAddGroup.eq_iff_sub_mem

end Scheme

end


end AlgebraicGeometry

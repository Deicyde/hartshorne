/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.RightDerivedLongExactSequence

/-!
# Acyclic resolutions compute right derived functors

Hartshorne, *Algebraic Geometry*, III, Proposition 1.2A.

Let `F : C ⥤ D` be an additive left exact functor between abelian categories, where `C` has
injective resolutions. An object `X` is `F`-acyclic (`Hartshorne.IsRightAcyclic`) if
`RⁱF(X) = 0` for every `i > 0`. Given a resolution `A ⟶ K•` (a quasi-isomorphism from `A`,
viewed as a complex concentrated in degree `0`) whose terms are `F`-acyclic, we construct
isomorphisms `RⁿF(A) ≅ Hⁿ(F(K•))` (`Hartshorne.acyclicResolutionIso`) and prove that they are
natural with respect to morphisms of resolutions (`Hartshorne.acyclicResolutionIso_naturality`).

## Proof

Write `Zⁿ` for the cycles of `K•` in degree `n`; the augmentation identifies `A` with `Z⁰`.
Exactness of the resolution gives short exact sequences `0 ⟶ Zⁿ ⟶ Kⁿ ⟶ Zⁿ⁺¹ ⟶ 0`. Since `Kⁿ`
is acyclic, the long exact sequence of right derived functors shows that the connecting
morphisms `RⁱF(Zⁿ⁺¹) ⟶ Rⁱ⁺¹F(Zⁿ)` are isomorphisms for `i ≥ 1`, so that
`Rⁿ⁺¹F(A) ≅ R¹F(Zⁿ)`, and that `R¹F(Zⁿ)` is the cokernel of `F(Kⁿ) ⟶ F(Zⁿ⁺¹)`. As `F` is left
exact, `F(Zⁿ⁺¹)` is the kernel of `F(Kⁿ⁺¹) ⟶ F(Kⁿ⁺²)`, so this cokernel is `Hⁿ⁺¹(F(K•))`.
In degree `0`, `R⁰F(A) ≅ F(A) ≅ F(Z⁰) = H⁰(F(K•))`. Naturality follows from the naturality of
the connecting morphisms.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Hartshorne

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type*} [Category* D] [Abelian D]

/-- An object `X` is `F`-acyclic if `RⁱF(X) = 0` for every `i > 0`. -/
def IsRightAcyclic [HasInjectiveResolutions C] (F : C ⥤ D) [F.Additive] (X : C) : Prop :=
  ∀ n : ℕ, IsZero ((F.rightDerived (n + 1)).obj X)

namespace AcyclicResolution

open HomologicalComplex

/-- Transport of a cokernel along an isomorphism of the target. -/
def isColimitCokernelCoforkOfIso {E : Type*} [Category* E] [Preadditive E]
    {X Y Y' Z : E} {f : X ⟶ Y} {π : Y ⟶ Z} {w : f ≫ π = 0}
    (h : IsColimit (CokernelCofork.ofπ π w)) (e : Y' ≅ Y) (f' : X ⟶ Y')
    (hf : f' ≫ e.hom = f) :
    IsColimit (CokernelCofork.ofπ (f := f') (e.hom ≫ π)
      (by rw [← Category.assoc, hf, w])) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun g' hg' => h.desc (CokernelCofork.ofπ (e.inv ≫ g')
      (by rw [← hf, Category.assoc, e.hom_inv_id_assoc, hg'])))
    (fun g' hg' => by
      rw [Category.assoc]
      have := h.fac (CokernelCofork.ofπ (e.inv ≫ g')
        (by rw [← hf, Category.assoc, e.hom_inv_id_assoc, hg'])) WalkingParallelPair.one
      simp only [Cofork.ofπ_ι_app] at this
      rw [this, e.hom_inv_id_assoc])
    (fun g' hg' m hm => by
      apply Cofork.IsColimit.hom_ext h
      have := h.fac (CokernelCofork.ofπ (e.inv ≫ g')
        (by rw [← hf, Category.assoc, e.hom_inv_id_assoc, hg'])) WalkingParallelPair.one
      simp only [Cofork.ofπ_ι_app, Cofork.π_ofπ] at this ⊢
      rw [this, ← hm]
      simp)

section Cycles

variable (K : CochainComplex C ℕ)

/-- The short complex `Zⁿ ⟶ Kⁿ ⟶ Zⁿ⁺¹` built from the cycles of a cochain complex. -/
@[simps]
abbrev cyclesSC (n : ℕ) : ShortComplex C :=
  ShortComplex.mk (K.iCycles n) (K.toCycles n (n + 1)) (by
    rw [← cancel_mono (K.iCycles (n + 1)), Category.assoc, toCycles_i, iCycles_d, zero_comp])

lemma cyclesSC_shortExact (n : ℕ) (h : K.ExactAt (n + 1)) : (cyclesSC K n).ShortExact := by
  have hepi : Epi (K.toCycles n (n + 1)) := by
    have hz : IsZero (K.homology (n + 1)) := (K.exactAt_iff_isZero_homology _).1 h
    have hc := K.homologyIsCokernel n (n + 1) (by simp)
    exact Preadditive.epi_of_isZero_cokernel' _ hc hz
  refine ShortComplex.ShortExact.mk' ?_ (show Mono (K.iCycles n) from inferInstance) hepi
  exact ShortComplex.exact_of_f_is_kernel _
    (isKernelOfComp (K.iCycles (n + 1)) (K.d n (n + 1))
      (K.cyclesIsKernel n (n + 1) (by simp)) _ (K.toCycles_i n (n + 1)))

variable {K} {L : CochainComplex C ℕ} (g : K ⟶ L)

/-- The morphism of short complexes `cyclesSC K n ⟶ cyclesSC L n` induced by `g : K ⟶ L`. -/
@[simps]
abbrev cyclesSCMap (n : ℕ) : cyclesSC K n ⟶ cyclesSC L n where
  τ₁ := cyclesMap g n
  τ₂ := g.f n
  τ₃ := cyclesMap g (n + 1)
  comm₁₂ := cyclesMap_i g n
  comm₂₃ := by
    show g.f n ≫ L.toCycles n (n + 1) = K.toCycles n (n + 1) ≫ cyclesMap g (n + 1)
    rw [← cancel_mono (L.iCycles (n + 1))]
    simp [cyclesMap_i]

end Cycles

section Resolution

variable {A : C} {K : CochainComplex C ℕ}
  (ε : (CochainComplex.single₀ C).obj A ⟶ K) [QuasiIso ε]

include ε in
lemma exactAt_succ (n : ℕ) : K.ExactAt (n + 1) := by
  rw [← quasiIsoAt_iff_exactAt ε (n + 1)
    (CochainComplex.exactAt_succ_single_obj A n)]
  infer_instance

omit [QuasiIso ε] in
@[reassoc]
lemma ε_f_zero_comp_d : ε.f 0 ≫ K.d 0 1 = 0 := by
  rw [HomologicalComplex.Hom.comm, HomologicalComplex.single_obj_d, zero_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The augmentation `A ⟶ K⁰` is a kernel of `K⁰ ⟶ K¹`. -/
def isLimitKernelFork :
    IsLimit (KernelFork.ofι (Z := A) (ε.f 0) (ε_f_zero_comp_d ε)) := by
  refine IsLimit.ofIsoLimit (K.cyclesIsKernel 0 1 (by simp)) (Iso.symm ?_)
  refine Fork.ext ((singleObjHomologySelfIso (ComplexShape.up ℕ) 0 A).symm ≪≫
    isoOfQuasiIsoAt ε 0 ≪≫
    K.isoHomologyπ₀.symm) ?_
  simp [singleObjHomologySelfIso, singleObjCyclesSelfIso]

/-- The augmentation identifies `A` with the cycles of `K` in degree `0`. -/
def isoCycles₀ : A ≅ K.cycles 0 :=
  IsLimit.conePointUniqueUpToIso (isLimitKernelFork ε) (K.cyclesIsKernel 0 1 (by simp))

@[reassoc (attr := simp)]
lemma isoCycles₀_hom_iCycles : (isoCycles₀ ε).hom ≫ K.iCycles 0 = ε.f 0 :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero

lemma isoCycles₀_inv_naturality {B : C} {L : CochainComplex C ℕ}
    (ε' : (CochainComplex.single₀ C).obj B ⟶ L) [QuasiIso ε'] (f : A ⟶ B) (g : K ⟶ L)
    (comm : ε.f 0 ≫ g.f 0 = f ≫ ε'.f 0) :
    (isoCycles₀ ε).inv ≫ f = cyclesMap g 0 ≫ (isoCycles₀ ε').inv := by
  have h : f ≫ (isoCycles₀ ε').hom = (isoCycles₀ ε).hom ≫ cyclesMap g 0 := by
    rw [← cancel_mono (L.iCycles 0)]
    simpa [cyclesMap_i] using comm.symm
  rw [Iso.inv_comp_eq, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end Resolution

section Functor

variable (F : C ⥤ D) [F.Additive] [Limits.PreservesFiniteLimits F] (K : CochainComplex C ℕ)

/-- `F` maps the cycles of `K` in degree `n` to the cycles of `F(K)`. -/
def cyclesIsoF (n : ℕ) :
    ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).cycles n ≅ F.obj (K.cycles n) :=
  IsLimit.conePointUniqueUpToIso
    (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).cyclesIsKernel n (n + 1) (by simp))
    (KernelFork.mapIsLimit _ (K.cyclesIsKernel n (n + 1) (by simp)) F)

@[reassoc (attr := simp)]
lemma cyclesIsoF_hom_map_iCycles (n : ℕ) :
    (cyclesIsoF F K n).hom ≫ F.map (K.iCycles n) =
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).iCycles n :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero

@[reassoc (attr := simp)]
lemma toCycles_cyclesIsoF_hom (n : ℕ) :
    ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).toCycles n (n + 1) ≫
        (cyclesIsoF F K (n + 1)).hom =
      F.map (K.toCycles n (n + 1)) := by
  refine (cancel_mono (F.map (K.iCycles (n + 1)))).1 ?_
  have h := congrArg F.map (K.toCycles_i n (n + 1))
  rw [F.map_comp] at h
  rw [Category.assoc, cyclesIsoF_hom_map_iCycles]
  exact (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).toCycles_i n (n + 1)).trans h.symm

variable {K} {L : CochainComplex C ℕ} (g : K ⟶ L)

@[reassoc]
lemma cyclesIsoF_hom_naturality (n : ℕ) :
    cyclesMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map g) n ≫ (cyclesIsoF F L n).hom =
      (cyclesIsoF F K n).hom ≫ F.map (cyclesMap g n) := by
  refine (cancel_mono (F.map (L.iCycles n))).1 ?_
  rw [Category.assoc, cyclesIsoF_hom_map_iCycles, Category.assoc, ← F.map_comp,
    cyclesMap_i, F.map_comp, cyclesIsoF_hom_map_iCycles_assoc]
  erw [cyclesMap_i]
  rfl

end Functor

section Derived

variable [HasInjectiveResolutions C] (F : C ⥤ D) [F.Additive]
  {K : CochainComplex C ℕ} (hE : ∀ n, K.ExactAt (n + 1)) (hK : ∀ n, IsRightAcyclic F (K.X n))

include hK in
lemma isIso_rightDerivedδ (n i : ℕ) :
    IsIso (rightDerivedδ F (cyclesSC_shortExact K n (hE n)) (i + 1)) := by
  have h₁ := rightDerived_exact₃ F (cyclesSC_shortExact K n (hE n)) (i + 1)
  have h₂ := rightDerived_exact₁ F (cyclesSC_shortExact K n (hE n)) (i + 1)
  have : Mono (rightDerivedδ F (cyclesSC_shortExact K n (hE n)) (i + 1)) :=
    h₁.mono_g ((hK n i).eq_of_src _ _)
  have : Epi (rightDerivedδ F (cyclesSC_shortExact K n (hE n)) (i + 1)) :=
    h₂.epi_f ((hK n (i + 1)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

include hE hK in
/-- The connecting isomorphism `Rⁱ⁺¹F(Zⁿ⁺¹) ≅ Rⁱ⁺²F(Zⁿ)`. -/
def δIso (n i : ℕ) :
    (F.rightDerived (i + 1)).obj (K.cycles (n + 1)) ≅
      (F.rightDerived (i + 1 + 1)).obj (K.cycles n) :=
  @asIso _ _ _ _ (rightDerivedδ F (cyclesSC_shortExact K n (hE n)) (i + 1))
    (isIso_rightDerivedδ F hE hK n i)

include hE hK in
/-- Dimension shifting: `Rⁱ⁺¹F(Zᵐ) ≅ Rⁱ⁺¹⁺ᵐF(Z⁰)`. -/
noncomputable def shiftIso : ∀ (m i k : ℕ), i + 1 + m = k →
    ((F.rightDerived (i + 1)).obj (K.cycles m) ≅ (F.rightDerived k).obj (K.cycles 0))
  | 0, i, k, h => eqToIso (by subst h; rfl)
  | m + 1, i, k, h => δIso F hE hK m i ≪≫ shiftIso m (i + 1) k (by omega)

/-- The composite `F(Zⁿ⁺¹) ≅ R⁰F(Zⁿ⁺¹) ⟶ R¹F(Zⁿ)`. -/
def δ' (n : ℕ) : F.obj (K.cycles (n + 1)) ⟶ (F.rightDerived 1).obj (K.cycles n) :=
  F.toRightDerivedZero.app _ ≫ rightDerivedδ F (cyclesSC_shortExact K n (hE n)) 0

lemma map_toCycles_rightDerivedδ (n : ℕ) : (F.rightDerived 0).map (K.toCycles n (n + 1)) ≫
    rightDerivedδ F (cyclesSC_shortExact K n (hE n)) 0 = 0 :=
  Hartshorne.RightDerivedLES.Horseshoe.map_g_comp_δ F (cyclesSC_shortExact K n (hE n)) _ _ 0

lemma map_toCycles_δ' (n : ℕ) : F.map (K.toCycles n (n + 1)) ≫ δ' F hE n = 0 := by
  have h := map_toCycles_rightDerivedδ F hE n
  rw [δ']
  erw [F.toRightDerivedZero.naturality_assoc, h, comp_zero]

variable [Limits.PreservesFiniteLimits F]

/-- `R¹F(Zⁿ)` is the cokernel of `F(Kⁿ) ⟶ F(Zⁿ⁺¹)`. -/
def isColimitδ' (n : ℕ) :
    IsColimit (CokernelCofork.ofπ (δ' F hE n) (map_toCycles_δ' F hE n)) := by
  have hex : (ShortComplex.mk _ _ (map_toCycles_rightDerivedδ F hE n)).Exact :=
    rightDerived_exact₃ F (cyclesSC_shortExact K n (hE n)) 0
  have hepi : Epi (rightDerivedδ F (cyclesSC_shortExact K n (hE n)) 0) :=
    (rightDerived_exact₁ F (cyclesSC_shortExact K n (hE n)) 0).epi_f
      ((hK n 0).eq_of_tgt _ _)
  let S' := ShortComplex.mk _ _ (map_toCycles_δ' F hE n)
  have e : S' ≅ ShortComplex.mk _ _ (map_toCycles_rightDerivedδ F hE n) :=
    ShortComplex.isoMk
      (asIso (F.toRightDerivedZero.app (K.X n)))
      (asIso (F.toRightDerivedZero.app (K.cycles (n + 1)))) (Iso.refl _)
      (F.toRightDerivedZero.naturality _).symm (by simp [S', δ'])
  have hex' : S'.Exact := (ShortComplex.exact_iff_of_iso e).2 hex
  have : Epi S'.g :=
    @epi_comp _ _ _ _ _ (F.toRightDerivedZero.app (K.cycles (n + 1))) inferInstance _ hepi
  exact hex'.gIsCokernel

/-- `Hⁿ⁺¹(F(K)) ≅ R¹F(Zⁿ)`. -/
def homIso (n : ℕ) :
    ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homology (n + 1) ≅
      (F.rightDerived 1).obj (K.cycles n) :=
  IsColimit.coconePointUniqueUpToIso
    (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homologyIsCokernel n (n + 1) (by simp))
    (isColimitCokernelCoforkOfIso (isColimitδ' F hE hK n) (cyclesIsoF F K (n + 1)) _
      (toCycles_cyclesIsoF_hom F K n))

@[reassoc (attr := simp)]
lemma homologyπ_homIso_hom (n : ℕ) :
    ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homologyπ (n + 1) ≫
        (homIso F hE hK n).hom =
      (cyclesIsoF F K (n + 1)).hom ≫ δ' F hE n := by
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homologyIsCokernel n (n + 1) (by simp))
    (isColimitCokernelCoforkOfIso (isColimitδ' F hE hK n) (cyclesIsoF F K (n + 1)) _
      (toCycles_cyclesIsoF_hom F K n)) WalkingParallelPair.one

variable (K) in
/-- `H⁰(F(K)) ≅ R⁰F(Z⁰)`. -/
def homIso₀ :
    ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homology 0 ≅
      (F.rightDerived 0).obj (K.cycles 0) :=
  (CochainComplex.isoHomologyπ₀ ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)).symm ≪≫
    cyclesIsoF F K 0 ≪≫
    asIso (F.toRightDerivedZero.app _)

end Derived

section Naturality

variable [HasInjectiveResolutions C] (F : C ⥤ D) [F.Additive]
  {K L : CochainComplex C ℕ} (g : K ⟶ L)
  (hEK : ∀ n, K.ExactAt (n + 1)) (hKK : ∀ n, IsRightAcyclic F (K.X n))
  (hEL : ∀ n, L.ExactAt (n + 1)) (hKL : ∀ n, IsRightAcyclic F (L.X n))

@[reassoc]
lemma δIso_hom_naturality (n i : ℕ) :
    (F.rightDerived (i + 1)).map (cyclesMap g (n + 1)) ≫ (δIso F hEL hKL n i).hom =
      (δIso F hEK hKK n i).hom ≫ (F.rightDerived (i + 1 + 1)).map (cyclesMap g n) :=
  (rightDerivedδ_naturality F (cyclesSCMap g n) _ _ (i + 1)).symm

@[reassoc]
lemma shiftIso_hom_naturality (m : ℕ) : ∀ (i k : ℕ) (h : i + 1 + m = k),
    (F.rightDerived (i + 1)).map (cyclesMap g m) ≫ (shiftIso F hEL hKL m i k h).hom =
      (shiftIso F hEK hKK m i k h).hom ≫ (F.rightDerived k).map (cyclesMap g 0) := by
  induction m with
  | zero =>
    intro i k h
    subst h
    simp [shiftIso]
  | succ m ih =>
    intro i k h
    simp only [shiftIso, Iso.trans_hom, Category.assoc]
    rw [δIso_hom_naturality_assoc F g hEK hKK hEL hKL m i, ih]

@[reassoc]
lemma δ'_naturality (n : ℕ) :
    F.map (cyclesMap g (n + 1)) ≫ δ' F hEL n =
      δ' F hEK n ≫ (F.rightDerived 1).map (cyclesMap g n) := by
  simp only [δ', Category.assoc]
  erw [F.toRightDerivedZero.naturality_assoc,
    ← rightDerivedδ_naturality F (cyclesSCMap g n) _ _ 0]

variable [Limits.PreservesFiniteLimits F]

@[reassoc]
lemma homIso_hom_naturality (n : ℕ) :
    homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map g) (n + 1) ≫
        (homIso F hEL hKL n).hom =
      (homIso F hEK hKK n).hom ≫ (F.rightDerived 1).map (cyclesMap g n) := by
  rw [← cancel_epi (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homologyπ (n + 1)),
    homologyπ_naturality_assoc, homologyπ_homIso_hom, homologyπ_homIso_hom_assoc,
    cyclesIsoF_hom_naturality_assoc, δ'_naturality F g hEK hEL]

@[reassoc]
lemma homIso₀_hom_naturality :
    homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map g) 0 ≫ (homIso₀ F L).hom =
      (homIso₀ F K).hom ≫ (F.rightDerived 0).map (cyclesMap g 0) := by
  simp [homIso₀, cyclesIsoF_hom_naturality_assoc]

end Naturality

end AcyclicResolution

open AcyclicResolution

variable [HasInjectiveResolutions C] (F : C ⥤ D) [F.Additive] [Limits.PreservesFiniteLimits F]

/-- **Hartshorne III.1.2A.** If `A ⟶ K•` is a resolution of `A` by `F`-acyclic objects, then
`RⁿF(A) ≅ Hⁿ(F(K•))` for every `n`. -/
def acyclicResolutionIso {A : C} {K : CochainComplex C ℕ}
    (ε : (CochainComplex.single₀ C).obj A ⟶ K) [QuasiIso ε]
    (hK : ∀ i, IsRightAcyclic F (K.X i)) :
    ∀ n : ℕ, (F.rightDerived n).obj A ≅
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homology n
  | 0 => (F.rightDerived 0).mapIso (isoCycles₀ ε) ≪≫ (homIso₀ F K).symm
  | n + 1 => (F.rightDerived (n + 1)).mapIso (isoCycles₀ ε) ≪≫
      (shiftIso F (exactAt_succ ε) hK n 0 (n + 1) (by omega)).symm ≪≫
        (homIso F (exactAt_succ ε) hK n).symm

/-- **Hartshorne III.1.2A (naturality).** The isomorphisms `RⁿF(A) ≅ Hⁿ(F(K•))` are natural with
respect to morphisms of `F`-acyclic resolutions: a morphism `f : A ⟶ B` together with a cochain
map `g : K• ⟶ L•` compatible with the augmentations. -/
theorem acyclicResolutionIso_naturality {A B : C} {K L : CochainComplex C ℕ}
    (εA : (CochainComplex.single₀ C).obj A ⟶ K) [QuasiIso εA]
    (hK : ∀ i, IsRightAcyclic F (K.X i))
    (εB : (CochainComplex.single₀ C).obj B ⟶ L) [QuasiIso εB]
    (hL : ∀ i, IsRightAcyclic F (L.X i))
    (f : A ⟶ B) (g : K ⟶ L) (comm : εA ≫ g = (CochainComplex.single₀ C).map f ≫ εB)
    (n : ℕ) :
    (F.rightDerived n).map f ≫ (acyclicResolutionIso F εB hL n).hom =
      (acyclicResolutionIso F εA hK n).hom ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map g) n := by
  have comm₀ : εA.f 0 ≫ g.f 0 = f ≫ εB.f 0 := by
    simpa using congrArg (fun φ => φ.f 0) comm
  have hiso := isoCycles₀_inv_naturality εA εB f g comm₀
  rw [← cancel_epi (acyclicResolutionIso F εA hK n).inv,
    ← cancel_mono (acyclicResolutionIso F εB hL n).inv]
  simp only [Category.assoc, Iso.hom_inv_id, Iso.inv_hom_id_assoc, Category.comp_id]
  cases n with
  | zero =>
    simp only [acyclicResolutionIso, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
      Category.assoc]
    rw [homIso₀_hom_naturality_assoc, ← Functor.map_comp, ← Functor.map_comp, hiso]
  | succ n =>
    simp only [acyclicResolutionIso, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
      Category.assoc]
    rw [homIso_hom_naturality_assoc]
    erw [shiftIso_hom_naturality_assoc]
    rw [← Functor.map_comp, ← Functor.map_comp, hiso]

end Hartshorne

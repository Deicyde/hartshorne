/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.Codimension
import Hartshorne.Scheme.HeightOneLocalizationIntersection
import Hartshorne.Scheme.LocallyFreeInvertible
import Hartshorne.Scheme.Normal
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed

/-!
# Locally free sections extend across codimension two

Hartshorne, *Algebraic Geometry*, II.8, the section-extension step in the proof of
Theorem 8.19 (pp. 181–182), also used in Exercise 8.8 (p. 190).

Let `X` be a normal integral Noetherian scheme, let `U ⊆ X` be an open subset whose complement
has codimension at least two, and let `E` be a locally free `𝒪_X`-module of finite rank. Then
the restriction map `Γ(X, E) → Γ(U, E)` is bijective.

## Proof

* Every point of `X` whose local ring has dimension at most one lies in `U`: a point `x ∉ U`
  has `closure {x} ⊆ X - U`, so `2 ≤ codim (X - U) ≤ codim (closure {x}) = dim 𝒪_{X,x}`.
* For an affine open `A = Spec R`, the ring `R` is an integrally closed Noetherian domain and
  every height-one prime of `R` is a point of `A ∩ U`. A section over `A ∩ U` is an element of
  the function field lying in every `R_𝔭` with `ht 𝔭 = 1`, hence in `R` by Hartshorne,
  Proposition II.6.3A. So `Γ(A, 𝒪_X) → Γ(A ∩ U, 𝒪_X)` is bijective.
* On an open `W` where `E|_W ≅ 𝒪_W ^ r`, the same holds for `E` over every affine open
  contained in `W`, since restriction commutes with finite direct sums.
* These affine opens form a basis of `X`, and a restriction map of sheaves that is bijective
  over a basis is bijective over every open (`Hartshorne.bijective_map_inf_of_forall_exists`):
  uniqueness comes from locality and existence from gluing.

## Main result

* `AlgebraicGeometry.Scheme.Modules.bijective_presheaf_map_top_of_two_le_codim`.
-/

open CategoryTheory Limits TopologicalSpace Opposite

universe u

namespace Hartshorne

/-- The restriction map of a presheaf along an equality of opens is bijective. -/
theorem bijective_map_homOfLE_of_eq {C : Type*} [Category* C] {FC : C → C → Type*}
    {CC : C → Type*} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    {T : TopCat.{u}} (F : TopCat.Presheaf C T) {V W : Opens T} (h : W ≤ V) (e : W = V) :
    Function.Bijective (F.map (homOfLE h).op) := by
  subst e
  rw [show homOfLE h = 𝟙 W from rfl, op_id, F.map_id]
  exact ConcreteCategory.bijective_of_isIso _

/-- Bijectivity of a restriction map only depends on the target open, not on the inclusion
proof. -/
theorem bijective_map_homOfLE_congr {C : Type*} [Category* C] {FC : C → C → Type*}
    {CC : C → Type*} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    {T : TopCat.{u}} (F : TopCat.Presheaf C T) {V W W' : Opens T} (h : W ≤ V) (h' : W' ≤ V)
    (e : W = W') :
    Function.Bijective (F.map (homOfLE h).op) ↔ Function.Bijective (F.map (homOfLE h').op) := by
  subst e
  rfl

/-- Let `F` be a sheaf of abelian groups and `U` an open set. If every point of every open `W`
has an open neighbourhood `W' ⊆ W` over which restriction `F(W') → F(W' ∩ U)` is bijective, then
restriction `F(V) → F(V ∩ U)` is bijective for every open `V`. -/
theorem bijective_map_inf_of_forall_exists {T : TopCat.{u}}
    (F : TopCat.Sheaf AddCommGrpCat.{u} T)
    (U : Opens T)
    (h : ∀ W : Opens T, ∀ x ∈ W, ∃ W' : Opens T, W' ≤ W ∧ x ∈ W' ∧
      Function.Bijective (F.1.map (homOfLE (inf_le_left : W' ⊓ U ≤ W')).op))
    (V : Opens T) :
    Function.Bijective (F.1.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op) := by
  have hinj : ∀ V : Opens T,
      Function.Injective (F.1.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op) := by
    intro V s t hst
    choose W hWV hxW hW using fun x : V => h V x.1 x.2
    refine F.eq_of_locally_eq' W V (fun x => homOfLE (hWV x))
      (fun x hx => Opens.mem_iSup.2 ⟨⟨x, hx⟩, hxW _⟩) s t fun x => ?_
    apply (hW x).1
    rw [← ConcreteCategory.comp_apply, ← F.1.map_comp, ← ConcreteCategory.comp_apply,
      ← F.1.map_comp]
    have e : (homOfLE (hWV x)).op ≫ (homOfLE (inf_le_left : W x ⊓ U ≤ W x)).op =
        (homOfLE (inf_le_left : V ⊓ U ≤ V)).op ≫
          (homOfLE (inf_le_inf_right U (hWV x))).op := rfl
    rw [e, F.1.map_comp, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hst]
  refine ⟨hinj V, fun t => ?_⟩
  choose W hWV hxW hW using fun x : V => h V x.1 x.2
  choose s hs using fun x : V =>
    (hW x).2 (F.1.map (homOfLE (inf_le_inf_right U (hWV x))).op t)
  have hcomp : TopCat.Presheaf.IsCompatible F.1 W s := by
    intro x y
    apply hinj (W x ⊓ W y)
    rw [← ConcreteCategory.comp_apply, ← F.1.map_comp, ← ConcreteCategory.comp_apply,
      ← F.1.map_comp]
    have e1 : (Opens.infLELeft (W x) (W y)).op ≫
        (homOfLE (inf_le_left : W x ⊓ W y ⊓ U ≤ W x ⊓ W y)).op =
        (homOfLE (inf_le_left : W x ⊓ U ≤ W x)).op ≫
          (homOfLE (inf_le_inf_right U inf_le_left : W x ⊓ W y ⊓ U ≤ W x ⊓ U)).op := rfl
    have e2 : (Opens.infLERight (W x) (W y)).op ≫
        (homOfLE (inf_le_left : W x ⊓ W y ⊓ U ≤ W x ⊓ W y)).op =
        (homOfLE (inf_le_left : W y ⊓ U ≤ W y)).op ≫
          (homOfLE (inf_le_inf_right U inf_le_right : W x ⊓ W y ⊓ U ≤ W y ⊓ U)).op := rfl
    rw [e1, e2, F.1.map_comp, F.1.map_comp, ConcreteCategory.comp_apply,
      ConcreteCategory.comp_apply, hs x, hs y, ← ConcreteCategory.comp_apply, ← F.1.map_comp,
      ← ConcreteCategory.comp_apply, ← F.1.map_comp]
    rfl
  obtain ⟨g, hg, -⟩ := F.existsUnique_gluing' W V (fun x => homOfLE (hWV x))
    (fun x hx => Opens.mem_iSup.2 ⟨⟨x, hx⟩, hxW _⟩) s hcomp
  refine ⟨g, F.eq_of_locally_eq' (fun x : V => W x ⊓ U) (V ⊓ U)
    (fun x => homOfLE (inf_le_inf_right U (hWV x)))
    (fun x hx => Opens.mem_iSup.2 ⟨⟨x, hx.1⟩, hxW _, hx.2⟩) _ _ fun x => ?_⟩
  rw [← hs x, ← hg x, ← ConcreteCategory.comp_apply, ← F.1.map_comp,
    ← ConcreteCategory.comp_apply, ← F.1.map_comp]
  rfl

end Hartshorne

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- On a normal integral scheme, the sections over a nonempty affine open form an integrally
closed domain. -/
private theorem isIntegrallyClosed_sections_of_isAffineOpen [IsIntegral X]
    [Hartshorne.IsNormal X]
    {A : X.Opens} (hA : IsAffineOpen A) [Nonempty A] : IsIntegrallyClosed Γ(X, A) := by
  refine IsIntegrallyClosed.of_localization_maximal fun p _ _ ↦ ?_
  let y : PrimeSpectrum Γ(X, A) := ⟨p, inferInstance⟩
  have hy : hA.fromSpec y ∈ A := hA.range_fromSpec.le ⟨y, rfl⟩
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hA.fromSpec y, hy⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk (hA.fromSpec y)) p :=
    hA.isLocalization_stalk' y hy
  let e := IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p)
    (X.presheaf.stalk (hA.fromSpec y))
  exact IsIntegrallyClosed.of_equiv e.symm.toRingEquiv

/-- **Hartogs property of normal Noetherian integral schemes.** If every point of `X` whose
local ring has dimension at most one lies in `U`, then for every affine open `A` the restriction
`Γ(X, A) → Γ(X, A ∩ U)` is bijective. -/
theorem Scheme.bijective_presheaf_map_inf_of_isAffineOpen [IsIntegral X] [IsLocallyNoetherian X]
    [Hartshorne.IsNormal X] (U : X.Opens)
    (hU : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 1 → x ∈ U)
    {A : X.Opens} (hA : IsAffineOpen A) :
    Function.Bijective (X.presheaf.map (homOfLE (inf_le_left : A ⊓ U ≤ A)).op) := by
  by_cases hne : Nonempty A
  swap
  · have hA0 : A = ⊥ := by
      rw [not_nonempty_iff] at hne
      ext x; exact ⟨fun hx => (hne.false ⟨x, hx⟩).elim, fun hx => hx.elim⟩
    exact Hartshorne.bijective_map_homOfLE_of_eq _ _ (by rw [hA0, bot_inf_eq])
  have hη : genericPoint X ∈ U := hU _ (by
    rw [show X.presheaf.stalk (genericPoint X) = X.functionField from rfl,
      ringKrullDim_eq_zero_of_field]; exact zero_le_one)
  have hηA : genericPoint X ∈ A :=
    ((genericPoint_spec X).mem_open_set_iff A.isOpen).mpr (by simpa using hne)
  have : Nonempty (A ⊓ U : X.Opens) := ⟨⟨_, hηA, hη⟩⟩
  have hcomp : ∀ a, X.germToFunctionField (A ⊓ U)
      (X.presheaf.map (homOfLE (inf_le_left : A ⊓ U ≤ A)).op a) = X.germToFunctionField A a :=
    fun a => X.presheaf.germ_res_apply _ _ _ a
  refine ⟨fun a b h => X.germToFunctionField_injective A (by rw [← hcomp, ← hcomp, h]),
    fun f => ?_⟩
  have := functionField_isFractionRing_of_isAffineOpen X A hA
  have := isIntegrallyClosed_sections_of_isAffineOpen hA
  have : IsNoetherianRing Γ(X, A) := IsLocallyNoetherian.component_noetherian ⟨A, hA⟩
  have key : ∀ (P : Ideal Γ(X, A)) [P.IsPrime], P.height = 1 →
      X.germToFunctionField (A ⊓ U) f ∈ Localization.subalgebra.ofField X.functionField
        P.primeCompl P.primeCompl_le_nonZeroDivisors := by
    intro P _ hP
    let y : PrimeSpectrum Γ(X, A) := ⟨P, inferInstance⟩
    have hy : hA.fromSpec y ∈ A := hA.range_fromSpec.le ⟨y, rfl⟩
    let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hA.fromSpec y, hy⟩
    have hloc : IsLocalization.AtPrime (X.presheaf.stalk (hA.fromSpec y)) P :=
      hA.isLocalization_stalk' y hy
    have hyU : hA.fromSpec y ∈ U := hU _ (by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height P _, hP]; exact le_rfl)
    obtain ⟨⟨c, s⟩, hcs⟩ := IsLocalization.mk'_surjective P.primeCompl
      (X.presheaf.germ (A ⊓ U) _ ⟨hy, hyU⟩ f)
    refine ⟨c, s, s.2, ?_⟩
    have htower := functionField_isScalarTower (X := X) A ⟨hA.fromSpec y, hy⟩
    have hs0 : algebraMap Γ(X, A) X.functionField s ≠ 0 := by
      refine IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_of_ne_zero ?_)
      rintro h; exact s.2 (h ▸ P.zero_mem)
    rw [eq_mul_inv_iff_mul_eq₀ hs0,
      ← Scheme.algebraMap_germ_eq_germToFunctionField (X := X) (U := A ⊓ U) ⟨hy, hyU⟩,
      ← hcs, IsScalarTower.algebraMap_apply Γ(X, A) (X.presheaf.stalk (hA.fromSpec y))
        X.functionField s, ← map_mul, IsLocalization.mk'_spec_mk, ← IsScalarTower.algebraMap_apply]
  obtain ⟨a, ha⟩ := Hartshorne.exists_algebraMap_eq_of_forall_height_one (A := Γ(X, A))
    X.functionField (X.germToFunctionField (A ⊓ U) f) key
  exact ⟨a, X.germToFunctionField_injective (A ⊓ U) ((hcomp a).trans ha)⟩

/-- If the complement of `U` has codimension at least two, every point whose local ring has
dimension at most one lies in `U`. -/
theorem Scheme.mem_of_ringKrullDim_stalk_le_one {X : Scheme.{u}} {U : X.Opens}
    (hU : 2 ≤ Hartshorne.codim ((U : Set X)ᶜ)) {x : X}
    (hx : ringKrullDim (X.presheaf.stalk x) ≤ 1) :
    x ∈ U := by
  by_contra hxU
  let e : IrreducibleCloseds X ≃o X := irreducibleSetEquivPoints
  have h1 : Hartshorne.codim ((U : Set X)ᶜ) ≤ Order.coheight (e.symm x) :=
    iInf₂_le _ (by
      simpa [e] using closure_minimal (Set.singleton_subset_iff.mpr hxU) U.isOpen.isClosed_compl)
  rw [Order.coheight_orderIso] at h1
  rw [ringKrullDim_stalk_eq_coheight] at hx
  have h2 : Order.coheight x ≤ 1 := by exact_mod_cast hx
  have h3 := hU.trans (h1.trans h2)
  exact absurd h3 (by decide)

namespace Scheme.Modules

variable {Y : Scheme.{u}}

/-- Bijectivity of a restriction map is invariant under isomorphism of modules. -/
theorem bijective_presheaf_map_of_iso {M N : Y.Modules} (φ : M ≅ N) {V W : Y.Opens}
    (h : W ≤ V) (hM : Function.Bijective (M.presheaf.map (homOfLE h).op)) :
    Function.Bijective (N.presheaf.map (homOfLE h).op) := by
  have hnat : ∀ s, N.presheaf.map (homOfLE h).op (φ.hom.app V s) =
      φ.hom.app W (M.presheaf.map (homOfLE h).op s) := fun s => by
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
    exact (ConcreteCategory.congr_hom
      ((Scheme.Modules.Hom.mapPresheaf φ.hom).naturality (homOfLE h).op) s).symm
  have hφ : ∀ V : Y.Opens, Function.Bijective (φ.hom.app V) := fun V =>
    ConcreteCategory.bijective_of_isIso _
  rw [← Function.Bijective.of_comp_iff _ (hφ V)]
  have : (N.presheaf.map (homOfLE h).op) ∘ (φ.hom.app V) =
      (φ.hom.app W) ∘ (M.presheaf.map (homOfLE h).op) := funext hnat
  rw [this]
  exact (hφ W).comp hM

/-- Restriction maps commute with morphisms of modules. -/
theorem presheaf_map_app_apply {M N : Y.Modules} (g : M ⟶ N) {V W : Y.Opens} (h : W ≤ V)
    (s : Γ(M, V)) :
    N.presheaf.map (homOfLE h).op (g.app V s) = g.app W (M.presheaf.map (homOfLE h).op s) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
  exact (ConcreteCategory.congr_hom
    ((Scheme.Modules.Hom.mapPresheaf g).naturality (homOfLE h).op) s).symm

/-- The sections of a finite sum of morphisms of modules. -/
theorem sum_app_apply {M N : Y.Modules} {J : Type*} (t : Finset J) (g : J → (M ⟶ N))
    (V : Y.Opens) (x : Γ(M, V)) : (∑ j ∈ t, g j).app V x = ∑ j ∈ t, (g j).app V x := by
  induction t using Finset.cons_induction with
  | empty => simp
  | cons a t ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons, Hom.add_app, AddCommGrpCat.hom_add_apply, ih]

/-- If restriction `Γ(M_j, V) → Γ(M_j, W)` is bijective for each summand of a finite direct
sum, then it is bijective for the direct sum. -/
theorem bijective_presheaf_map_biproduct {J : Type*} [Fintype J] (f : J → Y.Modules)
    [HasBiproduct f]
    {V W : Y.Opens} (h : W ≤ V)
    (hf : ∀ j, Function.Bijective ((f j).presheaf.map (homOfLE h).op)) :
    Function.Bijective ((⨁ f).presheaf.map (homOfLE h).op) := by
  have htot : ∀ (V : Y.Opens) (s : Γ(⨁ f, V)),
      s = ∑ j, (biproduct.ι f j).app V ((biproduct.π f j).app V s) := by
    intro V s
    have := congrArg (fun g : ⨁ f ⟶ ⨁ f => AlgebraicGeometry.Scheme.Modules.Hom.app g V s)
      (IsBilimit.total (biproduct.isBilimit f))
    rw [sum_app_apply] at this
    simpa using this.symm
  refine ⟨fun s t hst => ?_, fun t => ?_⟩
  · have hj : ∀ j, (biproduct.π f j).app V s = (biproduct.π f j).app V t := fun j =>
      (hf j).1 (by rw [presheaf_map_app_apply, presheaf_map_app_apply, hst])
    rw [htot V s, htot V t]
    simp only [hj]
  · choose s hs using fun j => (hf j).2 ((biproduct.π f j).app W t)
    refine ⟨∑ j, (biproduct.ι f j).app V (s j), ?_⟩
    conv_rhs => rw [htot W t]
    rw [map_sum (ConcreteCategory.hom ((⨁ f).presheaf.map (homOfLE h).op))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [presheaf_map_app_apply, hs]

/-- Restriction of `M|_W` from `V` to `V ∩ U` is the restriction of `M` from the image of `V`
to its intersection with `U`. -/
theorem bijective_restrict_map_iff {X : Scheme.{u}} (M : X.Modules) (W U : X.Opens)
    (V : W.toScheme.Opens) :
    Function.Bijective ((M.restrict W.ι).presheaf.map
        (homOfLE (inf_le_left : V ⊓ W.ι ⁻¹ᵁ U ≤ V)).op) ↔
      Function.Bijective (M.presheaf.map
        (homOfLE (inf_le_left : W.ι ''ᵁ V ⊓ U ≤ W.ι ''ᵁ V)).op) := by
  have e : W.ι ''ᵁ (V ⊓ W.ι ⁻¹ᵁ U) = W.ι ''ᵁ V ⊓ U := by
    ext1
    simp [Set.image_inter_preimage]
  exact Hartshorne.bijective_map_homOfLE_congr M.presheaf (Scheme.Hom.image_mono _ inf_le_left)
    inf_le_left e

end Scheme.Modules

/-- **Sections of a finite locally free sheaf extend across codimension two**
(Hartshorne II.8, proof of Theorem 8.19). -/
theorem Scheme.Modules.bijective_presheaf_map_top_of_two_le_codim {X : Scheme.{u}} [IsIntegral X]
    [IsNoetherian X] [Hartshorne.IsNormal X] (U : X.Opens)
    (hU : 2 ≤ Hartshorne.codim ((U : Set X)ᶜ))
    (E : X.Modules) {r : ℕ} (hE : E.IsLocallyFreeOfRank r) :
    Function.Bijective (E.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op) := by
  have hU' : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 1 → x ∈ U :=
    fun x hx => Scheme.mem_of_ringKrullDim_stalk_le_one hU hx
  have := Abelian.hasFiniteBiproducts (C := X.Modules)
  have hloc : ∀ W₀ : X.Opens, ∀ x ∈ W₀, ∃ A : X.Opens, A ≤ W₀ ∧ x ∈ A ∧
      Function.Bijective (E.presheaf.map (homOfLE (inf_le_left : A ⊓ U ≤ A)).op) := by
    intro W₀ x hx
    obtain ⟨W, hxW, ⟨α⟩⟩ := hE x
    obtain ⟨_, ⟨A, hA, rfl⟩, hxA, hAsub⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open
        (show x ∈ ((W₀ ⊓ W : X.Opens) : Set X) from ⟨hx, hxW⟩) (W₀ ⊓ W).2
    refine ⟨A, fun y hy => (hAsub hy).1, hxA, ?_⟩
    have hAW : A ≤ W := fun y hy => (hAsub hy).2
    obtain ⟨V, rfl⟩ : ∃ V : W.toScheme.Opens, W.ι ''ᵁ V = A :=
      ⟨W.ι ⁻¹ᵁ A, by
        rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
          inf_eq_right.2 hAW]⟩
    rw [← Scheme.Modules.bijective_restrict_map_iff]
    let I := ULift.{u} (Fin r)
    refine Scheme.Modules.bijective_presheaf_map_of_iso
      ((α ≪≫ (Scheme.Modules.restrictFreeIso W.ι I).symm).symm) _
      ((Scheme.Modules.bijective_restrict_map_iff (SheafOfModules.free I : X.Modules) W U V).2 ?_)
    have hunit : Function.Bijective (Scheme.Modules.presheaf
        (SheafOfModules.unit X.ringCatSheaf : X.Modules) |>.map
        (homOfLE (inf_le_left : W.ι ''ᵁ V ⊓ U ≤ W.ι ''ᵁ V)).op) :=
      Scheme.bijective_presheaf_map_inf_of_isAffineOpen U hU' hA
    let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
    have hsum := Scheme.Modules.bijective_presheaf_map_biproduct (fun _ : I => O)
      (inf_le_left : W.ι ''ᵁ V ⊓ U ≤ W.ι ''ᵁ V) fun _ => hunit
    let β : (⨁ fun _ : I => O) ≅ (SheafOfModules.free I : X.Modules) :=
      biproduct.isoCoproduct _
    exact Scheme.Modules.bijective_presheaf_map_of_iso β _ hsum
  exact (Hartshorne.bijective_map_homOfLE_congr _ _ _ (top_inf_eq U)).1
    (Hartshorne.bijective_map_inf_of_forall_exists ⟨E.presheaf, E.isSheaf⟩ U hloc ⊤)

end AlgebraicGeometry

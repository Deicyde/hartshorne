/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Localization.Finiteness
import Hartshorne.Scheme.CoherentAffineLocalCriterion
import Hartshorne.Scheme.CoherentFreeLocus

/-!
# The fibre dimension of a coherent sheaf is upper semicontinuous

Hartshorne, *Algebraic Geometry*, III Example 12.7.2 (p. 288).

For an `𝒪_Y`-module `G` and `y ∈ Y`, the *fibre dimension* of `G` at `y` is
`dim_{k(y)} (G_y ⊗_{𝒪_{Y,y}} k(y))`, where `G_y` carries its `𝒪_{Y,y}`-module structure as the
stalk of a presheaf of modules.  For a coherent `G` this function is upper semicontinuous: every
point has an open neighbourhood on which the fibre dimension is at most its value at the point,
and equivalently, for every integer `n`, the locus where it is at least `n` is closed.

The proof is local on an affine open `U = Spec A` containing `y`, where `M = Γ(U, G)` is a finite
`A`-module.  We first show that for `x ∈ U` the germ map `M → G_x` is the localization of `M` at
the prime of `A` corresponding to `x` (the restriction maps of `G|_U ≅ M~` to principal opens are
localizations).  Then, by Nakayama's lemma, a basis of the fibre at `y` lifts to elements
`m₁, …, m_d` of `M` generating `M_y`; some `f ∈ A` invertible at `y` multiplies `M` into the span
of the `mᵢ`, so the `mᵢ` generate every stalk on the principal open `D(f)`, and the fibre
dimension there is at most `d`.

Coherence (the project's `IsCoherent`) is used through the finite generation of sections on
affine opens, which does not need the Noetherian hypothesis; the statements for a Noetherian
base, as in Hartshorne, are recorded separately.
-/

open TensorProduct IsLocalRing

namespace Hartshorne

namespace FiberDimAux

variable {S N : Type*} [CommRing S] [IsLocalRing S] [AddCommGroup N] [Module S N]

/-- If finitely many elements span a finite module over a local ring, the fibre has dimension at
most their number. -/
theorem finrank_fiber_le_of_span_eq_top [Module.Finite S N] {ι : Type*} [Fintype ι]
    (v : ι → N) (hv : Submodule.span S (Set.range v) = ⊤) :
    Module.finrank (ResidueField S) (ResidueField S ⊗[S] N) ≤ Fintype.card ι := by
  apply finrank_le_of_span_eq_top (v := fun i ↦ (1 : ResidueField S) ⊗ₜ[S] v i)
  have h := (map_tensorProduct_mk_eq_top (R := S) (M := N) (N := Submodule.span S (Set.range v))).mpr hv
  rw [Submodule.map_span, ← Submodule.restrictScalars_span S (ResidueField S)
    Ideal.Quotient.mk_surjective, Submodule.restrictScalars_eq_top_iff, ← Set.range_comp] at h
  exact h

/-- A finite module over a local ring is spanned by as many elements as the dimension of its
fibre. -/
theorem exists_span_eq_top_fin_finrank [Module.Finite S N] :
    ∃ v : Fin (Module.finrank (ResidueField S) (ResidueField S ⊗[S] N)) → N,
      Submodule.span S (Set.range v) = ⊤ := by
  let b := Module.finBasis (ResidueField S) (ResidueField S ⊗[S] N)
  have hsurj : Function.Surjective (TensorProduct.mk S (ResidueField S) N 1) := by
    have h := (map_tensorProduct_mk_eq_top (R := S) (M := N) (N := ⊤)).mpr rfl
    rw [Submodule.map_top, LinearMap.range_eq_top] at h
    exact h
  choose v hv using fun i ↦ hsurj (b i)
  exact ⟨v, span_eq_top_of_tmul_eq_basis v b hv⟩


variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

/-- At a point `y`: lifting a minimal generating set of `M_y` to `M`, some `f ∉ 𝔭_y` multiplies
`M` into the span of the lifts. -/
theorem exists_smul_mem_span [Module.Finite A M] (p : Ideal A) [p.IsPrime]
    [Algebra A S] [IsLocalization.AtPrime S p] [Module A N] [IsScalarTower A S N]
    (g : M →ₗ[A] N) [IsLocalizedModule p.primeCompl g] :
    ∃ (m : Fin (Module.finrank (ResidueField S) (ResidueField S ⊗[S] N)) → M) (f : A),
      f ∉ p ∧ ∀ x : M, f • x ∈ Submodule.span A (Set.range m) := by
  classical
  have : Module.Finite S N := Module.Finite.of_isLocalizedModule p.primeCompl g
  obtain ⟨v, hv⟩ := exists_span_eq_top_fin_finrank (S := S) (N := N)
  choose ms hms using fun i ↦ IsLocalizedModule.surj p.primeCompl g (v i)
  let m : Fin _ → M := fun i ↦ (ms i).1
  have hspan : Submodule.span S (Set.range (g ∘ m)) = ⊤ := by
    rw [eq_top_iff, ← hv, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨u, hu⟩ := IsLocalization.map_units S (ms i).2
    have : v i = (↑u⁻¹ : S) • g (m i) := by
      rw [← hms i, Submonoid.smul_def, ← algebraMap_smul S ((ms i).2 : A) (v i), ← hu, smul_smul,
        Units.inv_mul, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have key : ∀ x : M, ∃ c : p.primeCompl, (c : A) • x ∈ Submodule.span A (Set.range m) := by
    intro x
    have hx : g x ∈ Submodule.span S (Set.range (g ∘ m)) := hspan ▸ Submodule.mem_top
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span p.primeCompl S _ _ hx
    rw [Set.range_comp, ← Submodule.map_span] at ht
    obtain ⟨y, hy, hyx⟩ := ht
    rw [Submonoid.smul_def, ← map_smul] at hyx
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := p.primeCompl) hyx
    refine ⟨c * t, ?_⟩
    rw [Submonoid.coe_mul, mul_smul, ← Submonoid.smul_def c ((t : A) • x), ← hc]
    exact Submodule.smul_mem _ _ hy
  choose c hc using key
  obtain ⟨T, hT⟩ := Module.Finite.fg_top (R := A) (M := M)
  let fS : p.primeCompl := ∏ x ∈ T, c x
  refine ⟨m, fS, fS.2, fun x ↦ ?_⟩
  have hle : (⊤ : Submodule A M) ≤
      (Submodule.span A (Set.range m)).comap ((fS : A) • LinearMap.id) := by
    rw [← hT, Submodule.span_le]
    intro x hx
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_coe, id]
    rw [show fS = (∏ x' ∈ T.erase x, c x') * c x from (Finset.prod_erase_mul T c hx).symm,
      Submonoid.coe_mul, mul_smul]
    exact Submodule.smul_mem _ _ (hc x)
  simpa using hle (Submodule.mem_top (x := x))

/-- At a point `z` where `f` is invertible: the lifts span `M_z`, so the fibre dimension at `z`
is at most their number. -/
theorem finrank_fiber_le_of_smul_mem_span [Module.Finite A M] (p : Ideal A) [p.IsPrime]
    [Algebra A S] [IsLocalization.AtPrime S p] [Module A N] [IsScalarTower A S N]
    (g : M →ₗ[A] N) [IsLocalizedModule p.primeCompl g] {d : ℕ} (m : Fin d → M) (f : A)
    (hfp : f ∉ p) (hf : ∀ x : M, f • x ∈ Submodule.span A (Set.range m)) :
    Module.finrank (ResidueField S) (ResidueField S ⊗[S] N) ≤ d := by
  have : Module.Finite S N := Module.Finite.of_isLocalizedModule p.primeCompl g
  have hspan : Submodule.span S (Set.range (g ∘ m)) = ⊤ := by
    rw [eq_top_iff]
    intro n _
    obtain ⟨⟨x, s⟩, hs⟩ := IsLocalizedModule.surj p.primeCompl g n
    let fs : p.primeCompl := ⟨f, hfp⟩ * s
    obtain ⟨u, hu⟩ := IsLocalization.map_units S fs
    have hmem : g (f • x) ∈ Submodule.span S (Set.range (g ∘ m)) := by
      have h := Submodule.mem_map_of_mem (f := g) (hf x)
      rw [Submodule.map_span, ← Set.range_comp] at h
      exact Submodule.span_subset_span A S _ h
    have : n = (↑u⁻¹ : S) • g (f • x) := by
      rw [map_smul, ← hs, Submonoid.smul_def, smul_smul, ← algebraMap_smul S (f * (s : A)) n]
      change n = (↑u⁻¹ : S) • algebraMap A S (fs : A) • n
      rw [← hu, smul_smul, Units.inv_mul, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ hmem
  simpa using finrank_fiber_le_of_span_eq_top (g ∘ m) hspan

end FiberDimAux


open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace FiberDimAux

variable {X : Scheme.{u}} (F : X.Modules) {U : X.Opens} (hU : IsAffineOpen U)

theorem fromSpec_image_basicOpen_le (f : Γ(X, U)) :
    hU.fromSpec ''ᵁ PrimeSpectrum.basicOpen f ≤ U := by
  rw [hU.fromSpec_image_basicOpen]
  exact X.basicOpen_le f

/-- Compatibility of the two ways of mapping `Γ(X, U)` to the sections over the image of a
principal open of `Spec Γ(X, U)`. -/
theorem ring_compat_basicOpen (f : Γ(X, U)) :
    (Scheme.ΓSpecIso Γ(X, U)).inv ≫
      (Spec Γ(X, U)).presheaf.map (PrimeSpectrum.basicOpen f).leTop.op ≫
        (hU.fromSpec.appIso (PrimeSpectrum.basicOpen f)).inv =
      X.presheaf.map (homOfLE (fromSpec_image_basicOpen_le hU f)).op := by
  have h2 := hU.fromSpec.appIso_inv_naturality
    (Opens.leTop (PrimeSpectrum.basicOpen f : (Spec Γ(X, U)).Opens)).op
  have h3 := CoherentAux.ring_compat hU
  have h4 : (Spec Γ(X, U)).presheaf.map (⊤ : (Spec Γ(X, U)).Opens).leTop.op = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_id]
    rfl
  rw [h4, Category.id_comp] at h3
  erw [h2]
  rw [← Category.assoc, h3, ← Functor.map_comp]
  rfl

/-- The `Γ(X, U)`-module structure on a stalk at a point of `U`, through the germ map. -/
noncomputable abbrev stalkModuleSections (x : U) :
    Module Γ(X, U) (F.presheaf.stalk (x : X)) :=
  Module.compHom _ (algebraMap Γ(X, U) (X.presheaf.stalk (x : X)))

attribute [local instance] stalkModuleSections

theorem isScalarTower_stalk (x : U) :
    IsScalarTower Γ(X, U) (X.presheaf.stalk (x : X)) (F.presheaf.stalk (x : X)) :=
  IsScalarTower.of_compHom _ _ _

attribute [local instance] isScalarTower_stalk

/-- The germ map `Γ(U, F) → F_x`, as a map of `Γ(X, U)`-modules. -/
noncomputable def germₗ (x : U) : Γ(F, U) →ₗ[Γ(X, U)] F.presheaf.stalk (x : X) where
  toFun := F.presheaf.germ U x x.2
  map_add' := map_add _
  map_smul' r m := schemeModules_germ_smul F U (x : X) x.2 r m

theorem germₗ_apply (x : U) (m : Γ(F, U)) : germₗ F x m = F.presheaf.germ U x x.2 m := rfl

/-- **Stalks of a quasi-coherent sheaf on an affine open are localizations.**  If
`F|_U ≅ Γ(U, F)~` on an affine open `U`, then for `x ∈ U` the germ map `Γ(U, F) → F_x`
is the localization at the prime ideal of `Γ(X, U)` corresponding to `x`. -/
theorem isLocalizedModule_germₗ (hiso : IsIso (F.restrict hU.fromSpec).fromTildeΓ) (x : U) :
    IsLocalizedModule (hU.primeIdealOf x).asIdeal.primeCompl (germₗ F x) := by
  have := hU.isLocalization_stalk x
  have hloc := (isIso_fromTildeΓ_iff_isLocalizing (F.restrict hU.fromSpec)).mp hiso
  let e := CoherentAux.sectionsEquiv F hU
  let ρ (f : Γ(X, U)) : Γ(F.restrict hU.fromSpec, ⊤) →ₗ[Γ(X, U)]
      Γ(F.restrict hU.fromSpec, CoherentAux.D f) :=
    ((modulesSpecToSheaf.obj (F.restrict hU.fromSpec)).obj.map (CoherentAux.D f).leTop.op).hom
  have hρ (f : Γ(X, U)) : IsLocalizedModule (Submonoid.powers f) (ρ f) := hloc f
  have hres (f : Γ(X, U)) (m : Γ(F, U)) :
      ρ f (e m) = F.presheaf.map (homOfLE (fromSpec_image_basicOpen_le hU f)).op m := by
    change F.presheaf.map _ (F.presheaf.map _ m) = _
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  have hsmul (f a : Γ(X, U)) (t : Γ(F.restrict hU.fromSpec, CoherentAux.D f)) :
      (a • t : Γ(F.restrict hU.fromSpec, CoherentAux.D f)) =
        (X.presheaf.map (homOfLE (fromSpec_image_basicOpen_le hU f)).op a •
          (show Γ(F, hU.fromSpec ''ᵁ CoherentAux.D f) from t) :) := by
    rw [Scheme.Modules.smul_Spec_def, ← ring_compat_basicOpen hU f]
    rfl
  have hprime (f : Γ(X, U)) (hxf : (x : X) ∈ X.basicOpen f) :
      f ∈ (hU.primeIdealOf x).asIdeal.primeCompl := by
    rw [← IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk (x : X))]
    exact (X.mem_basicOpen' f x).mp hxf
  refine ⟨fun s ↦ ?_, fun y ↦ ?_, fun {m₁ m₂} h ↦ ?_⟩
  · obtain ⟨u, hu⟩ := IsLocalization.map_units (X.presheaf.stalk (x : X)) s
    rw [Module.End.isUnit_iff]
    refine Function.bijective_iff_has_inverse.mpr ⟨fun y ↦ (↑u⁻¹ : X.presheaf.stalk (x : X)) • y,
      fun y ↦ ?_, fun y ↦ ?_⟩
    · simp only [Module.algebraMap_end_apply]
      rw [← algebraMap_smul (X.presheaf.stalk (x : X)) (s : Γ(X, U)) y, ← hu, smul_smul,
        Units.inv_mul, one_smul]
    · simp only [Module.algebraMap_end_apply]
      rw [← algebraMap_smul (X.presheaf.stalk (x : X)) (s : Γ(X, U)), ← hu, smul_smul,
        Units.mul_inv, one_smul]
  · obtain ⟨V, hxV, t, rfl⟩ := F.presheaf.exists_germ_eq y
    obtain ⟨f, hfV, hxf⟩ := hU.exists_basicOpen_le ⟨(x : X), hxV⟩ x.2
    have hWV : hU.fromSpec ''ᵁ CoherentAux.D f ≤ V :=
      (hU.fromSpec_image_basicOpen f).trans_le hfV
    have hxW : (x : X) ∈ hU.fromSpec ''ᵁ CoherentAux.D f := by
      rw [hU.fromSpec_image_basicOpen f]
      exact hxf
    have := hρ f
    let t' : Γ(F.restrict hU.fromSpec, CoherentAux.D f) := F.presheaf.map (homOfLE hWV).op t
    obtain ⟨⟨s', c⟩, hc⟩ := IsLocalizedModule.surj (Submonoid.powers f) (ρ f) t'
    obtain ⟨n, hn⟩ := c.2
    refine ⟨⟨e.symm s', ⟨f ^ n, pow_mem (hprime f hxf) n⟩⟩, ?_⟩
    have h1 : germₗ F x (e.symm s') = F.presheaf.germ _ (x : X) hxW
        (F.presheaf.map (homOfLE (fromSpec_image_basicOpen_le hU f)).op (e.symm s')) := by
      rw [germₗ_apply, TopCat.Presheaf.germ_res_apply]
    have hn' : f ^ n = (c : Γ(X, U)) := hn
    have key := congrArg (F.presheaf.germ _ (x : X) hxW) (hc.symm.trans (hsmul f c t'))
    rw [h1, ← hres, e.apply_symm_apply]
    refine Eq.trans ?_ key.symm
    rw [schemeModules_germ_smul, TopCat.Presheaf.germ_res_apply]
    change _ = _ • F.presheaf.germ _ (x : X) hxW (F.presheaf.map (homOfLE hWV).op t)
    rw [TopCat.Presheaf.germ_res_apply, ← hn']
    rfl
  · obtain ⟨V, hxV, iU, iV, hV⟩ := F.presheaf.germ_eq (x : X) x.2 x.2 m₁ m₂ h
    obtain ⟨f, hfV, hxf⟩ := hU.exists_basicOpen_le ⟨(x : X), hxV⟩ x.2
    have hWV : hU.fromSpec ''ᵁ CoherentAux.D f ≤ V :=
      (hU.fromSpec_image_basicOpen f).trans_le hfV
    have := hρ f
    have k (m : Γ(F, U)) (i : V ⟶ U) :
        F.presheaf.map (homOfLE (fromSpec_image_basicOpen_le hU f)).op m =
          F.presheaf.map (homOfLE hWV).op (F.presheaf.map i.op m) := by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    have h' : ρ f (e m₁) = ρ f (e m₂) := by
      rw [hres, hres, k m₁ iU, k m₂ iV, hV]
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers f) h'
    obtain ⟨n, hn⟩ := c.2
    refine ⟨⟨f ^ n, pow_mem (hprime f hxf) n⟩, e.injective ?_⟩
    have hn' : f ^ n = (c : Γ(X, U)) := hn
    simp only [Submonoid.smul_def] at hc ⊢
    rw [map_smul, map_smul, hn']
    exact hc

end FiberDimAux

open FiberDimAux

attribute [local instance] FiberDimAux.stalkModuleSections FiberDimAux.isScalarTower_stalk

/-- The **fibre dimension** of an `𝒪_X`-module `F` at `x`:
`dim_{k(x)} (F_x ⊗_{𝒪_{X,x}} k(x))`, where `k(x)` is the residue field of `𝒪_{X,x}`. -/
noncomputable def moduleFiberDim {X : Scheme.{u}} (F : X.Modules) (x : X) : ℕ :=
  Module.finrank (ResidueField (X.presheaf.stalk x))
    (ResidueField (X.presheaf.stalk x) ⊗[X.presheaf.stalk x] F.presheaf.stalk x)

/-- **Upper semicontinuity of the fibre dimension of a coherent sheaf**, neighbourhood form.
For a coherent `𝒪_Y`-module `G`, every `y ∈ Y` has an open neighbourhood on which the fibre
dimension of `G` is at most its value at `y`.  No Noetherian hypothesis is needed. -/
theorem exists_nhds_moduleFiberDim_le_of_isCoherent {Y : Scheme.{u}} (G : Y.Modules)
    (hG : IsCoherent G) (y : Y) :
    ∃ U : Y.Opens, y ∈ U ∧ ∀ y' ∈ U, moduleFiberDim G y' ≤ moduleFiberDim G y := by
  obtain ⟨_, ⟨U, hU', rfl⟩, hyU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hU : IsAffineOpen U := hU'
  have hiso : IsIso (G.restrict hU.fromSpec).fromTildeΓ :=
    (forall_affine_finite_of_isCoherent G hG ⟨U, hU⟩).2
  have : Module.Finite Γ(Y, U) Γ(G, U) := (forall_affine_finite_of_isCoherent G hG ⟨U, hU⟩).1
  have hunit (x : U) (f : Γ(Y, U)) :
      (x : Y) ∈ Y.basicOpen f ↔ f ∉ (hU.primeIdealOf x).asIdeal := by
    have := hU.isLocalization_stalk x
    rw [Y.mem_basicOpen' f x]
    exact IsLocalization.AtPrime.isUnit_to_map_iff (Y.presheaf.stalk (x : Y)) _ f
  obtain ⟨x, rfl⟩ : ∃ x : U, (x : Y) = y := ⟨⟨y, hyU⟩, rfl⟩
  have := hU.isLocalization_stalk x
  have := isLocalizedModule_germₗ G hU hiso x
  obtain ⟨m, f, hfp, hf⟩ := exists_smul_mem_span (S := Y.presheaf.stalk (x : Y))
    (N := G.presheaf.stalk (x : Y)) (hU.primeIdealOf x).asIdeal (germₗ G x)
  refine ⟨Y.basicOpen f, (hunit x f).mpr hfp, fun y' hy' ↦ ?_⟩
  obtain ⟨x', rfl⟩ : ∃ x' : U, (x' : Y) = y' := ⟨⟨y', Y.basicOpen_le f hy'⟩, rfl⟩
  have := hU.isLocalization_stalk x'
  have := isLocalizedModule_germₗ G hU hiso x'
  exact finrank_fiber_le_of_smul_mem_span (hU.primeIdealOf x').asIdeal (germₗ G x') m f
    ((hunit x' f).mp hy') hf

/-- **Upper semicontinuity of the fibre dimension of a coherent sheaf**, closed-set form.
For a coherent `𝒪_Y`-module `G` and every integer `n`, the locus where the fibre dimension of
`G` is at least `n` is closed.  No Noetherian hypothesis is needed. -/
theorem isClosed_setOf_le_moduleFiberDim_of_isCoherent {Y : Scheme.{u}} (G : Y.Modules)
    (hG : IsCoherent G) (n : ℤ) :
    IsClosed {y : Y | n ≤ (moduleFiberDim G y : ℤ)} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro y hy
  obtain ⟨U, hyU, hU⟩ := exists_nhds_moduleFiberDim_le_of_isCoherent G hG y
  refine ⟨U, fun y' hy' ↦ ?_, U.isOpen, hyU⟩
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hy ⊢
  exact lt_of_le_of_lt (by exact_mod_cast hU y' hy') hy

/-- **Hartshorne III Example 12.7.2**, neighbourhood form.  For a coherent sheaf `G` on a
Noetherian scheme `Y`, every `y ∈ Y` has an open neighbourhood on which the fibre dimension
`dim_{k(y')} (G_{y'} ⊗ k(y'))` is at most its value at `y`.  The Noetherian hypothesis is the
source's setting; see `exists_nhds_moduleFiberDim_le_of_isCoherent` for the general statement. -/
theorem exists_nhds_moduleFiberDim_le_of_isCoherent_of_isNoetherian {Y : Scheme.{u}}
    [_hY : IsNoetherian Y] (G : Y.Modules) (hG : IsCoherent G) (y : Y) :
    ∃ U : Y.Opens, y ∈ U ∧ ∀ y' ∈ U, moduleFiberDim G y' ≤ moduleFiberDim G y :=
  exists_nhds_moduleFiberDim_le_of_isCoherent G hG y

/-- **Hartshorne III Example 12.7.2**, closed-set form.  For a coherent sheaf `G` on a
Noetherian scheme `Y` and every integer `n`, the locus `{y | dim_{k(y)} (G_y ⊗ k(y)) ≥ n}` is
closed.  The Noetherian hypothesis is the source's setting; see
`isClosed_setOf_le_moduleFiberDim_of_isCoherent` for the general statement. -/
theorem isClosed_setOf_le_moduleFiberDim_of_isCoherent_of_isNoetherian {Y : Scheme.{u}}
    [_hY : IsNoetherian Y] (G : Y.Modules) (hG : IsCoherent G) (n : ℤ) :
    IsClosed {y : Y | n ≤ (moduleFiberDim G y : ℤ)} :=
  isClosed_setOf_le_moduleFiberDim_of_isCoherent G hG n

end Hartshorne

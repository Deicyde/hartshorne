/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.CoherentFreeLocus
import Hartshorne.Scheme.FibreDimensionFree
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.RingTheory.Localization.Finiteness

/-!
# Constant fibre dimension and local freeness of coherent sheaves

Let `X` be a reduced locally Noetherian scheme and `F` a coherent `𝒪_X`-module. Then `F` is
locally free of rank `n` if and only if every fibre `F_x ⊗ k(x)` has dimension `n` over the
residue field `k(x)` (Hartshorne II, Exercise 5.8(c), stated there for Noetherian `X`, in the
direction from constant fibre dimension to local freeness). The direction from local freeness
to the fibre dimension holds on any scheme.

The proof is local. On an affine open `Spec A ⊆ X` (with `A` reduced) the stalk `F_y` at a
prime `y` is the localization of the finite `A`-module `N = Γ(Spec A, F)`. For a prime `P` of
`𝒪_{X,y}` lying over the prime `q` of `A`, the fibre `κ(P) ⊗ F_y` has the dimension of
`κ(q) ⊗_A N`, which is the fibre of `F` at the point `q`. Constant fibre dimension thus makes
every fibre of the module `F_y` over the reduced local ring `𝒪_{X,y}` have the same dimension,
which forces `F_y` to be free; the free locus of a coherent sheaf then gives local freeness.

Fibre dimensions are transported along open immersions by
`rank_tensorProduct_eq_of_ringEquiv`, which compares base changes along compatible ring
isomorphisms.
-/

open CategoryTheory TopologicalSpace Opposite TensorProduct IsLocalRing Module

namespace Hartshorne

open AlgebraicGeometry

universe u

noncomputable section

/-- Base changes along compatible ring isomorphisms have the same rank: if `σ : R ≃+* R'` and
`τ : S ≃+* S'` are compatible with the algebra maps, and `e : M ≃+ M'` is `σ`-semilinear, then
`rank_S (S ⊗[R] M) = rank_{S'} (S' ⊗[R'] M')`. -/
theorem rank_tensorProduct_eq_of_ringEquiv {R R' S S' M M' : Type u} [CommRing R] [CommRing R']
    [CommRing S] [CommRing S'] [Algebra R S] [Algebra R' S'] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R' M'] (σ : R ≃+* R') (τ : S ≃+* S')
    (hτ : ∀ r, τ (algebraMap R S r) = algebraMap R' S' (σ r)) (e : M ≃+ M')
    (he : ∀ (r : R) (m : M), e (r • m) = σ r • e m) :
    Module.rank S (S ⊗[R] M) = Module.rank S' (S' ⊗[R'] M') := by
  have hτ' : ∀ r', τ.symm (algebraMap R' S' r') = algebraMap R S (σ.symm r') := by
    intro r'
    rw [RingEquiv.symm_apply_eq, hτ, RingEquiv.apply_symm_apply]
  have he' : ∀ (r' : R') (m' : M'), e.symm (r' • m') = σ.symm r' • e.symm m' := by
    intro r' m'
    rw [AddEquiv.symm_apply_eq, he, RingEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  let φ : S ⊗[R] M →+ S' ⊗[R'] M' := TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun s => AddMonoidHom.mk' (fun m => τ s ⊗ₜ[R'] e m)
      (fun a b => by simp [TensorProduct.tmul_add]))
      (fun a b => by ext m; simp [TensorProduct.add_tmul]))
    (fun r s m => by
      simp only [AddMonoidHom.mk'_apply]
      rw [Algebra.smul_def, map_mul, hτ, ← Algebra.smul_def, he, TensorProduct.smul_tmul])
  let ψ : S' ⊗[R'] M' →+ S ⊗[R] M := TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun s => AddMonoidHom.mk' (fun m => τ.symm s ⊗ₜ[R] e.symm m)
      (fun a b => by simp [TensorProduct.tmul_add]))
      (fun a b => by ext m; simp [TensorProduct.add_tmul]))
    (fun r s m => by
      simp only [AddMonoidHom.mk'_apply]
      rw [Algebra.smul_def, map_mul, hτ', ← Algebra.smul_def, he', TensorProduct.smul_tmul])
  have hφ (s : S) (m : M) : φ (s ⊗ₜ m) = τ s ⊗ₜ e m := rfl
  have hψ (s : S') (m : M') : ψ (s ⊗ₜ m) = τ.symm s ⊗ₜ e.symm m := rfl
  let j : S ⊗[R] M ≃+ S' ⊗[R'] M' :=
    { toFun := φ
      invFun := ψ
      left_inv := fun t => by
        induction t using TensorProduct.induction_on with
        | zero => simp
        | tmul s m => rw [hφ, hψ]; simp
        | add a b ha hb => rw [map_add, map_add, ha, hb]
      right_inv := fun t => by
        induction t using TensorProduct.induction_on with
        | zero => simp
        | tmul s m => rw [hψ, hφ]; simp
        | add a b ha hb => rw [map_add, map_add, ha, hb]
      map_add' := map_add φ }
  refine _root_.rank_eq_of_equiv_equiv τ j τ.bijective (fun s t => ?_)
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    change φ (s • a ⊗ₜ m) = τ s • φ (a ⊗ₜ m)
    rw [TensorProduct.smul_tmul', hφ, hφ, smul_eq_mul, map_mul, TensorProduct.smul_tmul',
      smul_eq_mul]
  | add a b ha hb => rw [smul_add, map_add, map_add, ha, hb, smul_add]

open FreeLocusAux

/-- The fibre `F_x ⊗ k(x)` of an `𝒪_X`-module can be computed after restricting along an open
immersion: it has the same dimension as the fibre of the restriction. -/
theorem rank_fibre_restrict {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] (M : X.Modules)
    (y : Y) :
    Module.rank (ResidueField (X.presheaf.stalk (f y)))
        (ResidueField (X.presheaf.stalk (f y)) ⊗[X.presheaf.stalk (f y)]
          M.presheaf.stalk (f y)) =
      Module.rank (ResidueField (Y.presheaf.stalk y))
        (ResidueField (Y.presheaf.stalk y) ⊗[Y.presheaf.stalk y]
          (M.restrict f).presheaf.stalk y) := by
  let φ := restrictStalkIso f M y
  let σ := stalkRingEquiv f y
  refine rank_tensorProduct_eq_of_ringEquiv σ (ResidueField.mapEquiv σ) (fun r => ?_)
    { toFun := φ.inv
      invFun := φ.hom
      left_inv := φ.inv_hom_id_apply
      right_inv := φ.hom_inv_id_apply
      map_add' := map_add _ } (fun a m => ?_)
  · simp [ResidueField.algebraMap_eq, ResidueField.map_residue]
  · change φ.inv (a • m) = σ a • φ.inv m
    calc φ.inv (a • m) = φ.inv (φ.hom (σ a • φ.inv m)) := by
          rw [restrictStalkIso_hom_smul, RingEquiv.symm_apply_apply, φ.inv_hom_id_apply]
      _ = σ a • φ.inv m := φ.hom_inv_id_apply _

/-- `finrank` form of `rank_fibre_restrict`. -/
theorem finrank_fibre_restrict {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) (y : Y) :
    finrank (ResidueField (X.presheaf.stalk (f y)))
        (ResidueField (X.presheaf.stalk (f y)) ⊗[X.presheaf.stalk (f y)]
          M.presheaf.stalk (f y)) =
      finrank (ResidueField (Y.presheaf.stalk y))
        (ResidueField (Y.presheaf.stalk y) ⊗[Y.presheaf.stalk y]
          (M.restrict f).presheaf.stalk y) :=
  congrArg Cardinal.toNat (rank_fibre_restrict f M y)

attribute [local instance] freeLocusStalkAlgebra freeLocus_asIdeal_isPrime
  freeLocus_stalk_isLocalization freeLocusStalkModule freeLocus_stalk_isScalarTower

/-- The stalks of a free module sheaf `𝒪 ^ (⊕ I)` on an affine scheme have bases indexed by
`I`. -/
theorem nonempty_basis_stalk_of_iso_free_spec {R : CommRingCat.{u}} (I : Type u)
    (G : (Spec R).Modules) (hG : G ≅ SheafOfModules.free I) (y : Spec R) :
    Nonempty (Basis I ((Spec R).presheaf.stalk y) (G.presheaf.stalk y)) := by
  have : IsIso (Scheme.Modules.fromTildeΓ (R := R) G) :=
    isIso_fromTildeΓ_iff.mpr ⟨_, ⟨tildeFinsupp I ≪≫ hG.symm⟩⟩
  have hloc : IsLocalizing (modulesSpecToSheaf.obj G) :=
    (isIso_fromTildeΓ_iff_isLocalizing _).mp this
  have := isLocalizedModule_germTopLinear G hloc y
  let e : Γ(G, ⊤) ≃ₗ[R] (I →₀ R) :=
    (moduleSpecΓFunctor.mapIso (hG ≪≫ (tildeFinsupp I).symm) ≪≫
      (tilde.toTildeΓNatIso.app (ModuleCat.of R (I →₀ R))).symm).toLinearEquiv
  exact ⟨(Basis.ofRepr e).ofIsLocalizedModule _ y.asIdeal.primeCompl (germTopLinear G y)⟩

/-- If `F|_U ≅ 𝒪_U ^ (⊕ I)` and `x ∈ U`, then the fibre `F_x ⊗ k(x)` has dimension `#I`. -/
theorem rank_fibre_of_restrict_iso_free {X : Scheme.{u}} (F : X.Modules) {U : X.Opens}
    {I : Type u} (α : F.restrict U.ι ≅ SheafOfModules.free I) {x : X} (hx : x ∈ U) :
    Module.rank (ResidueField (X.presheaf.stalk x))
        (ResidueField (X.presheaf.stalk x) ⊗[X.presheaf.stalk x] F.presheaf.stalk x) =
      Cardinal.mk I := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
  replace hVU : V ≤ U := hVU
  let j : Spec Γ(X, V) ⟶ U := hV.isoSpec.inv ≫ X.homOfLE hVU
  have hj : j ≫ U.ι = hV.fromSpec := by simp [j]; rfl
  have : IsOpenImmersion hV.fromSpec := hV.isOpenImmersion_fromSpec
  let β : F.restrict hV.fromSpec ≅ SheafOfModules.free I :=
    (Scheme.Modules.restrictFunctorCongr hj).symm.app F ≪≫
      (Scheme.Modules.restrictFunctorComp j U.ι).app F ≪≫
      (Scheme.Modules.restrictFunctor j).mapIso α ≪≫ Scheme.Modules.restrictFreeIso j I
  obtain ⟨y, rfl⟩ : x ∈ Set.range hV.fromSpec := by rwa [hV.range_fromSpec]
  rw [rank_fibre_restrict hV.fromSpec F y]
  obtain ⟨b⟩ := nonempty_basis_stalk_of_iso_free_spec I _ β y
  exact ((b.baseChange _).mk_eq_rank'').symm

/-- On a locally free module of rank `n`, every fibre `F_x ⊗ k(x)` has dimension `n`. -/
theorem finrank_fibre_of_isLocallyFreeOfRank {X : Scheme.{u}} (F : X.Modules) (n : ℕ)
    (hF : F.IsLocallyFreeOfRank n) (x : X) :
    finrank (ResidueField (X.presheaf.stalk x))
        (ResidueField (X.presheaf.stalk x) ⊗[X.presheaf.stalk x] F.presheaf.stalk x) = n := by
  obtain ⟨U, hxU, ⟨α⟩⟩ := hF x
  apply Module.finrank_eq_of_rank_eq
  rw [rank_fibre_of_restrict_iso_free F α hxU]
  simp

/-- If `f : N → M'` is a base change along `A → S`, then for every field `K` over `S` (with
compatible `A`-algebra structure), `K ⊗[S] M'` and `K ⊗[A] N` have the same dimension. -/
theorem finrank_tensor_eq_of_isBaseChange {A S K N M' : Type*} [CommRing A] [CommRing S]
    [Field K] [Algebra A S] [Algebra S K] [Algebra A K] [IsScalarTower A S K]
    [AddCommGroup N] [Module A N] [AddCommGroup M'] [Module A M'] [Module S M']
    [IsScalarTower A S M'] {f : N →ₗ[A] M'} (hf : IsBaseChange S f) :
    finrank K (K ⊗[S] M') = finrank K (K ⊗[A] N) :=
  ((AlgebraTensorModule.congr (LinearEquiv.refl K K) hf.equiv.symm).trans
    (AlgebraTensorModule.cancelBaseChange A S K K N)).finrank_eq

/-- On `Spec R` with `R` reduced, let `G` be associated to a finite `R`-module. If every fibre
of `G` has dimension `n`, then every stalk of `G` is free of rank `n`. -/
theorem nonempty_basis_stalk_of_finrank_fibre_spec {R : CommRingCat.{u}} [IsReduced R]
    (G : (Spec R).Modules) (hloc : IsLocalizing (modulesSpecToSheaf.obj G))
    [Module.Finite R Γ(G, ⊤)] (n : ℕ)
    (h : ∀ y : Spec R, finrank (ResidueField ((Spec R).presheaf.stalk y))
      (ResidueField ((Spec R).presheaf.stalk y) ⊗[(Spec R).presheaf.stalk y]
        G.presheaf.stalk y) = n)
    (y : Spec R) :
    Nonempty (Basis (Fin n) ((Spec R).presheaf.stalk y) (G.presheaf.stalk y)) := by
  have hbc (z : Spec R) : IsBaseChange ((Spec R).presheaf.stalk z) (germTopLinear G z) :=
    have := isLocalizedModule_germTopLinear G hloc z
    IsLocalizedModule.isBaseChange z.asIdeal.primeCompl _ (germTopLinear G z)
  have : IsReduced ((Spec R).presheaf.stalk y) :=
    isReduced_localizationPreserves y.asIdeal.primeCompl _ inferInstance
  have := isLocalizedModule_germTopLinear G hloc y
  have : Module.Finite ((Spec R).presheaf.stalk y) (G.presheaf.stalk y) :=
    Module.Finite.of_isLocalizedModule y.asIdeal.primeCompl
      (Rₚ := (Spec R).presheaf.stalk y) (germTopLinear G y)
  have hP (P : PrimeSpectrum ((Spec R).presheaf.stalk y)) :
      finrank P.asIdeal.ResidueField
        (P.asIdeal.ResidueField ⊗[(Spec R).presheaf.stalk y] G.presheaf.stalk y) = n := by
    let z : Spec R := ⟨P.asIdeal.comap (algebraMap R ((Spec R).presheaf.stalk y)),
      Ideal.comap_isPrime _ _⟩
    have : IsLocalization.AtPrime (Localization.AtPrime P.asIdeal) z.asIdeal :=
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization y.asIdeal.primeCompl
        (S := (Spec R).presheaf.stalk y) _ P.asIdeal
    let e : Localization.AtPrime P.asIdeal ≃ₐ[R] (Spec R).presheaf.stalk z :=
      have := freeLocus_stalk_isLocalization z
      IsLocalization.algEquiv z.asIdeal.primeCompl _ _
    rw [finrank_tensor_eq_of_isBaseChange (hbc y), ← h z, finrank_tensor_eq_of_isBaseChange (hbc z)]
    refine congrArg Cardinal.toNat (rank_tensorProduct_eq_of_ringEquiv (RingEquiv.refl R)
      (ResidueField.mapEquiv e.toRingEquiv) (fun r => ?_) (AddEquiv.refl _) (fun _ _ => rfl))
    rw [IsScalarTower.algebraMap_apply R (Localization.AtPrime P.asIdeal)
        P.asIdeal.ResidueField, ResidueField.algebraMap_eq,
      IsScalarTower.algebraMap_apply R ((Spec R).presheaf.stalk z)
        (ResidueField ((Spec R).presheaf.stalk z)), ResidueField.algebraMap_eq]
    simp [ResidueField.mapEquiv, ResidueField.map_residue]
  have hy := h y
  obtain ⟨b⟩ := free_of_forall_finrank_fiber_eq_of_isReduced (G.presheaf.stalk y)
    (fun P => (hP P).trans hy.symm)
  exact ⟨b.reindex (finCongr hy)⟩

/-- On a reduced scheme, if every fibre of a coherent sheaf `F` has dimension `n`, then every
stalk `F_x` is free and every fibre has rank `n` (as a cardinal). -/
theorem free_stalk_of_finrank_fibre {X : Scheme.{u}} [IsReduced X] (F : X.Modules)
    (hF : IsCoherent F) (n : ℕ)
    (h : ∀ x : X, finrank (ResidueField (X.presheaf.stalk x))
      (ResidueField (X.presheaf.stalk x) ⊗[X.presheaf.stalk x] F.presheaf.stalk x) = n)
    (x : X) :
    Module.Free (X.presheaf.stalk x) (F.presheaf.stalk x) ∧
      Module.rank (ResidueField (X.presheaf.stalk x))
        (ResidueField (X.presheaf.stalk x) ⊗[X.presheaf.stalk x] F.presheaf.stalk x) = n := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let Va : X.affineOpens := ⟨V, hV⟩
  obtain ⟨hfin, hiso⟩ := forall_affine_finite_of_isCoherent F hF Va
  let G := specRestriction F Va
  have : Module.Finite Γ(X, V) Γ(G, ⊤) := (finite_specRestriction_iff F Va).mpr hfin
  have hloc : IsLocalizing (modulesSpecToSheaf.obj G) :=
    (isIso_fromTildeΓ_iff_isLocalizing G).mp hiso
  have : IsOpenImmersion hV.fromSpec := hV.isOpenImmersion_fromSpec
  have hG : ∀ z : Spec Γ(X, V), finrank (ResidueField ((Spec Γ(X, V)).presheaf.stalk z))
      (ResidueField ((Spec Γ(X, V)).presheaf.stalk z) ⊗[(Spec Γ(X, V)).presheaf.stalk z]
        G.presheaf.stalk z) = n := fun z => by
    rw [← finrank_fibre_restrict hV.fromSpec F z]
    exact h _
  obtain ⟨y, rfl⟩ : x ∈ Set.range hV.fromSpec := by rwa [hV.range_fromSpec]
  obtain ⟨b⟩ := nonempty_basis_stalk_of_finrank_fibre_spec G hloc n hG y
  refine ⟨(free_stalk_restrict_iff hV.fromSpec F y).mpr (Module.Free.of_basis b), ?_⟩
  rw [rank_fibre_restrict hV.fromSpec F y, rank_eq_card_basis (b.baseChange _)]
  simp

/-- **Constant fibre dimension criterion**. On a reduced locally Noetherian scheme `X`, a
coherent `𝒪_X`-module `F` is locally free of rank `n` if and only if
`dim_{k(x)} (F_x ⊗ k(x)) = n` for every `x ∈ X`. The direction from constant fibre dimension to
local freeness is Hartshorne II, Exercise 5.8(c) (stated there for Noetherian `X`); the converse
direction supplements it. -/
theorem isLocallyFreeOfRank_iff_forall_finrank_fibre {X : Scheme.{u}} [IsReduced X]
    [IsLocallyNoetherian X] (F : X.Modules) (hF : IsCoherent F) (n : ℕ) :
    F.IsLocallyFreeOfRank n ↔ ∀ x : X, finrank (ResidueField (X.presheaf.stalk x))
      (ResidueField (X.presheaf.stalk x) ⊗[X.presheaf.stalk x] F.presheaf.stalk x) = n := by
  refine ⟨finrank_fibre_of_isLocallyFreeOfRank F n, fun h => ?_⟩
  have hfree := free_stalk_of_finrank_fibre F hF n h
  have hlf : F.IsLocallyFree :=
    (isLocallyFree_iff_forall_free_stalk_of_isLocallyNoetherian F hF).mpr fun x => (hfree x).1
  refine (F.isLocallyFreeOfRank_iff n).mpr ⟨hlf, fun x => ?_⟩
  obtain ⟨U, hxU, I, ⟨α⟩⟩ := hlf x
  rw [F.rankAt_eq α hxU, ← rank_fibre_of_restrict_iso_free F α hxU, (hfree x).2]

end

end Hartshorne

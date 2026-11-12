/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.AffineSpace
import Hartshorne.Scheme.QuasiCoherentAlgebraOfModule
import Hartshorne.Scheme.SymmetricAlgebraAffineSections

/-!
# Geometric vector bundles

Hartshorne II, Exercise 5.18 (pp. 128–129).

## Geometric vector bundles

Hartshorne defines a *geometric vector bundle of rank `n`* over a scheme `Y` as a scheme `f : X ⟶ Y`
over `Y` together with the additional data of an open covering `{U_i}` of `Y` and isomorphisms
`ψ_i : f⁻¹(U_i) ≅ 𝔸ⁿ_{U_i}` over `U_i`, such that for every `i, j` and every open affine
`U = Spec A ⊆ U_i ∩ U_j`, the automorphism `ψ = ψ_i ∘ ψ_j⁻¹` of `𝔸ⁿ_U = Spec A[x_1, …, x_n]` is
given by a linear automorphism `θ` of `A[x_1, …, x_n]`: `θ(a) = a` for `a ∈ A` and
`θ(x_k) = ∑_l a_{kl} x_l` with `a_{kl} ∈ A`. This is `GeometricVectorBundle f n`.

## The vector bundle of a locally free sheaf

For a locally free sheaf `E` of rank `n` on `Y`, Hartshorne's Exercise 5.18(a) defines
`V(E) = Spec_Y Sym(E)` (with Hartshorne's convention: `Sym(E)`, not `Sym(E^∨)`). Here
`Scheme.Modules.vectorBundle E hE` is the relative spectrum of the quasi-coherent
`𝒪_Y`-algebra `Sym(E)` (`Scheme.Modules.symmetricQuasiCoherentAlgebra`), an affine scheme over
`Y` (`Scheme.Modules.vectorBundleProj`).
-/

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry

noncomputable section

variable {X Y : Scheme.{u}}

/-- The standard chart `Spec A[x_1, …, x_n] ≅ 𝔸ⁿ_V ⊆ 𝔸ⁿ_U` of affine `n`-space over an open `U` of
`Y`, at an affine open `V ⊆ U` with ring of sections `A = Γ(V, 𝒪_V)`: the inverse of the
identification `𝔸ⁿ_V ≅ Spec A[x_1, …, x_n]`, followed by `𝔸ⁿ_V ⟶ 𝔸ⁿ_U`. -/
def affineSpaceChart (n : ℕ) {U : Y.Opens} (V : Y.affineOpens) (h : (V : Y.Opens) ≤ U) :
    Spec (.of (MvPolynomial (ULift.{u} (Fin n)) Γ(V, ⊤))) ⟶ 𝔸(ULift.{u} (Fin n); U) :=
  (AffineSpace.isoOfIsAffine (ULift.{u} (Fin n)) V).inv ≫
    AffineSpace.map (ULift.{u} (Fin n)) (Y.homOfLE h)

/-- Over affine bases `S`, `T`, the map `𝔸ⁿ_S ⟶ 𝔸ⁿ_T` induced by `f : S ⟶ T` is, under the
identifications `𝔸ⁿ_S ≅ Spec Γ(S)[x_1, …, x_n]`, the spectrum of the map of polynomial rings. -/
lemma AffineSpace.isoOfIsAffine_inv_map_hom (n : Type u) {S T : Scheme.{u}} [IsAffine S]
    [IsAffine T] (f : S ⟶ T) :
    (AffineSpace.isoOfIsAffine n S).inv ≫ AffineSpace.map n f ≫ (AffineSpace.isoOfIsAffine n T).hom =
      Spec.map (CommRingCat.ofHom (MvPolynomial.map f.appTop.hom)) := by
  apply ext_of_isAffine
  rw [← cancel_epi (Scheme.ΓSpecIso _).inv, ← cancel_mono (Scheme.ΓSpecIso _).hom]
  simp only [Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality,
    Iso.inv_hom_id_assoc, AffineSpace.isoOfIsAffine_hom_appTop]
  have hC : CommRingCat.ofHom (MvPolynomial.C (σ := n)) ≫ CommRingCat.ofHom
      (MvPolynomial.eval₂Hom (Scheme.Hom.appTop (𝔸(n; T) ↘ T)).hom (AffineSpace.coord T)) ≫
        Scheme.Hom.appTop (AffineSpace.map n f) ≫
          Scheme.Hom.appTop (AffineSpace.isoOfIsAffine n S).inv ≫ (Scheme.ΓSpecIso _).hom =
      f.appTop ≫ CommRingCat.ofHom MvPolynomial.C := by
    rw [← Category.assoc, ← CommRingCat.ofHom_comp, MvPolynomial.eval₂Hom_comp_C,
      CommRingCat.ofHom_hom, ← Category.assoc, ← Scheme.Hom.comp_appTop, AffineSpace.map_over,
      Scheme.Hom.comp_appTop, Category.assoc, ← Category.assoc (Scheme.Hom.appTop (𝔸(n; S) ↘ S)),
      ← Scheme.Hom.comp_appTop, AffineSpace.isoOfIsAffine_inv_over, Scheme.Hom.comp_appTop,
      Category.assoc, Scheme.ΓSpecIso_naturality]
    have h1 : (Scheme.ΓSpecIso Γ(S, ⊤)).hom = S.isoSpec.hom.appTop :=
      (Scheme.toSpecΓ_appTop S).symm
    rw [h1, ← Category.assoc (Scheme.Hom.appTop S.isoSpec.inv), ← Scheme.Hom.comp_appTop,
      Iso.hom_inv_id]
    simp
  ext1
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun k => ?_)
  · exact (congrArg (fun φ => φ.hom a) hC).trans (MvPolynomial.map_C _ _).symm
  · simp

/-- An `A`-algebra endomorphism `θ` of `A[x_1, …, x_n]` is *linear* if
`θ(x_k) = ∑_l a_{kl} x_l` for a matrix `(a_{kl})` with entries in `A`. -/
def IsLinearPolynomialAlgHom {A : Type u} [CommRing A] {n : ℕ}
    (θ : MvPolynomial (ULift.{u} (Fin n)) A →ₐ[A] MvPolynomial (ULift.{u} (Fin n)) A) : Prop :=
  ∃ a : Matrix (ULift.{u} (Fin n)) (ULift.{u} (Fin n)) A,
    ∀ k, θ (MvPolynomial.X k) = ∑ l, MvPolynomial.C (a k l) * MvPolynomial.X l

/-- **A geometric vector bundle of rank `n`** over `Y` (Hartshorne II, Exercise 5.18): the
additional data, on a scheme `f : X ⟶ Y` over `Y`, of an open covering `{U_i}` of `Y`
(`U`, `iSup_eq_top`) and isomorphisms `ψ_i : f⁻¹(U_i) ≅ 𝔸ⁿ_{U_i}` over `U_i` (`ψ`, `ψ_over`), such
that for all `i, j` and every open affine `V ⊆ U_i ∩ U_j`, with ring of sections `A`, the
automorphism `ψ_i ∘ ψ_j⁻¹` of `𝔸ⁿ_V = Spec A[x_1, …, x_n]` is `Spec θ` for a linear
`A`-algebra automorphism `θ` of `A[x_1, …, x_n]` (`linear`).

The condition on `ψ_i ∘ ψ_j⁻¹` is stated without restricting the `ψ_i` to `f⁻¹(V)`: it says that
the two open immersions `Spec A[x_1, …, x_n] ⟶ X` obtained from the charts of `𝔸ⁿ_{U_j}` and
`𝔸ⁿ_{U_i}` at `V` (`affineSpaceChart`) followed by `ψ_j⁻¹`, respectively `ψ_i⁻¹`, differ by
`Spec θ`, which is the equation `ψ_j⁻¹ = ψ_i⁻¹ ∘ Spec θ` on `𝔸ⁿ_V`, that is, `ψ_i ∘ ψ_j⁻¹ = Spec θ`.
The variables `x_1, …, x_n` are indexed by `ULift (Fin n)`, as for the free modules of rank `n`
in `Scheme.Modules.IsLocallyFreeOfRank`. -/
structure GeometricVectorBundle (f : X ⟶ Y) (n : ℕ) where
  /-- The index set of the covering. -/
  ι : Type u
  /-- The open covering `{U_i}` of `Y`. -/
  U : ι → Y.Opens
  iSup_eq_top : ⨆ i, U i = ⊤
  /-- The trivializations `ψ_i : f⁻¹(U_i) ≅ 𝔸ⁿ_{U_i}`. -/
  ψ : ∀ i, (f ⁻¹ᵁ U i).toScheme ≅ 𝔸(ULift.{u} (Fin n); U i)
  ψ_over : ∀ i, (ψ i).hom ≫ 𝔸(ULift.{u} (Fin n); U i) ↘ U i = f ∣_ U i
  linear : ∀ (i j : ι) (V : Y.affineOpens) (hi : (V : Y.Opens) ≤ U i) (hj : (V : Y.Opens) ≤ U j),
    ∃ θ : MvPolynomial (ULift.{u} (Fin n)) Γ(V, ⊤) ≃ₐ[Γ(V, ⊤)]
        MvPolynomial (ULift.{u} (Fin n)) Γ(V, ⊤),
      IsLinearPolynomialAlgHom θ.toAlgHom ∧
      affineSpaceChart n V hj ≫ (ψ j).inv ≫ (f ⁻¹ᵁ U j).ι =
        Spec.map (CommRingCat.ofHom θ.toRingEquiv.toRingHom) ≫
          affineSpaceChart n V hi ≫ (ψ i).inv ≫ (f ⁻¹ᵁ U i).ι

/-- An isomorphism `S ≅ T` induces `𝔸(n; S) ≅ 𝔸(n; T)`. -/
private def affineSpaceIsoOfIso (n : Type u) {S T : Scheme.{u}} (e : S ≅ T) :
    𝔸(n; S) ≅ 𝔸(n; T) where
  hom := AffineSpace.map n e.hom
  inv := AffineSpace.map n e.inv
  hom_inv_id := by rw [← AffineSpace.map_comp, e.hom_inv_id, AffineSpace.map_id]
  inv_hom_id := by rw [← AffineSpace.map_comp, e.inv_hom_id, AffineSpace.map_id]

/-- **The trivial geometric vector bundle** `𝔸ⁿ_Y ⟶ Y` of rank `n`, with the covering `{Y}` and
the identity trivialization. -/
def GeometricVectorBundle.trivial (Y : Scheme.{u}) (n : ℕ) :
    GeometricVectorBundle (𝔸(ULift.{u} (Fin n); Y) ↘ Y) n where
  ι := PUnit
  U _ := ⊤
  iSup_eq_top := ciSup_const
  ψ _ := Scheme.isoOfEq _ (Scheme.Hom.preimage_top _) ≪≫ Scheme.topIso _ ≪≫
    affineSpaceIsoOfIso (ULift.{u} (Fin n)) Y.topIso.symm
  ψ_over _ := by
    rw [← cancel_mono (⊤ : Y.Opens).ι, morphismRestrict_ι]
    simp only [Iso.trans_hom, Category.assoc]
    change (Scheme.isoOfEq _ _).hom ≫ (⊤ : (𝔸(ULift.{u} (Fin n); Y)).Opens).ι ≫
      AffineSpace.map _ Y.topIso.inv ≫ _ ≫ _ = _
    rw [AffineSpace.map_over_assoc, Scheme.toIso_inv_ι, Category.comp_id,
      Scheme.isoOfEq_hom_ι_assoc]
  linear i j V hi hj := by
    refine ⟨AlgEquiv.refl, ⟨1, fun k => ?_⟩, ?_⟩
    · simp [Matrix.one_apply]
    · cases i; cases j
      simp

namespace Scheme.Modules

open Hartshorne Hartshorne.SheafAlgebraOperations

variable {E : Y.Modules} {n : ℕ}

/-- `Sym(E)` is quasi-coherent for a locally free `E` of rank `n`. -/
theorem symmetricAlgebra_isQuasicoherent_of_isLocallyFreeOfRank
    (hE : E.IsLocallyFreeOfRank n) : SheafOfModules.IsQuasicoherent.{u, u, u} E.symmetricAlgebra :=
  ((isLocallyFreeOfRank_iff_ringed E n).mp hE).isFiniteLocallyFree
    |>.isQuasicoherent_moduleSheafSymmetricAlgebra

/-- **`Sym(E)` as a quasi-coherent `𝒪_Y`-algebra**, for a locally free `E` of rank `n`: its ring
of sections over an affine open `U` is `Γ(U, Sym(E))`. -/
def symmetricQuasiCoherentAlgebra (E : Y.Modules) (hE : E.IsLocallyFreeOfRank n) :
    QuasiCoherentAlgebra Y :=
  haveI := symmetricAlgebra_isQuasicoherent_of_isLocallyFreeOfRank hE
  ModuleSheafAlgebra.toQuasiCoherentAlgebra (symmetricAlgebraStructure_isCommutative E)

/-- **The geometric vector bundle `V(E) = Spec_Y Sym(E)`** of a locally free sheaf `E` of rank `n`
(Hartshorne II, Exercise 5.18(a)), with Hartshorne's convention `Sym(E)`, not `Sym(E^∨)`. It is
defined from `E` alone, so it does not depend on any choice of trivializations of `E`. -/
abbrev vectorBundle (E : Y.Modules) (hE : E.IsLocallyFreeOfRank n) : Scheme.{u} :=
  (symmetricQuasiCoherentAlgebra E hE).relSpec

/-- The structure morphism `V(E) ⟶ Y`, an affine morphism. -/
abbrev vectorBundleProj (E : Y.Modules) (hE : E.IsLocallyFreeOfRank n) :
    vectorBundle E hE ⟶ Y :=
  (symmetricQuasiCoherentAlgebra E hE).relSpecToBase

instance (E : Y.Modules) (hE : E.IsLocallyFreeOfRank n) : IsAffineHom (vectorBundleProj E hE) :=
  inferInstance

/-! ### Local trivializations of `V(E)` -/

/-- An affine open of `Y` as an object of the affine Zariski site. -/
abbrev affineSite (V : Y.affineOpens) : Y.AffineZariskiSite := ⟨V.1, V.2⟩

/-- For a frame `e` of `E` over an affine open `V` (a basis of `E|_V`), the ring isomorphism
`A[x_1, …, x_n] ≅ Γ(V, Sym(E))`, `x_k ↦ e_k`, where `A = Γ(V, 𝒪_V)`. -/
def frameChartRingEquiv (V : Y.affineOpens) {e : ULift.{u} (Fin n) → Γ(E, V)}
    (he : Ringed.IsLocalFrame (R := Y.sheaf) E V e) :
    MvPolynomial (ULift.{u} (Fin n)) Γ(V, ⊤) ≃+* E.symSections V :=
  (MvPolynomial.mapEquiv _ (V : Y.Opens).topIso.commRingCatIsoToRingEquiv).trans
    (RingEquiv.ofBijective (E.chartRingHom V e) (E.chartRingHom_bijective V.2 he))

lemma frameChartRingEquiv_apply (V : Y.affineOpens)
    {e : ULift.{u} (Fin n) → Γ(E, V)} (he : Ringed.IsLocalFrame (R := Y.sheaf) E V e)
    (p : MvPolynomial (ULift.{u} (Fin n)) Γ(V, ⊤)) :
    frameChartRingEquiv V he p = E.chartRingHom V e (MvPolynomial.map (V : Y.Opens).topIso.hom.hom p) := rfl

/-- `frameChartRingEquiv` as an isomorphism onto the ring of sections of the quasi-coherent algebra
`Sym(E)` over `V`. -/
def frameChartIso (hE : E.IsLocallyFreeOfRank n) (V : Y.affineOpens)
    {e : ULift.{u} (Fin n) → Γ(E, V)} (he : Ringed.IsLocalFrame (R := Y.sheaf) E V e) :
    CommRingCat.of (MvPolynomial (ULift.{u} (Fin n)) Γ(V, ⊤)) ≅
      (symmetricQuasiCoherentAlgebra E hE).sections.obj (op (affineSite V)) :=
  (frameChartRingEquiv V he).toCommRingCatIso

lemma frameChartIso_hom_apply (hE : E.IsLocallyFreeOfRank n) (V : Y.affineOpens)
    {e : ULift.{u} (Fin n) → Γ(E, V)} (he : Ringed.IsLocalFrame (R := Y.sheaf) E V e)
    (p : MvPolynomial (ULift.{u} (Fin n)) Γ(V, ⊤)) :
    (frameChartIso hE V he).hom p = E.chartRingHom V e (MvPolynomial.map (V : Y.Opens).topIso.hom.hom p) :=
  rfl

/-- **The local trivialization `ψ_V : f⁻¹(V) ≅ 𝔸ⁿ_V` of `V(E)`** given by a frame `e` of `E` over an
affine open `V`: `f⁻¹(V) ≅ Spec Γ(V, Sym(E)) ≅ Spec A[x_1, …, x_n] ≅ 𝔸ⁿ_V`. -/
def frameTrivialization (hE : E.IsLocallyFreeOfRank n) (V : Y.affineOpens)
    {e : ULift.{u} (Fin n) → Γ(E, V)} (he : Ringed.IsLocalFrame (R := Y.sheaf) E V e) :
    ((vectorBundleProj E hE) ⁻¹ᵁ V).toScheme ≅ 𝔸(ULift.{u} (Fin n); V) :=
  (symmetricQuasiCoherentAlgebra E hE).restrictIso (affineSite V) ≪≫
    Scheme.Spec.mapIso (frameChartIso hE V he).op ≪≫
    (AffineSpace.isoOfIsAffine _ V).symm

/-- The trivialization `ψ_V` is an isomorphism over `V`. -/
lemma frameTrivialization_hom_over (hE : E.IsLocallyFreeOfRank n) (V : Y.affineOpens)
    {e : ULift.{u} (Fin n) → Γ(E, V)}
    (he : Ringed.IsLocalFrame (R := Y.sheaf) E V e) :
    (frameTrivialization hE V he).hom ≫ 𝔸(ULift.{u} (Fin n); V) ↘ V =
      vectorBundleProj E hE ∣_ V := by
  rw [← cancel_mono (V : Y.Opens).ι, morphismRestrict_ι]
  simp only [frameTrivialization, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← (symmetricQuasiCoherentAlgebra E hE).restrictIso_hom_fromSpec (affineSite V)]
  congr 1
  rw [AffineSpace.isoOfIsAffine_inv_over_assoc, IsAffineOpen.fromSpec, IsAffineOpen.isoSpec]
  simp only [Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc,
    Scheme.Spec_map, Iso.op_hom, Iso.op_inv, Quiver.Hom.unop_op]
  have hring : CommRingCat.ofHom MvPolynomial.C ≫ (frameChartIso hE V he).hom =
      (V : Y.Opens).topIso.symm.inv ≫
        (symmetricQuasiCoherentAlgebra E hE).structureMap.app (op (affineSite V)) := by
    ext a
    change E.chartRingHom V e (MvPolynomial.map (V : Y.Opens).topIso.hom.hom (MvPolynomial.C a)) =
      ModuleSheafAlgebra.unitRingHom _ _ ((V : Y.Opens).topIso.hom a)
    rw [MvPolynomial.map_C, chartRingHom_C]
  rw [← Spec.map_comp_assoc, hring]
  exact (congrArg (· ≫ _) (Spec.map_comp _ _)).trans (Category.assoc _ _ _)

end Scheme.Modules

end

end AlgebraicGeometry

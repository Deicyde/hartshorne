/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.ModuleCohomologyComparison
import Hartshorne.RingedSpace.ModuleSheafHom
import Hartshorne.Scheme.CoherentAffineLocalCriterion
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Dualizing sheaves

Hartshorne, *Algebraic Geometry*, III.7, definition on p. 241.

Let `X` be a proper scheme of dimension `n` over a field `k`, given by a proper structure
morphism `f : X ⟶ Spec k` with `topologicalKrullDim X = n`. A dualizing sheaf for `X`
(`Hartshorne.DualizingSheaf`) consists of a coherent `𝒪_X`-module `ω°`, a `k`-linear trace
`t : Hⁿ(X, ω°) → k`, and the property that for every coherent `F` the map

`Hom_X(F, ω°) ⟶ Hⁿ(X, F)^∨`, `φ ↦ t ∘ Hⁿ(φ)`,

induced by the pairing `Hom_X(F, ω°) × Hⁿ(X, F) ⟶ Hⁿ(X, ω°) ⟶ k` is bijective. That map is
`k`-linear (`Hartshorne.dualityPairingMap`) and natural in `F`
(`Hartshorne.dualityPairingMap_naturality`), so a dualizing sheaf gives natural `k`-linear
isomorphisms `Hom_X(F, ω°) ≃ Hⁿ(X, F)^∨` (`Hartshorne.DualizingSheaf.dualityEquiv`).

## The `k`-linear structures

The structure morphism gives a ring map `k ⟶ Γ(X, 𝒪_X)`
(`Hartshorne.baseFieldToGlobalSections`). Cohomology `Hⁿ(X, -)` is computed as the derived
functors of `Γ(X, -) : Mod(𝒪_X) ⥤ Mod(Γ(X, 𝒪_X))` (Remark III.2.6.1), and restricting scalars
along `k ⟶ Γ(X, 𝒪_X)` makes it a functor to `k`-vector spaces
(`Hartshorne.cohomologyOverField`). `Hom_X(F, G)` is a `Γ(X, 𝒪_X)`-module, a global section
acting through the multiplication it induces on `G` (II.5, p. 109), hence a `k`-vector space
(`Hartshorne.homOverField`).

The pairing map is `k`-linear because `Hⁿ(X, -)` carries the multiplication by a global
section `r` on `G` to the multiplication by `r` on `Hⁿ(X, G)`
(`Hartshorne.Ringed.moduleSheafCohomologyModule_map_globalScalar`, over any ringed space): on an
injective resolution `G ⟶ I^•` the multiplications by `r` on the `I^p` form a cochain map lifting
the one on `G`, which `Γ(X, -)` sends to multiplication by `r`, and this passes to cohomology.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

namespace Hartshorne

section Scalar

variable {A : Type u} [Ring A]

/-- A morphism of complexes of `A`-modules acting on every term as multiplication by `r` acts on
homology as multiplication by `r`. -/
theorem homologyMap_apply_of_forall_f_apply {ι : Type*} {c : ComplexShape ι}
    {K : HomologicalComplex (ModuleCat.{u} A) c} (ψ : K ⟶ K) (r : A)
    (hψ : ∀ (p : ι) (x : K.X p), (ψ.f p).hom x = r • x) (n : ι) (y : K.homology n) :
    (HomologicalComplex.homologyMap ψ n).hom y = r • y := by
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ n)).1 inferInstance y
  have hz : (HomologicalComplex.cyclesMap ψ n).hom z = r • z := by
    apply (ModuleCat.mono_iff_injective (K.iCycles n)).1 inferInstance
    rw [map_smul, ← LinearMap.comp_apply, ← ModuleCat.hom_comp,
      HomologicalComplex.cyclesMap_i, ModuleCat.hom_comp, LinearMap.comp_apply, hψ]
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, HomologicalComplex.homologyπ_naturality,
    ModuleCat.hom_comp, LinearMap.comp_apply, hz, map_smul]

/-- Let `F` be an additive functor to `A`-modules and `s : X ⟶ X`. If `s` lifts to a cochain
endomorphism of an injective resolution of `X` which `F` sends to multiplication by `r` in every
degree, then every right derived functor of `F` sends `s` to multiplication by `r`. -/
theorem rightDerived_map_apply_of_lift {C : Type*} [Category* C] [Abelian C]
    [HasInjectiveResolutions C] (F : C ⥤ ModuleCat.{u} A) [F.Additive] {X : C} (s : X ⟶ X)
    (I : InjectiveResolution X) (φ : I.cocomplex ⟶ I.cocomplex)
    (comm : I.ι.f 0 ≫ φ.f 0 = s ≫ I.ι.f 0) (r : A)
    (hφ : ∀ (p : ℕ) (x : F.obj (I.cocomplex.X p)), (F.map (φ.f p)).hom x = r • x) (n : ℕ)
    (x : (F.rightDerived n).obj X) :
    ((F.rightDerived n).map s).hom x = r • x := by
  have h : (F.rightDerived n).map s = (I.isoRightDerivedObj F n).hom ≫
      (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ n).map φ ≫
        (I.isoRightDerivedObj F n).inv := by
    rw [← Category.assoc, Iso.eq_comp_inv,
      InjectiveResolution.isoRightDerivedObj_hom_naturality s I I φ comm F n]
  have hH := homologyMap_apply_of_forall_f_apply ((F.mapHomologicalComplex _).map φ) r
    (fun p y ↦ hφ p y) n ((I.isoRightDerivedObj F n).hom.hom x)
  rw [h, ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply]
  change (I.isoRightDerivedObj F n).inv.hom
    ((HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map φ) n).hom
      ((I.isoRightDerivedObj F n).hom.hom x)) = r • x
  rw [hH]
  refine ((I.isoRightDerivedObj F n).inv.hom.map_smul r _).trans ?_
  congr 1
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, Iso.hom_inv_id, ModuleCat.hom_id,
    LinearMap.id_apply]

end Scalar

namespace Ringed

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

/-- Multiplication by a global section of the structure sheaf commutes with every morphism of
module sheaves. -/
theorem globalScalar_naturality {M N : SheafOfModules.{u} (ringCatSheafOf R)} (g : M ⟶ N)
    (r : R.obj.obj (op ⊤)) :
    moduleSheafHomGlobalScalarRingHom M r ≫ g = g ≫ moduleSheafHomGlobalScalarRingHom N r := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  rintro ⟨V⟩
  ext x
  change (g.val.app (op V)).hom ((moduleSheafHomGlobalScalarRingHom M r).val.app (op V) x) =
    (moduleSheafHomGlobalScalarRingHom N r).val.app (op V) ((g.val.app (op V)).hom x)
  rw [(moduleSheafHomData R).global_scalar_app, (moduleSheafHomData R).global_scalar_app]
  exact (g.val.app (op V)).hom.map_smul _ x

/-- On global sections, the multiplication by a global section `r` is multiplication by `r`. -/
theorem evaluation_map_globalScalar (M : SheafOfModules.{u} (ringCatSheafOf R))
    (r : R.obj.obj (op ⊤)) (x : M.val.obj (op ⊤)) :
    ((SheafOfModules.evaluation (ringCatSheafOf R) (op ⊤)).map
      (moduleSheafHomGlobalScalarRingHom M r)).hom x = r • x := by
  change (moduleSheafHomGlobalScalarRingHom M r).val.app (op ⊤) x = r • x
  rw [(moduleSheafHomData R).global_scalar_app]
  have : (homOfLE (show (⊤ : Opens X) ≤ ⊤ from le_top)).op = 𝟙 (op ⊤) := Subsingleton.elim _ _
  rw [this, CategoryTheory.Functor.map_id]
  rfl

/-- The multiplications by a global section `r` on the terms of a complex of module sheaves form
a cochain endomorphism. -/
def globalScalarCochainMap (K : CochainComplex (SheafOfModules.{u} (ringCatSheafOf R)) ℕ)
    (r : R.obj.obj (op ⊤)) : K ⟶ K where
  f p := moduleSheafHomGlobalScalarRingHom (K.X p) r
  comm' p q _ := globalScalar_naturality (K.d p q) r

/-- **Cohomology is linear over global sections.** The functor `Hⁿ(X, -)`, valued in
`Γ(X, 𝒪_X)`-modules, sends the multiplication by a global section `r` on a module sheaf `M` to the
multiplication by `r` on `Hⁿ(X, M)`. This supplements Hartshorne III, Remark 2.6.1 (p. 208). -/
theorem moduleSheafCohomologyModule_map_globalScalar (M : SheafOfModules.{u} (ringCatSheafOf R))
    (r : R.obj.obj (op ⊤)) (n : ℕ) (x : (moduleSheafCohomologyModule (ringCatSheafOf R) n).obj M) :
    ((moduleSheafCohomologyModule (ringCatSheafOf R) n).map
      (moduleSheafHomGlobalScalarRingHom M r)).hom x = r • x :=
  haveI := ModuleCohomology.evaluation_additive (ringCatSheafOf R)
  rightDerived_map_apply_of_lift (SheafOfModules.evaluation.{u} (ringCatSheafOf R) (op ⊤))
    (moduleSheafHomGlobalScalarRingHom M r) (injectiveResolution M)
    (globalScalarCochainMap (injectiveResolution M).cocomplex r)
    (globalScalar_naturality (M := M) ((injectiveResolution M).ι.f 0) r).symm r
    (fun _ y ↦ evaluation_map_globalScalar _ r y) n x

end Ringed

section Field

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- The ring map `k ⟶ Γ(X, 𝒪_X)` induced by the structure morphism `f : X ⟶ Spec k`. -/
def baseFieldToGlobalSections : k →+* X.ringCatSheaf.obj.obj (op ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop).hom

/-- The cohomology `Hⁿ(X, -)` of `𝒪_X`-modules as a functor to `k`-vector spaces: the derived
functors of `Γ(X, -) : Mod(𝒪_X) ⥤ Mod(Γ(X, 𝒪_X))`, with scalars restricted along
`k ⟶ Γ(X, 𝒪_X)`. -/
def cohomologyOverField (n : ℕ) : X.Modules ⥤ ModuleCat.{u} k :=
  moduleSheafCohomologyModule X.ringCatSheaf n ⋙
    ModuleCat.restrictScalars (baseFieldToGlobalSections f)

instance (n : ℕ) : (cohomologyOverField f n).Additive :=
  haveI := ModuleCohomology.evaluation_additive X.ringCatSheaf
  inferInstanceAs (moduleSheafCohomologyModule X.ringCatSheaf n ⋙
    ModuleCat.restrictScalars (baseFieldToGlobalSections f)).Additive

/-- The multiplication by the image of `c ∈ k` in `Γ(X, 𝒪_X)`, as an endomorphism of an
`𝒪_X`-module `G`. -/
def baseFieldScalar (G : X.Modules) (c : k) : G ⟶ G :=
  Ringed.moduleSheafHomGlobalScalarRingHom (R := X.sheaf) G (baseFieldToGlobalSections f c)

/-- The `k`-vector space `Hom_X(F, G)`: a scalar acts through the multiplication its image in
`Γ(X, 𝒪_X)` induces on `G`. -/
def homOverField (F G : X.Modules) : ModuleCat.{u} k :=
  (ModuleCat.restrictScalars (baseFieldToGlobalSections f)).obj
    (@ModuleCat.of _ _ (F ⟶ G) _ (Ringed.moduleSheafHomGlobalHomModule (R := X.sheaf) F G))

/-- A scalar `c ∈ k` acts on `Hom_X(F, G)` by postcomposition with the multiplication by its
image in `Γ(X, 𝒪_X)`. -/
theorem homOverField_smul (F G : X.Modules) (c : k) (φ : homOverField f F G) :
    c • φ = (φ : F ⟶ G) ≫ baseFieldScalar f G c :=
  rfl

/-- `Hⁿ(X, -)` sends the multiplication by the image of `c ∈ k` to multiplication by `c`. -/
theorem cohomologyOverField_map_globalScalar (n : ℕ) (G : X.Modules) (c : k)
    (x : (cohomologyOverField f n).obj G) :
    ((cohomologyOverField f n).map (baseFieldScalar f G c)).hom x = c • x :=
  Ringed.moduleSheafCohomologyModule_map_globalScalar (R := X.sheaf) G _ n x

/-- The map `Hom_X(F, ω) ⟶ Hⁿ(X, F)^∨`, `φ ↦ t ∘ Hⁿ(φ)`, induced by the pairing
`Hom_X(F, ω) × Hⁿ(X, F) ⟶ Hⁿ(X, ω) ⟶ k` given by functoriality of `Hⁿ(X, -)` followed by a
`k`-linear map `t : Hⁿ(X, ω) ⟶ k` (Hartshorne III.7, p. 241). It is `k`-linear. -/
def dualityPairingMap (n : ℕ) {ω : X.Modules} (t : (cohomologyOverField f n).obj ω →ₗ[k] k)
    (F : X.Modules) :
    homOverField f F ω →ₗ[k] Module.Dual k ((cohomologyOverField f n).obj F) where
  toFun φ := t ∘ₗ ((cohomologyOverField f n).map (φ : F ⟶ ω)).hom
  map_add' φ ψ := by
    have key (φ ψ : F ⟶ ω) : t ∘ₗ ((cohomologyOverField f n).map (φ + ψ)).hom =
        t ∘ₗ ((cohomologyOverField f n).map φ).hom +
          t ∘ₗ ((cohomologyOverField f n).map ψ).hom := by
      rw [Functor.map_add, ModuleCat.hom_add, LinearMap.comp_add]
    exact key φ ψ
  map_smul' c φ := by
    have key (φ : F ⟶ ω) : t ∘ₗ ((cohomologyOverField f n).map
        (φ ≫ baseFieldScalar f ω c)).hom =
        c • t ∘ₗ ((cohomologyOverField f n).map φ).hom := by
      rw [Functor.map_comp]
      ext x
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.smul_apply,
        cohomologyOverField_map_globalScalar, map_smul]
    rw [homOverField_smul, RingHom.id_apply]
    exact key φ

theorem dualityPairingMap_apply (n : ℕ) {ω : X.Modules}
    (t : (cohomologyOverField f n).obj ω →ₗ[k] k) (F : X.Modules) (φ : F ⟶ ω)
    (x : (cohomologyOverField f n).obj F) :
    dualityPairingMap f n t F φ x = t (((cohomologyOverField f n).map φ).hom x) :=
  rfl

/-- The map `Hom_X(F, ω) ⟶ Hⁿ(X, F)^∨` is natural in `F`: for `g : F' ⟶ F`, the functional
attached to `g ≫ φ` is the one attached to `φ` composed with `Hⁿ(g)`. -/
theorem dualityPairingMap_naturality (n : ℕ) {ω : X.Modules}
    (t : (cohomologyOverField f n).obj ω →ₗ[k] k) {F F' : X.Modules} (g : F' ⟶ F) (φ : F ⟶ ω) :
    dualityPairingMap f n t F' (g ≫ φ) =
      (dualityPairingMap f n t F φ).comp ((cohomologyOverField f n).map g).hom := by
  ext x
  simp only [dualityPairingMap_apply, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

/-- **Dualizing sheaf** (Hartshorne III.7, p. 241). Let `X` be a proper scheme of dimension `n`
over a field `k`, with structure morphism `f : X ⟶ Spec k`. A dualizing sheaf for `X` consists of
a coherent `𝒪_X`-module `ω°`, a `k`-linear trace `t : Hⁿ(X, ω°) ⟶ k`, and the property that for
every coherent `𝒪_X`-module `F` the map `Hom_X(F, ω°) ⟶ Hⁿ(X, F)^∨`, `φ ↦ t ∘ Hⁿ(φ)`, induced by
the pairing `Hom_X(F, ω°) × Hⁿ(X, F) ⟶ Hⁿ(X, ω°) ⟶ k`, is bijective. That map is `k`-linear and
natural in `F` (`Hartshorne.dualityPairingMap_naturality`), so this gives natural `k`-linear
isomorphisms `Hom_X(F, ω°) ≃ Hⁿ(X, F)^∨` (`Hartshorne.DualizingSheaf.dualityEquiv`). -/
structure DualizingSheaf (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] (n : ℕ) (hdim : topologicalKrullDim X = n) where
  /-- The dualizing module `ω°_X`. -/
  sheaf : X.Modules
  /-- `ω°_X` is coherent. -/
  isCoherent : IsCoherent sheaf
  /-- The trace `t : Hⁿ(X, ω°_X) ⟶ k`. -/
  trace : (cohomologyOverField f n).obj sheaf →ₗ[k] k
  /-- For every coherent `F`, the pairing induces a bijection `Hom_X(F, ω°_X) ⟶ Hⁿ(X, F)^∨`. -/
  bijective_dualityPairingMap (F : X.Modules) (hF : IsCoherent F) :
    Function.Bijective (dualityPairingMap f n trace F)

namespace DualizingSheaf

variable {f} [IsProper f] {n : ℕ} {hdim : topologicalKrullDim X = n}

/-- The natural `k`-linear isomorphism `Hom_X(F, ω°_X) ≃ Hⁿ(X, F)^∨` of a dualizing sheaf, for
coherent `F`. -/
def dualityEquiv (D : DualizingSheaf f n hdim) (F : X.Modules) (hF : IsCoherent F) :
    homOverField f F D.sheaf ≃ₗ[k] Module.Dual k ((cohomologyOverField f n).obj F) :=
  LinearEquiv.ofBijective (dualityPairingMap f n D.trace F) (D.bijective_dualityPairingMap F hF)

theorem dualityEquiv_apply (D : DualizingSheaf f n hdim) (F : X.Modules) (hF : IsCoherent F)
    (φ : F ⟶ D.sheaf) (x : (cohomologyOverField f n).obj F) :
    D.dualityEquiv F hF φ x = D.trace (((cohomologyOverField f n).map φ).hom x) :=
  rfl

/-- The isomorphisms `Hom_X(F, ω°_X) ≃ Hⁿ(X, F)^∨` are natural in the coherent module `F`. -/
theorem dualityEquiv_naturality (D : DualizingSheaf f n hdim) {F F' : X.Modules}
    (hF : IsCoherent F) (hF' : IsCoherent F') (g : F' ⟶ F) (φ : F ⟶ D.sheaf) :
    D.dualityEquiv F' hF' (g ≫ φ) =
      (D.dualityEquiv F hF φ).comp ((cohomologyOverField f n).map g).hom :=
  dualityPairingMap_naturality f n D.trace g φ

end DualizingSheaf

end Field

end Hartshorne

/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.LinearAlgebra.Dual.BaseChange
import Mathlib.RingTheory.Ideal.Cotangent

/-!
# The Zariski tangent map

Hartshorne, *Algebraic Geometry*, III.10, the tangent map before Proposition 10.4 (p. 270).

For a morphism of schemes `f : X ⟶ Y`, a point `x : X` and `y = f x`, the Zariski tangent
space `T_x X` is the residue-field dual `Hom_{k(x)}(𝔪_x/𝔪_x², k(x))` of the cotangent space of the
local ring `𝒪_{X,x}`; this is the notion of tangent space used for rational points in the project
(the dual of `IsLocalRing.CotangentSpace`), now over the residue field of an arbitrary point.

The construction is carried out for a local homomorphism `A → B` of local rings and then
specialised to the stalk map `𝒪_{Y,y} → 𝒪_{X,x}`.

## Main definitions

* `Hartshorne.localCotangentMap`: the cotangent map `𝔪_A/𝔪_A² → 𝔪_B/𝔪_B²`.
* `Hartshorne.localCotangentBaseChange`: its scalar extension
  `κ_B ⊗_{κ_A} 𝔪_A/𝔪_A² → 𝔪_B/𝔪_B²`, a `κ_B`-linear map.
* `Hartshorne.dualBaseChangeEquiv`: for a finite-dimensional `k`-vector space `V` and a field
  extension `K/k`, the natural isomorphism `K ⊗_k V^∨ ≃ (K ⊗_k V)^∨`.
* `Hartshorne.localTangentMap`: the `κ_B`-linear tangent map `T_B → κ_B ⊗_{κ_A} T_A`.
* `Hartshorne.zariskiTangentMap`: the `k(x)`-linear tangent map
  `T_x X → k(x) ⊗_{k(y)} T_y Y` of a morphism of schemes.

## Main results

* Duality: `Hartshorne.dualBaseChangeEquiv_zariskiTangentMap` (and the local
  `Hartshorne.dualBaseChangeEquiv_localTangentMap`) says that, after the identification
  `k(x) ⊗_{k(y)} T_y Y ≃ (k(x) ⊗_{k(y)} 𝔪_y/𝔪_y²)^∨`, the tangent map is the transpose of the
  scalar-extended cotangent map; `Hartshorne.localTangentMap_eq_iff` shows this characterises it.
* Compatibility with the map on local rings: `Hartshorne.localCotangentMap_stalkMap_toCotangent`
  and `Hartshorne.dualBaseChangeEquiv_zariskiTangentMap_toCotangent` say that the class of
  `m ∈ 𝔪_y` goes to the class of its image under the stalk map, so `⟨T(v), 1 ⊗ [m]⟩ = v([f♯ m])`;
  `Hartshorne.stalkMap_residueField_algebraMap_eq` identifies the residue-field extension with the
  residue-field map of `f`.
* Functoriality: `Hartshorne.zariskiTangentMap_comp` (and the local
  `Hartshorne.localTangentMap_comp`) says that for `f : X ⟶ Y`, `g : Y ⟶ Z`, the tangent map of
  `f ≫ g` at `x` is the scalar extension to `k(x)` of the tangent map of `g` at `f x`, composed
  with the tangent map of `f` at `x` and the cancellation
  `k(x) ⊗_{k(y)} (k(y) ⊗_{k(z)} T_z Z) ≃ k(x) ⊗_{k(z)} T_z Z`.

## Implementation notes

The tensor product is written `k(x) ⊗_{k(y)} T_y Y`, with the field `k(x)` on the left, which is
how Mathlib extends scalars; Hartshorne's `T_y Y ⊗_{k(y)} k(x)` is the same space up to the
symmetry of the tensor product. The natural map `T_x X → k(x) ⊗_{k(y)} T_y Y` exists because
dualising commutes with extension of scalars for finite-dimensional spaces, so the cotangent
space at `y` is assumed finite-dimensional over `k(y)` (as it is when `𝒪_{Y,y}` is Noetherian,
for instance for schemes locally of finite type over a field).
-/

namespace Hartshorne

noncomputable section

open IsLocalRing Module
open scoped TensorProduct

universe u v w

/-- The Zariski tangent space `Hom_κ(𝔪/𝔪², κ)` of a local ring with residue field `κ`. -/
abbrev LocalZariskiTangentSpace (A : Type u) [CommRing A] [IsLocalRing A] : Type u :=
  Module.Dual (ResidueField A) (CotangentSpace A)

section LocalRing

variable (A : Type u) (B : Type v) [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
  [Algebra A B] [IsLocalHom (algebraMap A B)]

theorem maximalIdeal_le_comap_ofId :
    maximalIdeal A ≤ (maximalIdeal B).comap (Algebra.ofId A B) := fun a ha ↦
  map_nonunit (algebraMap A B) a ha

/-- The cotangent map `𝔪_A/𝔪_A² → 𝔪_B/𝔪_B²` of a local homomorphism. -/
def localCotangentMap : CotangentSpace A →ₗ[A] CotangentSpace B :=
  Ideal.mapCotangent (maximalIdeal A) (maximalIdeal B) (Algebra.ofId A B)
    (maximalIdeal_le_comap_ofId A B)

theorem localCotangentMap_toCotangent (m : maximalIdeal A) :
    localCotangentMap A B ((maximalIdeal A).toCotangent m) =
      (maximalIdeal B).toCotangent
        ⟨algebraMap A B m, maximalIdeal_le_comap_ofId A B m.2⟩ :=
  rfl

theorem localCotangentMap_residue_smul (a : ResidueField A) (ω : CotangentSpace A) :
    localCotangentMap A B (a • ω) =
      algebraMap (ResidueField A) (ResidueField B) a • localCotangentMap A B ω := by
  obtain ⟨a, rfl⟩ := residue_surjective a
  rw [ResidueField.algebraMap_residue]
  have hA : residue A a • ω = a • ω := algebraMap_smul (ResidueField A) a ω
  have hB : ∀ η : CotangentSpace B, residue B (algebraMap A B a) • η = a • η := fun η ↦ by
    rw [show residue B (algebraMap A B a) = algebraMap B (ResidueField B) (algebraMap A B a)
      from rfl, algebraMap_smul, algebraMap_smul]
  rw [hA, hB, map_smul]

/-- The cotangent map as a map of vector spaces over the residue field of `A`, where the
residue field of `A` acts on the target through the residue field of `B`. -/
private def localCotangentMapResidue :
    letI : Module (ResidueField A) (CotangentSpace B) :=
      Module.compHom _ (algebraMap (ResidueField A) (ResidueField B))
    CotangentSpace A →ₗ[ResidueField A] CotangentSpace B :=
  letI : Module (ResidueField A) (CotangentSpace B) :=
    Module.compHom _ (algebraMap (ResidueField A) (ResidueField B))
  { toFun := localCotangentMap A B
    map_add' := map_add _
    map_smul' := localCotangentMap_residue_smul A B }

/-- The cotangent map after extending scalars from the residue field `κ_A` of `A` to the residue
field `κ_B` of `B`: the `κ_B`-linear map `κ_B ⊗_{κ_A} 𝔪_A/𝔪_A² → 𝔪_B/𝔪_B²`. -/
def localCotangentBaseChange :
    ResidueField B ⊗[ResidueField A] CotangentSpace A →ₗ[ResidueField B] CotangentSpace B :=
  letI : Module (ResidueField A) (CotangentSpace B) :=
    Module.compHom _ (algebraMap (ResidueField A) (ResidueField B))
  haveI : IsScalarTower (ResidueField A) (ResidueField B) (CotangentSpace B) :=
    ⟨fun a b η ↦ by
      change (a • b) • η = algebraMap (ResidueField A) (ResidueField B) a • (b • η)
      rw [Algebra.smul_def, mul_smul]⟩
  (localCotangentMapResidue A B).liftBaseChange (ResidueField B)

theorem localCotangentBaseChange_tmul (c : ResidueField B) (ω : CotangentSpace A) :
    localCotangentBaseChange A B (c ⊗ₜ ω) = c • localCotangentMap A B ω :=
  rfl

end LocalRing

section DualBaseChange

variable (k : Type u) (K : Type v) (V : Type w) [Field k] [Field K] [Algebra k K]
  [AddCommGroup V] [Module k V] [Module.Finite k V]

/-- For a finite-dimensional `k`-vector space `V` and a field extension `K/k`, the natural
`K`-linear isomorphism `K ⊗_k V^∨ ≃ (K ⊗_k V)^∨`. -/
def dualBaseChangeEquiv : K ⊗[k] Dual k V ≃ₗ[K] Dual K (K ⊗[k] V) :=
  (TensorProduct.isBaseChange k V K).toDualBaseChange

theorem dualBaseChangeEquiv_tmul_tmul (a : K) (φ : Dual k V) (b : K) (v : V) :
    dualBaseChangeEquiv k K V (a ⊗ₜ φ) (b ⊗ₜ v) = b * a * algebraMap k K (φ v) := by
  have h := (TensorProduct.isBaseChange k V K).toDualBaseChange_tmul a φ v
  have hb : (b ⊗ₜ[k] v : K ⊗[k] V) = b • (TensorProduct.mk k K V 1 v) := by
    simp [TensorProduct.smul_tmul']
  rw [hb, map_smul, smul_eq_mul, mul_assoc]
  exact congrArg (b * ·) h

end DualBaseChange

section TangentMap

variable (A : Type u) (B : Type v) [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
  [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite (ResidueField A) (CotangentSpace A)]

/-- The tangent map `T_B → κ_B ⊗_{κ_A} T_A` of a local homomorphism `A → B`, the transpose of the
scalar-extended cotangent map composed with the inverse of `κ_B ⊗ T_A ≃ (κ_B ⊗ 𝔪_A/𝔪_A²)^∨`. -/
def localTangentMap :
    LocalZariskiTangentSpace B →ₗ[ResidueField B]
      ResidueField B ⊗[ResidueField A] LocalZariskiTangentSpace A :=
  (dualBaseChangeEquiv (ResidueField A) (ResidueField B) (CotangentSpace A)).symm.toLinearMap ∘ₗ
    (localCotangentBaseChange A B).dualMap

/-- The tangent map is dual to the scalar-extended cotangent map. -/
theorem dualBaseChangeEquiv_localTangentMap (v : LocalZariskiTangentSpace B) :
    dualBaseChangeEquiv (ResidueField A) (ResidueField B) (CotangentSpace A)
        (localTangentMap A B v) =
      (localCotangentBaseChange A B).dualMap v := by
  simp [localTangentMap]

theorem dualBaseChangeEquiv_comp_localTangentMap :
    (dualBaseChangeEquiv (ResidueField A) (ResidueField B) (CotangentSpace A)).toLinearMap ∘ₗ
        localTangentMap A B =
      (localCotangentBaseChange A B).dualMap :=
  LinearMap.ext (dualBaseChangeEquiv_localTangentMap A B)

/-- The pairing formula `⟨T(v), c ⊗ ω⟩ = c · v(dω)`. -/
theorem dualBaseChangeEquiv_localTangentMap_tmul (v : LocalZariskiTangentSpace B)
    (c : ResidueField B) (ω : CotangentSpace A) :
    dualBaseChangeEquiv (ResidueField A) (ResidueField B) (CotangentSpace A)
        (localTangentMap A B v) (c ⊗ₜ ω) =
      c * v (localCotangentMap A B ω) := by
  rw [dualBaseChangeEquiv_localTangentMap, LinearMap.dualMap_apply,
    localCotangentBaseChange_tmul, map_smul, smul_eq_mul]

/-- The tangent map is the unique element pairing with `1 ⊗ ω` as `v` pairs with `dω`. -/
theorem localTangentMap_eq_iff (v : LocalZariskiTangentSpace B)
    (t : ResidueField B ⊗[ResidueField A] LocalZariskiTangentSpace A) :
    localTangentMap A B v = t ↔
      ∀ ω : CotangentSpace A,
        dualBaseChangeEquiv (ResidueField A) (ResidueField B) (CotangentSpace A) t (1 ⊗ₜ ω) =
          v (localCotangentMap A B ω) := by
  constructor
  · rintro rfl ω
    rw [dualBaseChangeEquiv_localTangentMap_tmul, one_mul]
  · intro h
    apply (dualBaseChangeEquiv (ResidueField A) (ResidueField B) (CotangentSpace A)).injective
    apply (TensorProduct.isBaseChange (ResidueField A) (CotangentSpace A)
      (ResidueField B)).algHom_ext
    intro ω
    simp only [TensorProduct.mk_apply]
    rw [dualBaseChangeEquiv_localTangentMap_tmul, one_mul, h]

/-- Compatibility with the map on local rings: for `m ∈ 𝔪_A`, the tangent vector `T(v)` pairs
with the class of `m` as `v` pairs with the class of the image of `m` in `𝔪_B`. -/
theorem dualBaseChangeEquiv_localTangentMap_toCotangent (v : LocalZariskiTangentSpace B)
    (m : maximalIdeal A) :
    dualBaseChangeEquiv (ResidueField A) (ResidueField B) (CotangentSpace A)
        (localTangentMap A B v) (1 ⊗ₜ (maximalIdeal A).toCotangent m) =
      v ((maximalIdeal B).toCotangent
        ⟨algebraMap A B m, maximalIdeal_le_comap_ofId A B m.2⟩) := by
  rw [dualBaseChangeEquiv_localTangentMap_tmul, one_mul, localCotangentMap_toCotangent]

end TangentMap

section Comp

variable (A : Type u) (B : Type v) (C : Type w) [CommRing A] [IsLocalRing A] [CommRing B]
  [IsLocalRing B] [CommRing C] [IsLocalRing C] [Algebra A B] [Algebra B C] [Algebra A C]
  [IsScalarTower A B C] [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap B C)]
  [IsLocalHom (algebraMap A C)]

theorem localCotangentMap_comp_apply (ω : CotangentSpace A) :
    localCotangentMap A C ω = localCotangentMap B C (localCotangentMap A B ω) := by
  obtain ⟨m, rfl⟩ := Ideal.toCotangent_surjective (maximalIdeal A) ω
  simp only [localCotangentMap_toCotangent]
  congr 1
  exact Subtype.ext (IsScalarTower.algebraMap_apply A B C m)

variable [Module.Finite (ResidueField A) (CotangentSpace A)]

private theorem dualBaseChangeEquiv_cancelBaseChange_tmul (c : ResidueField C)
    (s : ResidueField B ⊗[ResidueField A] LocalZariskiTangentSpace A) (ω : CotangentSpace A) :
    dualBaseChangeEquiv (ResidueField A) (ResidueField C) (CotangentSpace A)
        (TensorProduct.AlgebraTensorModule.cancelBaseChange (ResidueField A) (ResidueField B)
          (ResidueField C) (ResidueField C) (LocalZariskiTangentSpace A) (c ⊗ₜ s)) (1 ⊗ₜ ω) =
      c * algebraMap (ResidueField B) (ResidueField C)
        (dualBaseChangeEquiv (ResidueField A) (ResidueField B) (CotangentSpace A) s (1 ⊗ₜ ω)) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | add s t hs ht => simp only [TensorProduct.tmul_add, map_add, LinearMap.add_apply, hs, ht,
      mul_add]
  | tmul b χ =>
    rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, dualBaseChangeEquiv_tmul_tmul,
      dualBaseChangeEquiv_tmul_tmul, Algebra.smul_def,
      IsScalarTower.algebraMap_apply (ResidueField A) (ResidueField B) (ResidueField C)]
    simp only [one_mul, map_mul]
    ring

private theorem dualBaseChangeEquiv_cancelBaseChange_baseChange
    [Module.Finite (ResidueField B) (CotangentSpace B)]
    (t : ResidueField C ⊗[ResidueField B] LocalZariskiTangentSpace B) (ω : CotangentSpace A) :
    dualBaseChangeEquiv (ResidueField A) (ResidueField C) (CotangentSpace A)
        (TensorProduct.AlgebraTensorModule.cancelBaseChange (ResidueField A) (ResidueField B)
          (ResidueField C) (ResidueField C) (LocalZariskiTangentSpace A)
          ((localTangentMap A B).baseChange (ResidueField C) t)) (1 ⊗ₜ ω) =
      dualBaseChangeEquiv (ResidueField B) (ResidueField C) (CotangentSpace B) t
        (1 ⊗ₜ localCotangentMap A B ω) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add s t hs ht => simp only [map_add, LinearMap.add_apply, hs, ht]
  | tmul c ψ =>
    rw [LinearMap.baseChange_tmul, dualBaseChangeEquiv_cancelBaseChange_tmul,
      dualBaseChangeEquiv_localTangentMap_tmul, dualBaseChangeEquiv_tmul_tmul]
    simp

/-- **Functoriality of the tangent map.** For local homomorphisms `A → B → C`, the tangent map
of `A → C` is the composite of the tangent map of `B → C`, the scalar extension to `κ_C` of the
tangent map of `A → B`, and the cancellation `κ_C ⊗_{κ_B} (κ_B ⊗_{κ_A} T_A) ≃ κ_C ⊗_{κ_A} T_A`. -/
theorem localTangentMap_comp [Module.Finite (ResidueField B) (CotangentSpace B)] :
    localTangentMap A C =
      (TensorProduct.AlgebraTensorModule.cancelBaseChange (ResidueField A) (ResidueField B)
          (ResidueField C) (ResidueField C) (LocalZariskiTangentSpace A)).toLinearMap ∘ₗ
        (localTangentMap A B).baseChange (ResidueField C) ∘ₗ localTangentMap B C := by
  ext v : 1
  rw [localTangentMap_eq_iff]
  intro ω
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  rw [dualBaseChangeEquiv_cancelBaseChange_baseChange, dualBaseChangeEquiv_localTangentMap_tmul,
    one_mul, localCotangentMap_comp_apply A B C]

end Comp

section Scheme

open AlgebraicGeometry CategoryTheory

variable {X Y Z : Scheme.{u}}

/-- The Zariski tangent space `T_x X = Hom_{k(x)}(𝔪_x/𝔪_x², k(x))` of a scheme at a point. -/
abbrev ZariskiTangentSpace (X : Scheme.{u}) (x : X) : Type u :=
  LocalZariskiTangentSpace (X.presheaf.stalk x)

/-- The stalk map of a morphism of schemes is a local homomorphism, viewed as an algebra map. -/
theorem isLocalHom_stalkMap_algebraMap (f : X ⟶ Y) (x : X) :
    letI := (f.stalkMap x).hom.toAlgebra
    IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
  inferInstanceAs (IsLocalHom (f.stalkMap x).hom)

/-- With the algebra structure given by the stalk map, the induced map of residue fields is the
residue-field map of the morphism. -/
theorem stalkMap_residueField_algebraMap_eq (f : X ⟶ Y) (x : X) :
    letI := (f.stalkMap x).hom.toAlgebra
    haveI := isLocalHom_stalkMap_algebraMap f x
    algebraMap (ResidueField (Y.presheaf.stalk (f x))) (ResidueField (X.presheaf.stalk x)) =
      (f.residueFieldMap x).hom := by
  let _ := (f.stalkMap x).hom.toAlgebra
  have := isLocalHom_stalkMap_algebraMap f x
  ext a
  obtain ⟨a, rfl⟩ := residue_surjective a
  rfl

/-- **The Zariski tangent map** `T_x X → k(x) ⊗_{k(y)} T_y Y` of a morphism `f : X ⟶ Y` at
`x`, with `y = f x`. -/
def zariskiTangentMap (f : X ⟶ Y) (x : X)
    [Module.Finite (ResidueField (Y.presheaf.stalk (f x)))
      (CotangentSpace (Y.presheaf.stalk (f x)))] :
    letI := (f.stalkMap x).hom.toAlgebra
    haveI := isLocalHom_stalkMap_algebraMap f x
    ZariskiTangentSpace X x →ₗ[ResidueField (X.presheaf.stalk x)]
      ResidueField (X.presheaf.stalk x) ⊗[ResidueField (Y.presheaf.stalk (f x))]
        ZariskiTangentSpace Y (f x) :=
  letI := (f.stalkMap x).hom.toAlgebra
  haveI := isLocalHom_stalkMap_algebraMap f x
  localTangentMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)

/-- The cotangent map of `f` at `x` sends the class of `m ∈ 𝔪_y` to the class of its image under
the stalk map. -/
theorem localCotangentMap_stalkMap_toCotangent (f : X ⟶ Y) (x : X)
    (m : maximalIdeal (Y.presheaf.stalk (f x))) :
    letI := (f.stalkMap x).hom.toAlgebra
    haveI := isLocalHom_stalkMap_algebraMap f x
    localCotangentMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
        ((maximalIdeal _).toCotangent m) =
      (maximalIdeal (X.presheaf.stalk x)).toCotangent
        ⟨(f.stalkMap x).hom m, map_nonunit (f.stalkMap x).hom m m.2⟩ := by
  let _ := (f.stalkMap x).hom.toAlgebra
  have := isLocalHom_stalkMap_algebraMap f x
  exact localCotangentMap_toCotangent _ _ m

/-- The scheme tangent map is dual to the scalar-extended cotangent map
`k(x) ⊗_{k(y)} 𝔪_y/𝔪_y² → 𝔪_x/𝔪_x²`. -/
theorem dualBaseChangeEquiv_zariskiTangentMap (f : X ⟶ Y) (x : X)
    [Module.Finite (ResidueField (Y.presheaf.stalk (f x)))
      (CotangentSpace (Y.presheaf.stalk (f x)))]
    (v : ZariskiTangentSpace X x) :
    letI := (f.stalkMap x).hom.toAlgebra
    haveI := isLocalHom_stalkMap_algebraMap f x
    dualBaseChangeEquiv _ _ _ (zariskiTangentMap f x v) =
      (localCotangentBaseChange (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)).dualMap v := by
  let _ := (f.stalkMap x).hom.toAlgebra
  have := isLocalHom_stalkMap_algebraMap f x
  exact dualBaseChangeEquiv_localTangentMap _ _ v

/-- Compatibility of the scheme tangent map with the stalk map: `⟨T_x f(v), 1 ⊗ [m]⟩ = v([f♯ m])`
for `m ∈ 𝔪_y`. -/
theorem dualBaseChangeEquiv_zariskiTangentMap_toCotangent (f : X ⟶ Y) (x : X)
    [Module.Finite (ResidueField (Y.presheaf.stalk (f x)))
      (CotangentSpace (Y.presheaf.stalk (f x)))]
    (v : ZariskiTangentSpace X x) (m : maximalIdeal (Y.presheaf.stalk (f x))) :
    letI := (f.stalkMap x).hom.toAlgebra
    haveI := isLocalHom_stalkMap_algebraMap f x
    dualBaseChangeEquiv _ _ _ (zariskiTangentMap f x v) (1 ⊗ₜ (maximalIdeal _).toCotangent m) =
      v ((maximalIdeal (X.presheaf.stalk x)).toCotangent
        ⟨(f.stalkMap x).hom m, map_nonunit (f.stalkMap x).hom m m.2⟩) := by
  let _ := (f.stalkMap x).hom.toAlgebra
  have := isLocalHom_stalkMap_algebraMap f x
  exact dualBaseChangeEquiv_localTangentMap_toCotangent _ _ v m

/-- The stalk maps of `f`, `g` and `f ≫ g` form a scalar tower. -/
theorem stalkMap_isScalarTower (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    letI := (f.stalkMap x).hom.toAlgebra
    letI := (g.stalkMap (f x)).hom.toAlgebra
    letI : Algebra (Z.presheaf.stalk (g (f x))) (X.presheaf.stalk x) :=
      ((f ≫ g).stalkMap x).hom.toAlgebra
    IsScalarTower (Z.presheaf.stalk (g (f x))) (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := by
  let _ := (f.stalkMap x).hom.toAlgebra
  let _ := (g.stalkMap (f x)).hom.toAlgebra
  let _ : Algebra (Z.presheaf.stalk (g (f x))) (X.presheaf.stalk x) :=
    ((f ≫ g).stalkMap x).hom.toAlgebra
  refine IsScalarTower.of_algebraMap_eq' ?_
  change ((f ≫ g).stalkMap x).hom = (f.stalkMap x).hom.comp (g.stalkMap (f x)).hom
  rw [Scheme.Hom.stalkMap_comp]
  rfl

/-- **Functoriality of the Zariski tangent map.** For `f : X ⟶ Y`, `g : Y ⟶ Z` and `x : X`,
with `y = f x` and `z = g y`, the tangent map of `f ≫ g` at `x` is the composite
`T_x X → k(x) ⊗_{k(y)} T_y Y → k(x) ⊗_{k(y)} (k(y) ⊗_{k(z)} T_z Z) ≃ k(x) ⊗_{k(z)} T_z Z`. -/
theorem zariskiTangentMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
    [Module.Finite (ResidueField (Y.presheaf.stalk (f x)))
      (CotangentSpace (Y.presheaf.stalk (f x)))]
    [Module.Finite (ResidueField (Z.presheaf.stalk (g (f x))))
      (CotangentSpace (Z.presheaf.stalk (g (f x))))] :
    letI := (f.stalkMap x).hom.toAlgebra
    letI := (g.stalkMap (f x)).hom.toAlgebra
    letI : Algebra (Z.presheaf.stalk (g (f x))) (X.presheaf.stalk x) :=
      ((f ≫ g).stalkMap x).hom.toAlgebra
    haveI := isLocalHom_stalkMap_algebraMap f x
    haveI := isLocalHom_stalkMap_algebraMap g (f x)
    haveI : IsLocalHom (algebraMap (Z.presheaf.stalk (g (f x))) (X.presheaf.stalk x)) :=
      isLocalHom_stalkMap_algebraMap (f ≫ g) x
    haveI := stalkMap_isScalarTower f g x
    haveI : Module.Finite (ResidueField (Z.presheaf.stalk ((f ≫ g) x)))
        (CotangentSpace (Z.presheaf.stalk ((f ≫ g) x))) :=
      inferInstanceAs (Module.Finite (ResidueField (Z.presheaf.stalk (g (f x))))
        (CotangentSpace (Z.presheaf.stalk (g (f x)))))
    zariskiTangentMap (f ≫ g) x =
      (TensorProduct.AlgebraTensorModule.cancelBaseChange
          (ResidueField (Z.presheaf.stalk (g (f x)))) (ResidueField (Y.presheaf.stalk (f x)))
          (ResidueField (X.presheaf.stalk x)) (ResidueField (X.presheaf.stalk x))
          (ZariskiTangentSpace Z (g (f x)))).toLinearMap ∘ₗ
        (zariskiTangentMap g (f x)).baseChange (ResidueField (X.presheaf.stalk x)) ∘ₗ
          zariskiTangentMap f x := by
  let _ := (f.stalkMap x).hom.toAlgebra
  let _ := (g.stalkMap (f x)).hom.toAlgebra
  let _ : Algebra (Z.presheaf.stalk (g (f x))) (X.presheaf.stalk x) :=
    ((f ≫ g).stalkMap x).hom.toAlgebra
  have := isLocalHom_stalkMap_algebraMap f x
  have := isLocalHom_stalkMap_algebraMap g (f x)
  have : IsLocalHom (algebraMap (Z.presheaf.stalk (g (f x))) (X.presheaf.stalk x)) :=
    isLocalHom_stalkMap_algebraMap (f ≫ g) x
  have := stalkMap_isScalarTower f g x
  exact localTangentMap_comp (Z.presheaf.stalk (g (f x))) (Y.presheaf.stalk (f x))
    (X.presheaf.stalk x)

end Scheme

end

end Hartshorne

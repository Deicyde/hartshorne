/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Weil.RationalEllAdicCohomology
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.Algebra.Group.Shrink
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# Roots of unity and Tate twists on the small étale site

For a scheme `X` and a natural number `n`, this file constructs the sheaf `μ_n` of `n`-th roots
of unity on the small étale site of `X`: its sections over an étale `X`-scheme `U` are the
`n`-th roots of unity in `Γ(U, 𝒪_U)`, written additively.  The sheaf property comes from
representability: the presheaf `U ↦ μ_n(Γ(U, 𝒪_U))` on all schemes is represented by
`Spec ℤ[ℤ/n]`, hence is a sheaf for the fpqc topology (which is subcanonical), hence for the
étale topology, and it restricts to the small étale site along the continuous forgetful functor.

With `ℤ/ℓ^r(1) = μ_{ℓ^r}`, the transition maps `μ_{ℓ^s} ⟶ μ_{ℓ^r}`, `ζ ↦ ζ ^ (ℓ ^ (s - r))`
(`r ≤ s`) form the inverse system `ℤ_ℓ(1)`.  The tensor product of two sheaves of abelian groups
is the sheafification of the pointwise tensor product over `ℤ`; tensor powers of `μ_{ℓ^r}` give
the nonnegative twists `ℤ/ℓ^r(q)`, `q ≥ 0` (with `ℤ/ℓ^r(0)` the constant sheaf `ℤ/ℓ^r`), their
inverse systems in `r`, and the classical groups `lim_r H^i_et(X, ℤ/ℓ^r(q))`.

The internal Hom `U ↦ Hom(F|_U, G|_U)` of two abelian sheaves is a sheaf of `u`-small abelian
groups: a morphism `F|_U ⟶ G|_U` is determined by its components at the essentially small family
of affine étale schemes over `U`.  The negative twists are `ℤ/ℓ^r(-1) = Hom(μ_{ℓ^r}, ℤ/ℓ^r)` and
its tensor powers.  The transition `ℤ/ℓ^s(-1) → ℤ/ℓ^r(-1)` restricts `τ : μ_{ℓ^s} → ℤ/ℓ^s` to
`μ_{ℓ^r}` and divides by `ℓ ^ (s - r)`: the restriction is killed by `ℓ ^ r`, and the
`ℓ^r`-torsion of `ℤ/ℓ^s` is `ℓ^(s-r) ℤ/ℓ^s ≅ ℤ/ℓ^r`, also on sections of the constant sheaves
because taking sections of constant sheaves is left exact.  Together these give `ℤ_ℓ(q)` for every
integer `q`, and the groups `H^i(X, ℤ_ℓ(q)) = lim_r H^i_et(X, ℤ/ℓ^r(q))`.  Since `ℓ^r` kills
`ℤ/ℓ^r(q)`, the construction of `Hartshorne.Weil.RationalEllAdicCohomology` (redone here for any
inverse system whose `r`-th stage is killed by `ℓ ^ r`) makes `H^i(X, ℤ_ℓ(q))` a
`ℤ_[ℓ]`-module, and `H^i(X, ℚ_ℓ(q)) = ℚ_ℓ ⊗_{ℤ_ℓ} H^i(X, ℤ_ℓ(q))`; for `q = 0` both agree
definitionally with `Hartshorne.Weil.RationalEllAdicCohomology`.

Except for the transition maps of negative twists, which need `ℓ ≠ 0`, no hypothesis on `ℓ` is
needed for these constructions, apart from `ℓ` prime for `ℤ_[ℓ]` and `ℚ_[ℓ]`; invertibility of
`ℓ` on `X` enters only in theorems about them.

## Main declarations

- `AlgebraicGeometry.Scheme.etaleRootsOfUnitySheaf X n`: the sheaf `μ_n` on `X_et`.
- `AlgebraicGeometry.Scheme.isSheaf_fpqcTopology_rootsOfUnityPresheaf`: `U ↦ μ_n(Γ(U, 𝒪_U))` is
  an fpqc sheaf on schemes.
- `AlgebraicGeometry.Scheme.etaleTateTwistOne X ℓ r`: `ℤ/ℓ^r(1) = μ_{ℓ^r}`.
- `AlgebraicGeometry.Scheme.etaleTateTwistOneSystem X ℓ`: the inverse system `r ↦ μ_{ℓ^r}`.
- `Hartshorne.sheafTensor J F G`, `Hartshorne.sheafTensorPowSucc J F k`: tensor products and
  tensor powers of sheaves of abelian groups.
- `AlgebraicGeometry.Scheme.etaleTateTwistNat X ℓ r q`: `ℤ/ℓ^r(q)` for `q ≥ 0`, and
  `AlgebraicGeometry.Scheme.etaleTateTwistNatSystem X ℓ q`: the inverse system in `r`.
- `AlgebraicGeometry.Scheme.etaleSheafHom F G`: the internal Hom of abelian sheaves on `X_et`.
- `AlgebraicGeometry.Scheme.etaleTateTwist X ℓ r q`: `ℤ/ℓ^r(q)` for every integer `q`, and
  `AlgebraicGeometry.Scheme.etaleTateTwistSystem X ℓ q`: the inverse system `ℤ_ℓ(q)`.
- `AlgebraicGeometry.Scheme.classicalEllAdicCohomologyTwist X ℓ q i` and
  `AlgebraicGeometry.Scheme.rationalEllAdicCohomologyTwist X ℓ q i`: `H^i(X, ℤ_ℓ(q))` and
  `H^i(X, ℚ_ℓ(q))`.
-/

open CategoryTheory Limits Opposite

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u v w

namespace Hartshorne

/-- The group ring `ℤ[ℤ/n]`, which represents `n`-th roots of unity. -/
abbrev RootsOfUnityRing (n : ℕ) : Type := MonoidAlgebra ℤ (Multiplicative (ZMod n))

/-- The tautological `n`-th root of unity of `ℤ[ℤ/n]`: the image of the generator of `ℤ/n`. -/
noncomputable def universalRootOfUnity (n : ℕ) : rootsOfUnity n (RootsOfUnityRing n) :=
  ⟨(MonoidAlgebra.of ℤ (Multiplicative (ZMod n))).toHomUnits (Multiplicative.ofAdd 1), by
    rw [mem_rootsOfUnity, ← map_pow, ← ofAdd_nsmul, nsmul_one, ZMod.natCast_self, ofAdd_zero,
      map_one]⟩

/-- The class of `1` generates `ℤ/n`, written multiplicatively. -/
lemma mem_zpowers_ofAdd_one (n : ℕ) (x : Multiplicative (ZMod n)) :
    x ∈ Subgroup.zpowers (Multiplicative.ofAdd (1 : ZMod n)) := by
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨((Multiplicative.toAdd x).cast : ℤ), ?_⟩
  rw [← ofAdd_zsmul, zsmul_one, ZMod.intCast_zmod_cast, ofAdd_toAdd]

variable {A : Type*} [CommRing A]

/-- Ring homomorphisms out of `ℤ[ℤ/n]` correspond to `n`-th roots of unity: a ring
homomorphism `φ` corresponds to the image of the tautological root of unity. -/
theorem bijective_restrictRootsOfUnity_universalRootOfUnity (n : ℕ) :
    Function.Bijective (fun φ : RootsOfUnityRing n →+* A ↦
      restrictRootsOfUnity φ n (universalRootOfUnity n)) := by
  constructor
  · intro φ ψ h
    have hu : (Units.map (φ : RootsOfUnityRing n →* A)).comp
          (MonoidAlgebra.of ℤ (Multiplicative (ZMod n))).toHomUnits =
        (Units.map (ψ : RootsOfUnityRing n →* A)).comp
          (MonoidAlgebra.of ℤ (Multiplicative (ZMod n))).toHomUnits :=
      (MonoidHom.eq_iff_eq_on_generator (mem_zpowers_ofAdd_one n) _ _).2
        (congrArg (fun ζ : rootsOfUnity n A ↦ (ζ : Aˣ)) h)
    apply MonoidAlgebra.ringHom_ext
    · intro r
      have := RingHom.ext_int (φ.comp MonoidAlgebra.singleOneRingHom)
        (ψ.comp MonoidAlgebra.singleOneRingHom)
      exact congrArg (fun f : ℤ →+* A ↦ f r) this
    · intro m
      exact congrArg (fun f : Multiplicative (ZMod n) →* Aˣ ↦ ((f m : Aˣ) : A)) hu
  · intro ζ
    have hord : orderOf (ζ : Aˣ) ∣ orderOf (Multiplicative.ofAdd (1 : ZMod n)) := by
      rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
      exact orderOf_dvd_of_pow_eq_one ((mem_rootsOfUnity _ _).1 ζ.2)
    let ψ := monoidHomOfForallMemZpowers (mem_zpowers_ofAdd_one n) hord
    refine ⟨(MonoidAlgebra.lift ℤ A (Multiplicative (ZMod n))
      ((Units.coeHom A).comp ψ)).toRingHom, ?_⟩
    apply Subtype.ext
    apply Units.ext
    change MonoidAlgebra.lift ℤ A (Multiplicative (ZMod n)) ((Units.coeHom A).comp ψ)
      (MonoidAlgebra.of ℤ _ (Multiplicative.ofAdd 1)) = ((ζ : Aˣ) : A)
    rw [MonoidAlgebra.lift_of]
    simp [ψ]

/-- The universe-lifted group ring `ℤ[ℤ/n]`, as a commutative ring in universe `u`. -/
noncomputable abbrev rootsOfUnityRingCat (n : ℕ) : CommRingCat.{u} :=
  CommRingCat.of (ULift.{u} (RootsOfUnityRing n))

/-- The tautological `n`-th root of unity of the universe-lifted group ring. -/
noncomputable def universalRootOfUnityULift (n : ℕ) :
    rootsOfUnity n (rootsOfUnityRingCat.{u} n) :=
  restrictRootsOfUnity (ULift.ringEquiv.{0, u} (R := RootsOfUnityRing n)).symm n
    (universalRootOfUnity n)

/-- The universe-lifted group ring `ℤ[ℤ/n]` also represents `n`-th roots of unity. -/
theorem bijective_restrictRootsOfUnity_universalRootOfUnityULift (n : ℕ) :
    Function.Bijective (fun φ : rootsOfUnityRingCat.{u} n →+* A ↦
      restrictRootsOfUnity φ n (universalRootOfUnityULift n)) := by
  let e : (rootsOfUnityRingCat.{u} n →+* A) ≃ (RootsOfUnityRing n →+* A) :=
    { toFun φ := φ.comp (ULift.ringEquiv.{0, u} (R := RootsOfUnityRing n)).symm.toRingHom
      invFun ψ := ψ.comp (ULift.ringEquiv.{0, u} (R := RootsOfUnityRing n)).toRingHom
      left_inv φ := RingHom.ext fun _ ↦ rfl
      right_inv ψ := RingHom.ext fun _ ↦ rfl }
  have h := (bijective_restrictRootsOfUnity_universalRootOfUnity (A := A) n).comp e.bijective
  convert h using 1
  funext φ
  exact Subtype.ext (Units.ext rfl)

/-- The functor `A ↦ μ_n(A)` from commutative rings to abelian groups, the group of `n`-th
roots of unity being written additively. -/
@[simps]
noncomputable def rootsOfUnityFunctor (n : ℕ) : CommRingCat.{u} ⥤ Ab.{u} where
  obj A := AddCommGrpCat.of (Additive (rootsOfUnity n A))
  map f := AddCommGrpCat.ofHom (restrictRootsOfUnity f.hom n).toAdditive
  map_id A := by
    ext ζ
    exact Subtype.ext (Units.ext rfl)
  map_comp f g := by
    ext ζ
    exact Subtype.ext (Units.ext rfl)

/-- Raising to the `k`-th power sends `n`-th roots of unity to `m`-th roots of unity when
`k * m = n`. -/
@[simps]
def rootsOfUnityPowHom (B : Type*) [CommMonoid B] {k m n : ℕ} (h : k * m = n) :
    rootsOfUnity n B →* rootsOfUnity m B where
  toFun ζ := ⟨(ζ : Bˣ) ^ k, by
    rw [mem_rootsOfUnity, ← pow_mul, h]
    exact (mem_rootsOfUnity _ _).1 ζ.2⟩
  map_one' := Subtype.ext (one_pow k)
  map_mul' a b := Subtype.ext (mul_pow _ _ k)

/-- The natural transformation `μ_n ⟶ μ_m`, `ζ ↦ ζ ^ k`, when `k * m = n`. -/
@[simps]
noncomputable def rootsOfUnityFunctorPow {k m n : ℕ} (h : k * m = n) :
    rootsOfUnityFunctor.{u} n ⟶ rootsOfUnityFunctor m where
  app A := AddCommGrpCat.ofHom (rootsOfUnityPowHom A h).toAdditive
  naturality A B f := by
    ext ζ
    exact Subtype.ext (Units.ext (map_pow f.hom _ k).symm)

/-- The inverse system `r ↦ μ_{ℓ^r}` of functors on commutative rings, with transition maps
`μ_{ℓ^s} ⟶ μ_{ℓ^r}`, `ζ ↦ ζ ^ (ℓ ^ (s - r))`, for `r ≤ s`. -/
@[simps]
noncomputable def rootsOfUnityFunctorSystem (ℓ : ℕ) : ℕᵒᵖ ⥤ (CommRingCat.{u} ⥤ Ab.{u}) where
  obj r := rootsOfUnityFunctor (ℓ ^ r.unop)
  map f := rootsOfUnityFunctorPow (pow_sub_mul_pow ℓ (leOfHom f.unop))
  map_id r := by
    ext A ζ
    refine Subtype.ext (Units.ext ?_)
    change (((Additive.toMul ζ : rootsOfUnity _ A) : Aˣ) : A) ^ (ℓ ^ (r.unop - r.unop)) =
      (((Additive.toMul ζ : rootsOfUnity _ A) : Aˣ) : A)
    simp
  map_comp {r s t} f g := by
    ext A ζ
    refine Subtype.ext (Units.ext ?_)
    have h1 := leOfHom f.unop
    have h2 := leOfHom g.unop
    change (((Additive.toMul ζ : rootsOfUnity _ A) : Aˣ) : A) ^ (ℓ ^ (r.unop - t.unop)) =
      ((((Additive.toMul ζ : rootsOfUnity _ A) : Aˣ) : A) ^ (ℓ ^ (r.unop - s.unop))) ^
        (ℓ ^ (s.unop - t.unop))
    rw [← pow_mul, ← pow_add]
    congr 2
    omega

end Hartshorne

namespace AlgebraicGeometry.Scheme

open Hartshorne

/-- The presheaf `U ↦ μ_n(Γ(U, 𝒪_U))` of `n`-th roots of unity on the category of schemes. -/
noncomputable def rootsOfUnityPresheaf (n : ℕ) : Scheme.{u}ᵒᵖ ⥤ Ab.{u} :=
  Scheme.Γ ⋙ rootsOfUnityFunctor n

/-- A morphism `U ⟶ Spec ℤ[ℤ/n]` gives an `n`-th root of unity in `Γ(U, 𝒪_U)`: the image of
the tautological root of unity. -/
noncomputable def rootOfUnityOfHomSpec (n : ℕ) {U : Scheme.{u}}
    (g : U ⟶ Spec (rootsOfUnityRingCat n)) :
    rootsOfUnity n Γ(U, ⊤) :=
  restrictRootsOfUnity ((Scheme.ΓSpecIso _).inv ≫ g.appTop).hom n (universalRootOfUnityULift n)

/-- Morphisms `U ⟶ Spec ℤ[ℤ/n]` correspond to `n`-th roots of unity in `Γ(U, 𝒪_U)`. -/
theorem bijective_rootOfUnityOfHomSpec (n : ℕ) (U : Scheme.{u}) :
    Function.Bijective (rootOfUnityOfHomSpec n (U := U)) := by
  have h1 : Function.Bijective (fun g : U ⟶ Spec (rootsOfUnityRingCat n) ↦
      ((Scheme.ΓSpecIso _).inv ≫ g.appTop)) := by
    refine ⟨fun g g' h ↦ ext_to_Spec h, fun φ ↦ ⟨ΓSpec.adjunction.homEquiv U (op _) φ.op, ?_⟩⟩
    exact ΓSpecIso_inv_ΓSpec_adjunction_homEquiv φ
  have h2 : Function.Bijective (fun φ : rootsOfUnityRingCat.{u} n ⟶ Γ(U, ⊤) ↦
      restrictRootsOfUnity φ.hom n (universalRootOfUnityULift n)) :=
    (bijective_restrictRootsOfUnity_universalRootOfUnityULift n).comp
      ⟨fun _ _ h ↦ CommRingCat.hom_ext h, fun f ↦ ⟨CommRingCat.ofHom f, rfl⟩⟩
  exact h2.comp h1

/-- The presheaf of `n`-th roots of unity on schemes is represented by `Spec ℤ[ℤ/n]`. -/
noncomputable def rootsOfUnityPresheafRepresentableIso (n : ℕ) :
    yoneda.obj (Spec (rootsOfUnityRingCat.{u} n)) ≅
      rootsOfUnityPresheaf n ⋙ CategoryTheory.forget Ab.{u} :=
  NatIso.ofComponents
    (fun U ↦ Equiv.toIso ((Equiv.ofBijective _ (bijective_rootOfUnityOfHomSpec n U.unop)).trans
      Additive.ofMul))
    (by
      intro U V f
      ext g
      apply Subtype.ext
      apply Units.ext
      simp [rootOfUnityOfHomSpec, rootsOfUnityPresheaf]
      rfl)

/-- The presheaf of `n`-th roots of unity is a sheaf for the fpqc topology on schemes. -/
theorem isSheaf_fpqcTopology_rootsOfUnityPresheaf (n : ℕ) :
    Presheaf.IsSheaf fpqcTopology (rootsOfUnityPresheaf.{u} n) := by
  apply Presheaf.isSheaf_of_isSheaf_comp _ _ (CategoryTheory.forget Ab.{u})
  rw [← Presheaf.isSheaf_of_iso_iff (rootsOfUnityPresheafRepresentableIso n),
    isSheaf_iff_isSheaf_of_type]
  exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _

/-- Every étale covering is an fpqc covering. -/
lemma etaleTopology_le_fpqcTopology : etaleTopology.{u} ≤ fpqcTopology :=
  etaleTopology_le_proetaleTopology.trans proetaleTopology_le_fpqcTopology

/-- The presheaf of `n`-th roots of unity is a sheaf for the étale topology on schemes. -/
theorem isSheaf_etaleTopology_rootsOfUnityPresheaf (n : ℕ) :
    Presheaf.IsSheaf etaleTopology (rootsOfUnityPresheaf.{u} n) :=
  (isSheaf_fpqcTopology_rootsOfUnityPresheaf n).of_le etaleTopology_le_fpqcTopology

/-- The forgetful functor from the small étale site to schemes over `X` preserves finite limits. -/
instance (X : Scheme.{u}) : PreservesFiniteLimits (Etale.forget X) :=
  inferInstanceAs (PreservesFiniteLimits (MorphismProperty.Over.forget _ _ _))

/-- The forgetful functor from the small étale site to schemes over `X` is representably flat. -/
instance (X : Scheme.{u}) : RepresentablyFlat (Etale.forget X) :=
  flat_of_preservesFiniteLimits _

/-- The forgetful functor from the small étale site of `X` to schemes over `X` is continuous. -/
instance isContinuous_etaleForget (X : Scheme.{u}) :
    (Etale.forget X).IsContinuous X.smallEtaleTopology (etaleTopology.over X) := by
  rw [Functor.isContinuous_iff_coverPreserving]
  exact Functor.coverPreserving_restrictedTopology (MorphismProperty.Over.forget _ ⊤ X) _

/-- The forgetful functor from the small étale site of `X` to all schemes is continuous for the
étale topology. -/
instance isContinuous_etaleForget_comp_overForget (X : Scheme.{u}) :
    (Etale.forget X ⋙ CategoryTheory.Over.forget X).IsContinuous X.smallEtaleTopology
      etaleTopology :=
  Functor.isContinuous_comp _ _ _ (etaleTopology.over X) _

/-- The big-site sheaf of `n`-th roots of unity, for the étale topology. -/
noncomputable def rootsOfUnityEtaleBigSheaf (n : ℕ) : Sheaf etaleTopology.{u} Ab.{u} :=
  ⟨rootsOfUnityPresheaf n, isSheaf_etaleTopology_rootsOfUnityPresheaf n⟩

/-- The sheaf `μ_n` of `n`-th roots of unity on the small étale site of `X`:
its sections over an étale `X`-scheme `U` are the `n`-th roots of unity in `Γ(U, 𝒪_U)`, written
additively. -/
noncomputable def etaleRootsOfUnitySheaf (X : Scheme.{u}) (n : ℕ) :
    Sheaf X.smallEtaleTopology Ab.{u} :=
  ((Etale.forget X ⋙ CategoryTheory.Over.forget X).sheafPushforwardContinuous Ab.{u}
    X.smallEtaleTopology etaleTopology).obj (rootsOfUnityEtaleBigSheaf n)

/-- The sections of `μ_n` over an étale `X`-scheme `U` are the `n`-th roots of unity in
`Γ(U, 𝒪_U)`. -/
theorem etaleRootsOfUnitySheaf_obj_obj (X : Scheme.{u}) (n : ℕ) (U : X.Etale) :
    (X.etaleRootsOfUnitySheaf n).obj.obj (op U) =
      AddCommGrpCat.of (Additive (rootsOfUnity n Γ(U.left, ⊤))) :=
  rfl

/-- The inverse system `r ↦ μ_{ℓ^r}` of étale sheaves on the category of schemes. -/
noncomputable def rootsOfUnityEtaleBigSystem (ℓ : ℕ) : ℕᵒᵖ ⥤ Sheaf etaleTopology.{u} Ab.{u} :=
  ObjectProperty.lift _ (rootsOfUnityFunctorSystem ℓ ⋙ (Functor.whiskeringLeft _ _ _).obj Scheme.Γ)
    (fun r ↦ isSheaf_etaleTopology_rootsOfUnityPresheaf (ℓ ^ r.unop))

/-- The étale Tate twist `ℤ/ℓ^r(1) = μ_{ℓ^r}` on the small étale site of `X`. -/
noncomputable abbrev etaleTateTwistOne (X : Scheme.{u}) (ℓ r : ℕ) :
    Sheaf X.smallEtaleTopology Ab.{u} :=
  X.etaleRootsOfUnitySheaf (ℓ ^ r)

/-- The inverse system `r ↦ ℤ/ℓ^r(1) = μ_{ℓ^r}` of sheaves on the small étale site of `X`, with
transition maps `μ_{ℓ^s} ⟶ μ_{ℓ^r}`, `ζ ↦ ζ ^ (ℓ ^ (s - r))`, for `r ≤ s`; this is the
`ℓ`-adic sheaf `ℤ_ℓ(1)`. -/
noncomputable def etaleTateTwistOneSystem (X : Scheme.{u}) (ℓ : ℕ) :
    ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology Ab.{u} :=
  rootsOfUnityEtaleBigSystem ℓ ⋙
    (Etale.forget X ⋙ CategoryTheory.Over.forget X).sheafPushforwardContinuous Ab.{u}
      X.smallEtaleTopology etaleTopology

/-- The `r`-th stage of `ℤ_ℓ(1)` is `μ_{ℓ^r}`. -/
theorem etaleTateTwistOneSystem_obj (X : Scheme.{u}) (ℓ : ℕ) (r : ℕᵒᵖ) :
    (X.etaleTateTwistOneSystem ℓ).obj r = X.etaleTateTwistOne ℓ r.unop :=
  rfl

end AlgebraicGeometry.Scheme

namespace Hartshorne

section Tensor

variable {C : Type*} [Category C]

/-- The pointwise tensor product `U ↦ F(U) ⊗_ℤ G(U)` of two presheaves of abelian groups. -/
@[simps]
noncomputable def presheafTensor (F G : Cᵒᵖ ⥤ Ab.{u}) : Cᵒᵖ ⥤ Ab.{u} where
  obj U := AddCommGrpCat.of (TensorProduct ℤ (F.obj U) (G.obj U))
  map f := AddCommGrpCat.ofHom (TensorProduct.map (F.map f).hom.toIntLinearMap
    (G.map f).hom.toIntLinearMap).toAddMonoidHom
  map_id U := by
    ext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add x y hx hy => simp_all
  map_comp f g := by
    ext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add x y hx hy => simp_all

/-- The pointwise tensor product of two morphisms of presheaves of abelian groups. -/
@[simps]
noncomputable def presheafTensorMap {F F' G G' : Cᵒᵖ ⥤ Ab.{u}} (α : F ⟶ F') (β : G ⟶ G') :
    presheafTensor F G ⟶ presheafTensor F' G' where
  app U := AddCommGrpCat.ofHom (TensorProduct.map (α.app U).hom.toIntLinearMap
    (β.app U).hom.toIntLinearMap).toAddMonoidHom
  naturality U V f := by
    ext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      change (α.app V (F.map f a)) ⊗ₜ[ℤ] (β.app V (G.map f b)) =
        (F'.map f (α.app U a)) ⊗ₜ[ℤ] (G'.map f (β.app U b))
      rw [NatTrans.naturality_apply, NatTrans.naturality_apply]
    | add x y hx hy => simp_all

/-- The pointwise tensor product is functorial: identities. -/
theorem presheafTensorMap_id (F G : Cᵒᵖ ⥤ Ab.{u}) :
    presheafTensorMap (𝟙 F) (𝟙 G) = 𝟙 (presheafTensor F G) := by
  ext U x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add x y hx hy => simp_all

/-- The pointwise tensor product is functorial: composition. -/
theorem presheafTensorMap_comp {F F' F'' G G' G'' : Cᵒᵖ ⥤ Ab.{u}} (α : F ⟶ F') (α' : F' ⟶ F'')
    (β : G ⟶ G') (β' : G' ⟶ G'') :
    presheafTensorMap (α ≫ α') (β ≫ β') = presheafTensorMap α β ≫ presheafTensorMap α' β' := by
  ext U x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add x y hx hy => simp_all

end Tensor

section SheafTensor

variable {C : Type w} [Category.{v} C] (J : GrothendieckTopology C) [HasSheafify J Ab.{u}]

/-- The tensor product `F ⊗ G` of two sheaves of abelian groups: the sheafification of the
pointwise tensor product `U ↦ F(U) ⊗_ℤ G(U)`. -/
noncomputable def sheafTensor (F G : Sheaf J Ab.{u}) : Sheaf J Ab.{u} :=
  (presheafToSheaf J Ab.{u}).obj (presheafTensor F.obj G.obj)

/-- The tensor product of two morphisms of sheaves of abelian groups. -/
noncomputable def sheafTensorMap {F F' G G' : Sheaf J Ab.{u}} (α : F ⟶ F') (β : G ⟶ G') :
    sheafTensor J F G ⟶ sheafTensor J F' G' :=
  (presheafToSheaf J Ab.{u}).map (presheafTensorMap α.hom β.hom)

/-- The tensor product of sheaves is functorial: identities. -/
theorem sheafTensorMap_id (F G : Sheaf J Ab.{u}) :
    sheafTensorMap J (𝟙 F) (𝟙 G) = 𝟙 (sheafTensor J F G) := by
  simp only [sheafTensorMap, ObjectProperty.FullSubcategory.id_hom, presheafTensorMap_id]
  exact (presheafToSheaf J Ab.{u}).map_id _

/-- The tensor product of sheaves is functorial: composition. -/
theorem sheafTensorMap_comp {F F' F'' G G' G'' : Sheaf J Ab.{u}} (α : F ⟶ F') (α' : F' ⟶ F'')
    (β : G ⟶ G') (β' : G' ⟶ G'') :
    sheafTensorMap J (α ≫ α') (β ≫ β') = sheafTensorMap J α β ≫ sheafTensorMap J α' β' := by
  simp only [sheafTensorMap, ObjectProperty.FullSubcategory.comp_hom, presheafTensorMap_comp,
    Functor.map_comp]

/-- The tensor power `F^{⊗(k+1)} = F ⊗ ⋯ ⊗ F` (`k + 1` factors, bracketed to the left) of a
sheaf of abelian groups. -/
noncomputable def sheafTensorPowSucc (F : Sheaf J Ab.{u}) : ℕ → Sheaf J Ab.{u}
  | 0 => F
  | k + 1 => sheafTensor J (sheafTensorPowSucc F k) F

/-- The tensor power `α^{⊗(k+1)}` of a morphism of sheaves of abelian groups. -/
noncomputable def sheafTensorPowSuccMap {F G : Sheaf J Ab.{u}} (α : F ⟶ G) :
    (k : ℕ) → sheafTensorPowSucc J F k ⟶ sheafTensorPowSucc J G k
  | 0 => α
  | k + 1 => sheafTensorMap J (sheafTensorPowSuccMap α k) α

/-- Tensor powers are functorial: identities. -/
theorem sheafTensorPowSuccMap_id (F : Sheaf J Ab.{u}) (k : ℕ) :
    sheafTensorPowSuccMap J (𝟙 F) k = 𝟙 (sheafTensorPowSucc J F k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change sheafTensorMap J (sheafTensorPowSuccMap J (𝟙 F) k) (𝟙 F) = _
    rw [ih, sheafTensorMap_id]
    rfl

/-- Tensor powers are functorial: composition. -/
theorem sheafTensorPowSuccMap_comp {F G H : Sheaf J Ab.{u}} (α : F ⟶ G) (β : G ⟶ H) (k : ℕ) :
    sheafTensorPowSuccMap J (α ≫ β) k =
      sheafTensorPowSuccMap J α k ≫ sheafTensorPowSuccMap J β k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change sheafTensorMap J (sheafTensorPowSuccMap J (α ≫ β) k) (α ≫ β) =
      sheafTensorMap J (sheafTensorPowSuccMap J α k) α ≫
        sheafTensorMap J (sheafTensorPowSuccMap J β k) β
    rw [ih, sheafTensorMap_comp]

/-- The tensor power functor `F ↦ F^{⊗(k+1)}` on sheaves of abelian groups. -/
@[simps]
noncomputable def sheafTensorPowSuccFunctor (k : ℕ) : Sheaf J Ab.{u} ⥤ Sheaf J Ab.{u} where
  obj F := sheafTensorPowSucc J F k
  map α := sheafTensorPowSuccMap J α k
  map_id F := sheafTensorPowSuccMap_id J F k
  map_comp α β := sheafTensorPowSuccMap_comp J α β k

end SheafTensor


end Hartshorne

namespace AlgebraicGeometry.Scheme

open Hartshorne

/-- The étale Tate twist `ℤ/ℓ^r(q)` for `q ≥ 0` on the small étale site of `X`: the constant sheaf
`ℤ/ℓ^r` for `q = 0`, and the tensor power `μ_{ℓ^r}^{⊗q}` for `q ≥ 1`. -/
noncomputable def etaleTateTwistNat (X : Scheme.{u}) (ℓ r : ℕ) :
    ℕ → Sheaf X.smallEtaleTopology Ab.{u}
  | 0 => X.constantTorsionEtaleSheaf ℓ r
  | q + 1 => sheafTensorPowSucc X.smallEtaleTopology (X.etaleTateTwistOne ℓ r) q

/-- The twist `ℤ/ℓ^r(1)` is `μ_{ℓ^r}`. -/
theorem etaleTateTwistNat_one (X : Scheme.{u}) (ℓ r : ℕ) :
    X.etaleTateTwistNat ℓ r 1 = X.etaleTateTwistOne ℓ r :=
  rfl

/-- The inverse system `r ↦ ℤ/ℓ^r(q)` (`q ≥ 0`) of sheaves on the small étale site of `X`: the
reduction maps of the constant sheaves for `q = 0`, and the `q`-th tensor powers of the transition
maps `μ_{ℓ^s} ⟶ μ_{ℓ^r}` for `q ≥ 1`.  This is the `ℓ`-adic sheaf `ℤ_ℓ(q)`. -/
noncomputable def etaleTateTwistNatSystem (X : Scheme.{u}) (ℓ : ℕ) :
    ℕ → ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology Ab.{u}
  | 0 => X.constantTorsionEtaleSheafSystem ℓ
  | q + 1 => X.etaleTateTwistOneSystem ℓ ⋙ sheafTensorPowSuccFunctor X.smallEtaleTopology q

/-- The `r`-th stage of `ℤ_ℓ(q)` is `ℤ/ℓ^r(q)`. -/
theorem etaleTateTwistNatSystem_obj (X : Scheme.{u}) (ℓ q : ℕ) (r : ℕᵒᵖ) :
    (X.etaleTateTwistNatSystem ℓ q).obj r = X.etaleTateTwistNat ℓ r.unop q := by
  cases q <;> rfl

/-- The inverse system `r ↦ H^i_et(X, ℤ/ℓ^r(q))` (`q ≥ 0`) of torsion étale cohomology groups with
twisted coefficients. -/
noncomputable def twistedTorsionEtaleCohomologySystem (X : Scheme.{u}) (ℓ q i : ℕ) :
    ℕᵒᵖ ⥤ Ab.{u} :=
  X.etaleTateTwistNatSystem ℓ q ⋙ (Sheaf.Γ X.smallEtaleTopology Ab.{u}).rightDerived i

/-- The classical `ℓ`-adic cohomology group with Tate-twisted coefficients
`H^i(X, ℤ_ℓ(q)) = lim_r H^i_et(X, ℤ/ℓ^r(q))` (`q ≥ 0`): the ordinary inverse limit in abelian
groups. -/
noncomputable def classicalEllAdicCohomologyTwistNat (X : Scheme.{u}) (ℓ q i : ℕ) : Ab.{u} :=
  limit (X.twistedTorsionEtaleCohomologySystem ℓ q i)

/-- With the trivial twist this is the classical `ℓ`-adic cohomology group. -/
theorem classicalEllAdicCohomologyTwistNat_zero (X : Scheme.{u}) (ℓ i : ℕ) :
    X.classicalEllAdicCohomologyTwistNat ℓ 0 i = X.classicalEllAdicCohomology ℓ i :=
  rfl

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

section InternalHom

variable {X : Scheme.{u}} (F G : Sheaf X.smallEtaleTopology Ab.{u})

/-- The abelian group `Hom(F|_U, G|_U)` of morphisms between the restrictions of two abelian
sheaves to the site of étale `X`-schemes over `U`. -/
abbrev EtaleHomOver (U : X.Etale) : Type (u + 1) :=
  (CategoryTheory.Over.forget U).op ⋙ F.obj ⟶ (CategoryTheory.Over.forget U).op ⋙ G.obj

/-- A morphism `F|_U ⟶ G|_U` is determined by its components at the affine étale `X`-schemes
over `U`, which form an essentially small family; hence `Hom(F|_U, G|_U)` is `u`-small. -/
instance small_etaleHomOver (U : X.Etale) : Small.{u} (EtaleHomOver F G U) := by
  let e := equivSmallModel.{u} X.AffineEtale
  let A : SmallModel X.AffineEtale → X.Etale := fun w ↦ (AffineEtale.Spec X).obj (e.inverse.obj w)
  let Φ : EtaleHomOver F G U → ((w : SmallModel X.AffineEtale) → (g : A w ⟶ U) →
      (F.obj.obj (op (A w)) →+ G.obj.obj (op (A w)))) :=
    fun τ w g ↦ (τ.app (op (CategoryTheory.Over.mk g))).hom
  refine small_of_injective (f := Φ) ?_
  intro τ τ' h
  ext Y : 2
  obtain ⟨Y⟩ := Y
  let I := Σ w : SmallModel X.AffineEtale, (A w ⟶ Y.left)
  have hf : Sieve.ofArrows (fun i : I ↦ A i.1) (fun i ↦ i.2) ∈ X.smallEtaleTopology Y.left := by
    refine X.smallEtaleTopology.superset_covering ?_
      ((AffineEtale.Spec X).is_cover_of_isCoverDense X.smallEtaleTopology Y.left)
    rintro Z f ⟨⟨a, lift, map, fac⟩⟩
    refine ⟨A (e.functor.obj a), lift ≫ (AffineEtale.Spec X).map (e.unitIso.hom.app a),
      (AffineEtale.Spec X).map (e.unitIso.inv.app a) ≫ map,
      Presieve.ofArrows.mk (ι := I) ⟨e.functor.obj a, _⟩, ?_⟩
    rw [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
    simp [fac]
  refine G.property.hom_ext_ofArrows (fun i : I ↦ i.2) hf ?_
  rintro ⟨w, g⟩
  have hn := τ.naturality (CategoryTheory.Over.homMk g : CategoryTheory.Over.mk (g ≫ Y.hom) ⟶ Y).op
  have hn' := τ'.naturality
    (CategoryTheory.Over.homMk g : CategoryTheory.Over.mk (g ≫ Y.hom) ⟶ Y).op
  have hw : τ.app (op (CategoryTheory.Over.mk (g ≫ Y.hom))) =
      τ'.app (op (CategoryTheory.Over.mk (g ≫ Y.hom))) :=
    AddCommGrpCat.hom_ext (congrFun (congrFun h w) (g ≫ Y.hom))
  rw [hw] at hn
  exact hn.symm.trans hn'

/-- Restriction `Hom(F|_U, G|_U) → Hom(F|_V, G|_V)` along a morphism `V ⟶ U` of étale
`X`-schemes, as an additive map. -/
noncomputable def etaleHomOverRestrict {U V : X.Etale} (f : V ⟶ U) :
    EtaleHomOver F G U →+ EtaleHomOver F G V where
  toFun τ := Functor.whiskerLeft (CategoryTheory.Over.map f).op τ
  map_zero' := by ext; rfl
  map_add' τ τ' := by ext; rfl

/-- Restriction along the identity is the identity. -/
theorem etaleHomOverRestrict_id (U : X.Etale) (τ : EtaleHomOver F G U) :
    etaleHomOverRestrict F G (𝟙 U) τ = τ :=
  ConcreteCategory.congr_hom ((presheafHom F.obj G.obj).map_id (op U)) τ

/-- Restriction is compatible with composition. -/
theorem etaleHomOverRestrict_comp {U V W : X.Etale} (f : V ⟶ U) (g : W ⟶ V)
    (τ : EtaleHomOver F G U) :
    etaleHomOverRestrict F G (g ≫ f) τ =
      etaleHomOverRestrict F G g (etaleHomOverRestrict F G f τ) :=
  ConcreteCategory.congr_hom ((presheafHom F.obj G.obj).map_comp f.op g.op) τ

/-- The presheaf `U ↦ Hom(F|_U, G|_U)` of abelian groups on the small étale site of `X`, shrunk
to the universe `u`. -/
@[simps]
noncomputable def etaleHomPresheaf : X.Etaleᵒᵖ ⥤ Ab.{u} where
  obj U := AddCommGrpCat.of (Shrink.{u} (EtaleHomOver F G U.unop))
  map f := AddCommGrpCat.ofHom
    ((Shrink.addEquiv.{u}).symm.toAddMonoidHom.comp
      ((etaleHomOverRestrict F G f.unop).comp Shrink.addEquiv.toAddMonoidHom))
  map_id U := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro φ
    change (Shrink.addEquiv.{u}).symm
      (etaleHomOverRestrict F G (𝟙 U.unop) (Shrink.addEquiv φ)) = φ
    rw [etaleHomOverRestrict_id, AddEquiv.symm_apply_apply]
  map_comp f g := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro φ
    change (Shrink.addEquiv.{u}).symm
      (etaleHomOverRestrict F G (g.unop ≫ f.unop) (Shrink.addEquiv φ)) =
      (Shrink.addEquiv.{u}).symm (etaleHomOverRestrict F G g.unop
        (Shrink.addEquiv ((Shrink.addEquiv.{u}).symm
          (etaleHomOverRestrict F G f.unop (Shrink.addEquiv φ)))))
    rw [AddEquiv.apply_symm_apply, etaleHomOverRestrict_comp]

/-- The presheaf `U ↦ Hom(F|_U, G|_U)` is a sheaf. -/
theorem isSheaf_etaleHomPresheaf :
    Presheaf.IsSheaf X.smallEtaleTopology (etaleHomPresheaf F G) := by
  apply Presheaf.isSheaf_of_isSheaf_comp _ _ (CategoryTheory.forget Ab.{u})
  rw [isSheaf_iff_isSheaf_of_type]
  have h := (Presheaf.IsSheaf.hom F.obj G.obj G.property)
  rw [isSheaf_iff_isSheaf_of_type] at h
  refine Presieve.isSheaf_of_nat_equiv (fun U ↦ by exact equivShrink (EtaleHomOver F G U))
    (fun U V f x ↦ ?_) h
  change equivShrink _ (etaleHomOverRestrict F G f x) = (Shrink.addEquiv.{u}).symm
    (etaleHomOverRestrict F G f (Shrink.addEquiv.{u} (equivShrink _ x)))
  have hx : Shrink.addEquiv.{u} (equivShrink (EtaleHomOver F G V) x) = x :=
    (equivShrink (EtaleHomOver F G V)).symm_apply_apply x
  rw [hx]
  rfl

/-- The internal Hom sheaf `Hom(F, G)` of two abelian sheaves on the small étale site of `X`. -/
noncomputable def etaleSheafHom : Sheaf X.smallEtaleTopology Ab.{u} :=
  ⟨etaleHomPresheaf F G, isSheaf_etaleHomPresheaf F G⟩

end InternalHom

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

open Hartshorne

/-- The étale Tate twist `ℤ/ℓ^r(-1)`: the dual `Hom(μ_{ℓ^r}, ℤ/ℓ^r)` of `ℤ/ℓ^r(1) = μ_{ℓ^r}`. -/
noncomputable def etaleTateTwistNegOne (X : Scheme.{u}) (ℓ r : ℕ) :
    Sheaf X.smallEtaleTopology Ab.{u} :=
  etaleSheafHom (X.etaleTateTwistOne ℓ r) (X.constantTorsionEtaleSheaf ℓ r)

/-- The étale Tate twist `ℤ/ℓ^r(q)` for every integer `q`: the constant sheaf `ℤ/ℓ^r` for
`q = 0`, the tensor power `μ_{ℓ^r}^{⊗q}` for `q > 0`, and the tensor power
`ℤ/ℓ^r(-1)^{⊗(-q)}` of the dual `ℤ/ℓ^r(-1) = Hom(μ_{ℓ^r}, ℤ/ℓ^r)` for `q < 0`. -/
noncomputable def etaleTateTwist (X : Scheme.{u}) (ℓ r : ℕ) : ℤ → Sheaf X.smallEtaleTopology Ab.{u}
  | .ofNat q => X.etaleTateTwistNat ℓ r q
  | .negSucc k => sheafTensorPowSucc X.smallEtaleTopology (X.etaleTateTwistNegOne ℓ r) k

/-- For `q ≥ 0`, `ℤ/ℓ^r(q)` is the nonnegative twist. -/
theorem etaleTateTwist_natCast (X : Scheme.{u}) (ℓ r q : ℕ) :
    X.etaleTateTwist ℓ r q = X.etaleTateTwistNat ℓ r q :=
  rfl

/-- The twist `ℤ/ℓ^r(-1)` is the dual of `μ_{ℓ^r}`. -/
theorem etaleTateTwist_neg_one (X : Scheme.{u}) (ℓ r : ℕ) :
    X.etaleTateTwist ℓ r (-1) = X.etaleTateTwistNegOne ℓ r :=
  rfl

end AlgebraicGeometry.Scheme

namespace Hartshorne

/-- Multiplication by `ℓ ^ (s - r)`, as a homomorphism `ℤ/ℓ^r → ℤ/ℓ^s` for `r ≤ s`. -/
noncomputable def zmodPowMulHom (ℓ : ℕ) {r s : ℕ} (h : r ≤ s) : ZMod (ℓ ^ r) →+ ZMod (ℓ ^ s) :=
  ZMod.lift (ℓ ^ r) ⟨zmultiplesHom (ZMod (ℓ ^ s)) ((ℓ ^ (s - r) : ℕ) : ZMod (ℓ ^ s)), by
    rw [zmultiplesHom_apply, natCast_zsmul, nsmul_eq_mul, ← Nat.cast_mul, ← pow_add,
      Nat.add_sub_cancel' h, ZMod.natCast_self]⟩

/-- Multiplication by `ℓ ^ (s - r)` on natural-number classes. -/
theorem zmodPowMulHom_natCast (ℓ : ℕ) {r s : ℕ} (h : r ≤ s) (k : ℕ) :
    zmodPowMulHom ℓ h (k : ZMod (ℓ ^ r)) = ((k * ℓ ^ (s - r) : ℕ) : ZMod (ℓ ^ s)) := by
  have := ZMod.lift_coe (ℓ ^ r) ⟨zmultiplesHom (ZMod (ℓ ^ s)) ((ℓ ^ (s - r) : ℕ) : ZMod (ℓ ^ s)),
    by rw [zmultiplesHom_apply, natCast_zsmul, nsmul_eq_mul, ← Nat.cast_mul, ← pow_add,
      Nat.add_sub_cancel' h, ZMod.natCast_self]⟩ (k : ℤ)
  simp only [Int.cast_natCast] at this
  rw [zmodPowMulHom, this]
  simp [Nat.cast_mul]

/-- For `ℓ ≠ 0`, multiplication by `ℓ ^ (s - r)` is injective on `ℤ/ℓ^r`. -/
theorem injective_zmodPowMulHom {ℓ : ℕ} (hℓ : ℓ ≠ 0) {r s : ℕ} (h : r ≤ s) :
    Function.Injective (zmodPowMulHom ℓ h) := by
  have : NeZero (ℓ ^ r) := ⟨pow_ne_zero r hℓ⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  rw [← ZMod.natCast_zmod_val x, zmodPowMulHom_natCast, ZMod.natCast_eq_zero_iff] at hx
  rw [← ZMod.natCast_zmod_val x, ZMod.natCast_eq_zero_iff]
  have hs : ℓ ^ s = ℓ ^ (s - r) * ℓ ^ r := by rw [← pow_add, Nat.sub_add_cancel h]
  rw [hs, mul_comm x.val] at hx
  exact Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero (pow_ne_zero _ hℓ)) hx

/-- For `ℓ ≠ 0`, the `ℓ^r`-torsion of `ℤ/ℓ^s` is the image of `ℤ/ℓ^r`. -/
theorem exists_zmodPowMulHom_eq {ℓ : ℕ} (hℓ : ℓ ≠ 0) {r s : ℕ} (h : r ≤ s) (y : ZMod (ℓ ^ s))
    (hy : (ℓ ^ r) • y = 0) : ∃ x, zmodPowMulHom ℓ h x = y := by
  have : NeZero (ℓ ^ s) := ⟨pow_ne_zero s hℓ⟩
  rw [← ZMod.natCast_zmod_val y, nsmul_eq_mul, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at hy
  have hs : ℓ ^ s = ℓ ^ r * ℓ ^ (s - r) := by rw [← pow_add, Nat.add_sub_cancel' h]
  replace hy : ℓ ^ r * ℓ ^ (s - r) ∣ ℓ ^ r * y.val := hs ▸ hy
  obtain ⟨k, hk⟩ := Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero (pow_ne_zero _ hℓ)) hy
  refine ⟨(k : ZMod (ℓ ^ r)), ?_⟩
  rw [zmodPowMulHom_natCast, ← ZMod.natCast_zmod_val y, hk, mul_comm]

/-- The image of `ℤ/ℓ^r` in `ℤ/ℓ^s` is killed by `ℓ ^ r`. -/
theorem nsmul_zmodPowMulHom (ℓ : ℕ) {r s : ℕ} (h : r ≤ s) (x : ZMod (ℓ ^ r)) :
    (ℓ ^ r) • zmodPowMulHom ℓ h x = 0 := by
  rw [← map_nsmul, nsmul_eq_mul, Nat.cast_pow, ← Nat.cast_pow, ZMod.natCast_self, zero_mul,
    map_zero]

/-- Multiplication by `ℓ ^ (s - r)` on integer classes. -/
theorem zmodPowMulHom_intCast (ℓ : ℕ) {r s : ℕ} (h : r ≤ s) (k : ℤ) :
    zmodPowMulHom ℓ h (k : ZMod (ℓ ^ r)) =
      (k : ZMod (ℓ ^ s)) * ((ℓ ^ (s - r) : ℕ) : ZMod (ℓ ^ s)) := by
  rw [zmodPowMulHom, ZMod.lift_coe]
  simp [zsmul_eq_mul]

/-- For `r = s` the map is the identity. -/
theorem zmodPowMulHom_refl (ℓ r : ℕ) : zmodPowMulHom ℓ (le_refl r) = AddMonoidHom.id _ := by
  ext x
  rw [← ZMod.intCast_zmod_cast x, zmodPowMulHom_intCast]
  simp

/-- The maps compose: `ℓ^(t-s) ℓ^(s-r) = ℓ^(t-r)`. -/
theorem zmodPowMulHom_trans (ℓ : ℕ) {r s t : ℕ} (hrs : r ≤ s) (hst : s ≤ t) :
    zmodPowMulHom ℓ (hrs.trans hst) = (zmodPowMulHom ℓ hst).comp (zmodPowMulHom ℓ hrs) := by
  ext x
  rw [← ZMod.intCast_zmod_cast x, AddMonoidHom.comp_apply, zmodPowMulHom_intCast,
    zmodPowMulHom_intCast]
  rw [show ((x.cast : ℤ) : ZMod (ℓ ^ s)) * ((ℓ ^ (s - r) : ℕ) : ZMod (ℓ ^ s)) =
      (((x.cast : ℤ) * (ℓ ^ (s - r) : ℕ) : ℤ) : ZMod (ℓ ^ s)) by push_cast; rfl,
    zmodPowMulHom_intCast]
  have : t - r = (s - r) + (t - s) := by omega
  push_cast
  rw [this, pow_add, mul_assoc]

/-- The short complex `ℤ/ℓ^r → ℤ/ℓ^s → ℤ/ℓ^s` of abelian groups, where the first map is
multiplication by `ℓ ^ (s - r)` and the second is multiplication by `ℓ ^ r`. -/
noncomputable def zmodPowShortComplex (ℓ : ℕ) {r s : ℕ} (h : r ≤ s) : ShortComplex Ab.{u} :=
  ShortComplex.mk ((AddCommGrpCat.uliftFunctor.{u}).map (AddCommGrpCat.ofHom (zmodPowMulHom ℓ h)))
    ((ℓ ^ r) • 𝟙 _) (by
      ext x
      exact ULift.ext _ _ (nsmul_zmodPowMulHom ℓ h x.down))

/-- The first map of `zmodPowShortComplex` is injective. -/
theorem mono_zmodPowShortComplex_f {ℓ : ℕ} (hℓ : ℓ ≠ 0) {r s : ℕ} (h : r ≤ s) :
    Mono (zmodPowShortComplex.{u} ℓ h).f := by
  rw [AddCommGrpCat.mono_iff_injective]
  intro x y hxy
  exact ULift.ext _ _ (injective_zmodPowMulHom hℓ h (congrArg ULift.down hxy))

/-- The short complex `ℤ/ℓ^r → ℤ/ℓ^s → ℤ/ℓ^s` is exact. -/
theorem exact_zmodPowShortComplex {ℓ : ℕ} (hℓ : ℓ ≠ 0) {r s : ℕ} (h : r ≤ s) :
    (zmodPowShortComplex.{u} ℓ h).Exact := by
  rw [ShortComplex.ab_exact_iff]
  intro y hy
  obtain ⟨x, hx⟩ := exists_zmodPowMulHom_eq hℓ h y.down (congrArg ULift.down hy)
  exact ⟨ULift.up x, ULift.ext _ _ hx⟩

/-- The inclusion `μ_m ⟶ μ_n` of functors on commutative rings, for `m ∣ n`. -/
@[simps]
noncomputable def rootsOfUnityFunctorIncl {m n : ℕ} (h : m ∣ n) :
    rootsOfUnityFunctor.{u} m ⟶ rootsOfUnityFunctor n where
  app A := AddCommGrpCat.ofHom (Subgroup.inclusion (rootsOfUnity_le_of_dvd h)).toAdditive
  naturality A B f := by
    ext ζ
    rfl

end Hartshorne

namespace AlgebraicGeometry.Scheme

open Hartshorne

/-- The morphism `μ_m ⟶ μ_n` of sheaves on the small étale site of `X` induced by a natural
transformation of the functors `A ↦ μ_m(A)` and `A ↦ μ_n(A)`. -/
noncomputable def etaleRootsOfUnitySheafMap (X : Scheme.{u}) {m n : ℕ}
    (α : rootsOfUnityFunctor.{u} m ⟶ rootsOfUnityFunctor n) :
    X.etaleRootsOfUnitySheaf m ⟶ X.etaleRootsOfUnitySheaf n :=
  ((Etale.forget X ⋙ CategoryTheory.Over.forget X).sheafPushforwardContinuous Ab.{u}
    X.smallEtaleTopology etaleTopology).map
      (ObjectProperty.homMk (Functor.whiskerLeft Scheme.Γ α))

/-- The inclusion `μ_m ⟶ μ_n` of sheaves on the small étale site of `X`, for `m ∣ n`. -/
noncomputable def etaleRootsOfUnitySheafIncl (X : Scheme.{u}) {m n : ℕ} (h : m ∣ n) :
    X.etaleRootsOfUnitySheaf m ⟶ X.etaleRootsOfUnitySheaf n :=
  X.etaleRootsOfUnitySheafMap (rootsOfUnityFunctorIncl h)

/-- The inclusion `μ_m ⟶ μ_n` is the identity on sections: a root of unity `ζ` over `U` is sent
to `ζ`. -/
theorem etaleRootsOfUnitySheafIncl_app (X : Scheme.{u}) {m n : ℕ} (h : m ∣ n) (U : X.Etale)
    (ζ : (X.etaleRootsOfUnitySheaf m).obj.obj (op U)) :
    ((Additive.toMul ((X.etaleRootsOfUnitySheafIncl h).hom.app (op U) ζ) :
        rootsOfUnity n Γ(U.left, ⊤)) : Γ(U.left, ⊤)ˣ) =
      ((Additive.toMul ζ : rootsOfUnity m Γ(U.left, ⊤)) : Γ(U.left, ⊤)ˣ) :=
  rfl

/-- The power map `μ_n ⟶ μ_m`, `ζ ↦ ζ ^ (n / m)`, of sheaves on the small étale site of `X`, for
`m ∣ n`. -/
noncomputable def etaleRootsOfUnitySheafPow (X : Scheme.{u}) {m n : ℕ} (h : m ∣ n) :
    X.etaleRootsOfUnitySheaf n ⟶ X.etaleRootsOfUnitySheaf m :=
  X.etaleRootsOfUnitySheafMap (rootsOfUnityFunctorPow (Nat.div_mul_cancel h))

/-- The power map `μ_n ⟶ μ_m` sends a root of unity `ζ` over `U` to `ζ ^ (n / m)`. -/
theorem etaleRootsOfUnitySheafPow_app (X : Scheme.{u}) {m n : ℕ} (h : m ∣ n) (U : X.Etale)
    (ζ : (X.etaleRootsOfUnitySheaf n).obj.obj (op U)) :
    ((Additive.toMul ((X.etaleRootsOfUnitySheafPow h).hom.app (op U) ζ) :
        rootsOfUnity m Γ(U.left, ⊤)) : Γ(U.left, ⊤)ˣ) =
      ((Additive.toMul ζ : rootsOfUnity n Γ(U.left, ⊤)) : Γ(U.left, ⊤)ˣ) ^ (n / m) :=
  rfl

/-- The inclusion `μ_{ℓ^r} ⟶ μ_{ℓ^s}` for `r ≤ s`. -/
noncomputable def etaleTateTwistOneIncl (X : Scheme.{u}) (ℓ : ℕ) {r s : ℕ} (h : r ≤ s) :
    X.etaleTateTwistOne ℓ r ⟶ X.etaleTateTwistOne ℓ s :=
  X.etaleRootsOfUnitySheafMap (rootsOfUnityFunctorIncl (pow_dvd_pow ℓ h))

/-- Sections of `μ_{ℓ^r}` are killed by `ℓ ^ r`. -/
theorem etaleTateTwistOneIncl_app_comp_nsmul (X : Scheme.{u}) (ℓ : ℕ) {r s : ℕ} (h : r ≤ s)
    (V : X.Etale) :
    (X.etaleTateTwistOneIncl ℓ h).hom.app (op V) ≫ ((ℓ ^ r) • 𝟙 _) = 0 := by
  ext ζ
  refine Subtype.ext ?_
  exact (mem_rootsOfUnity _ _).1 (Additive.toMul ζ).2

/-- Multiplication by `ℓ ^ (s - r)`, as a morphism `ℤ/ℓ^r ⟶ ℤ/ℓ^s` of constant sheaves. -/
noncomputable def constantTorsionEtaleSheafMul (X : Scheme.{u}) (ℓ : ℕ) {r s : ℕ} (h : r ≤ s) :
    X.constantTorsionEtaleSheaf ℓ r ⟶ X.constantTorsionEtaleSheaf ℓ s :=
  (constantSheaf X.smallEtaleTopology Ab.{u}).map (zmodPowShortComplex.{u} ℓ h).f

/-- Sections over `V` of the constant sheaf with a given value. -/
noncomputable abbrev constantSheafEval (X : Scheme.{u}) (V : X.Etale) : Ab.{u} ⥤ Ab.{u} :=
  Functor.const _ ⋙ presheafToSheaf X.smallEtaleTopology Ab.{u} ⋙ sheafToPresheaf _ _ ⋙
    (CategoryTheory.evaluation _ _).obj (op V)

/-- Sections of constant sheaves form an additive functor. -/
instance (X : Scheme.{u}) (V : X.Etale) : (constantSheafEval X V).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- A homomorphism into the sections over `V` of `ℤ/ℓ^s` that is killed by `ℓ ^ r` factors
through multiplication by `ℓ ^ (s - r)` from `ℤ/ℓ^r`. -/
theorem exists_lift_constantTorsionEtaleSheafMul (X : Scheme.{u}) {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    {r s : ℕ} (h : r ≤ s) (V : X.Etale) {P : Ab.{u}}
    (k : P ⟶ (X.constantTorsionEtaleSheaf ℓ s).obj.obj (op V)) (hk : k ≫ ((ℓ ^ r) • 𝟙 _) = 0) :
    ∃ l, l ≫ (X.constantTorsionEtaleSheafMul ℓ h).hom.app (op V) = k := by
  have := mono_zmodPowShortComplex_f.{u} hℓ h
  let hS := (exact_zmodPowShortComplex.{u} hℓ h).fIsKernel
  let hT := KernelFork.mapIsLimit _ hS (constantSheafEval X V)
  let k' : P ⟶ (constantSheafEval X V).obj (zmodPowShortComplex.{u} ℓ h).X₂ := k
  have hk' : k' ≫ (constantSheafEval X V).map (zmodPowShortComplex.{u} ℓ h).g = 0 := by
    change k' ≫ (constantSheafEval X V).map ((ℓ ^ r) • 𝟙 (zmodPowShortComplex.{u} ℓ h).X₂) = 0
    have e : (constantSheafEval X V).map (𝟙 (zmodPowShortComplex.{u} ℓ h).X₂) = 𝟙 _ :=
      CategoryTheory.Functor.map_id _ _
    rw [CategoryTheory.Functor.map_nsmul, e]
    exact hk
  exact ⟨(KernelFork.IsLimit.lift' hT k' hk').1, (KernelFork.IsLimit.lift' hT k' hk').2⟩

/-- Multiplication by `ℓ ^ (s - r)` from `ℤ/ℓ^r` to `ℤ/ℓ^s` is injective on sections. -/
instance mono_constantTorsionEtaleSheafMul_app (X : Scheme.{u}) {ℓ : ℕ} [NeZero ℓ]
    {r s : ℕ} (h : r ≤ s) (V : X.Etale) :
    Mono ((X.constantTorsionEtaleSheafMul ℓ h).hom.app (op V)) := by
  have := mono_zmodPowShortComplex_f.{u} (NeZero.ne ℓ) h
  let hS := (exact_zmodPowShortComplex.{u} (NeZero.ne ℓ) h).fIsKernel
  let hT := KernelFork.mapIsLimit _ hS (constantSheafEval X V)
  exact (Fork.IsLimit.mono hT :)

end AlgebraicGeometry.Scheme

namespace Hartshorne

section LiftThroughMono

variable {D : Type*} [Category D] {A : Type*} [Category A] {P Q Q' : D ⥤ A} (j : Q' ⟶ Q)
  [hj : ∀ Y, Mono (j.app Y)] (α : P ⟶ Q) (hα : ∀ Y, ∃ l : P.obj Y ⟶ Q'.obj Y, l ≫ j.app Y = α.app Y)

/-- A natural transformation `α : P ⟶ Q` whose components factor through the components of a
componentwise monomorphism `j : Q' ⟶ Q` factors through `j`. -/
noncomputable def natTransLiftOfMono : P ⟶ Q' where
  app Y := (hα Y).choose
  naturality Y Y' φ := by
    rw [← cancel_mono (j.app Y'), Category.assoc, (hα Y').choose_spec, Category.assoc,
      j.naturality, ← Category.assoc, (hα Y).choose_spec, α.naturality]

/-- The lift composed with `j` is `α`. -/
@[reassoc (attr := simp)]
theorem natTransLiftOfMono_comp : natTransLiftOfMono j α hα ≫ j = α := by
  ext Y
  exact (hα Y).choose_spec

/-- The lift is unique. -/
theorem eq_natTransLiftOfMono (β : P ⟶ Q') (hβ : β ≫ j = α) : β = natTransLiftOfMono j α hα := by
  ext Y
  rw [← cancel_mono (j.app Y)]
  exact (congrArg (fun γ ↦ γ.app Y) hβ).trans (hα Y).choose_spec.symm

end LiftThroughMono

end Hartshorne

namespace AlgebraicGeometry.Scheme

open Hartshorne

section NegativeTwist

variable (X : Scheme.{u}) (ℓ : ℕ) [NeZero ℓ] {r s : ℕ} (h : r ≤ s)

/-- Multiplication by `ℓ ^ (s - r)`, restricted to the étale `X`-schemes over `U`. -/
noncomputable abbrev constantTorsionEtaleSheafMulOver (U : X.Etale) :=
  Functor.whiskerLeft (CategoryTheory.Over.forget U).op (X.constantTorsionEtaleSheafMul ℓ h).hom

/-- Multiplication by `ℓ ^ (s - r)` is injective on sections over every `V` over `U`. -/
instance (U : X.Etale) (Y : (CategoryTheory.Over U)ᵒᵖ) :
    Mono ((X.constantTorsionEtaleSheafMulOver ℓ h U).app Y) :=
  mono_constantTorsionEtaleSheafMul_app X h Y.unop.left

/-- The restriction of `τ : μ_{ℓ^s}|_U ⟶ ℤ/ℓ^s|_U` along the inclusion `μ_{ℓ^r} ⟶ μ_{ℓ^s}`. -/
noncomputable abbrev negTwistRestrictIncl (U : X.Etale)
    (τ : EtaleHomOver (X.etaleTateTwistOne ℓ s) (X.constantTorsionEtaleSheaf ℓ s) U) :=
  Functor.whiskerLeft (CategoryTheory.Over.forget U).op (X.etaleTateTwistOneIncl ℓ h).hom ≫ τ

omit [NeZero ℓ] in
/-- If `ℓ ^ r` kills `a`, it kills `a ≫ t`. -/
theorem comp_comp_nsmul_id_eq_zero {C : Type*} [Category C] [Preadditive C] {A B D : C}
    (a : A ⟶ B) (t : B ⟶ D) (n : ℕ) (ha : a ≫ (n • 𝟙 B) = 0) :
    (a ≫ t) ≫ (n • 𝟙 D) = 0 := by
  rw [Preadditive.comp_nsmul, Category.comp_id, ← Preadditive.nsmul_comp]
  rw [Preadditive.comp_nsmul, Category.comp_id] at ha
  rw [ha, zero_comp]

/-- The restriction of `τ` to `μ_{ℓ^r}` takes values in the image of `ℤ/ℓ^r`. -/
theorem exists_lift_negTwistRestrictIncl (U : X.Etale)
    (τ : EtaleHomOver (X.etaleTateTwistOne ℓ s) (X.constantTorsionEtaleSheaf ℓ s) U)
    (Y : (CategoryTheory.Over U)ᵒᵖ) :
    ∃ l, l ≫ (X.constantTorsionEtaleSheafMulOver ℓ h U).app Y =
      (X.negTwistRestrictIncl ℓ h U τ).app Y := by
  refine exists_lift_constantTorsionEtaleSheafMul X (NeZero.ne ℓ) h Y.unop.left _ ?_
  exact comp_comp_nsmul_id_eq_zero _ (τ.app Y) _
    (X.etaleTateTwistOneIncl_app_comp_nsmul ℓ h Y.unop.left)

/-- The transition `ℤ/ℓ^s(-1) → ℤ/ℓ^r(-1)` on sections over `U`: a morphism
`τ : μ_{ℓ^s}|_U ⟶ ℤ/ℓ^s|_U` goes to the unique `σ : μ_{ℓ^r}|_U ⟶ ℤ/ℓ^r|_U` such that
multiplication by `ℓ ^ (s - r)` after `σ` is the restriction of `τ` to `μ_{ℓ^r}`. -/
noncomputable def negTwistTransitionApp (U : X.Etale) :
    EtaleHomOver (X.etaleTateTwistOne ℓ s) (X.constantTorsionEtaleSheaf ℓ s) U →+
      EtaleHomOver (X.etaleTateTwistOne ℓ r) (X.constantTorsionEtaleSheaf ℓ r) U where
  toFun τ := natTransLiftOfMono (X.constantTorsionEtaleSheafMulOver ℓ h U)
    (X.negTwistRestrictIncl ℓ h U τ) (X.exists_lift_negTwistRestrictIncl ℓ h U τ)
  map_zero' := (eq_natTransLiftOfMono _ _ _ 0 (by simp)).symm
  map_add' τ τ' := (eq_natTransLiftOfMono _ _ _ _ (by simp [Preadditive.add_comp])).symm

/-- Characterizing property of the transition. -/
theorem negTwistTransitionApp_comp (U : X.Etale)
    (τ : EtaleHomOver (X.etaleTateTwistOne ℓ s) (X.constantTorsionEtaleSheaf ℓ s) U) :
    X.negTwistTransitionApp ℓ h U τ ≫ X.constantTorsionEtaleSheafMulOver ℓ h U =
      X.negTwistRestrictIncl ℓ h U τ :=
  natTransLiftOfMono_comp _ _ _

/-- Uniqueness of the transition. -/
theorem eq_negTwistTransitionApp (U : X.Etale)
    (τ : EtaleHomOver (X.etaleTateTwistOne ℓ s) (X.constantTorsionEtaleSheaf ℓ s) U)
    (σ : EtaleHomOver (X.etaleTateTwistOne ℓ r) (X.constantTorsionEtaleSheaf ℓ r) U)
    (hσ : σ ≫ X.constantTorsionEtaleSheafMulOver ℓ h U = X.negTwistRestrictIncl ℓ h U τ) :
    σ = X.negTwistTransitionApp ℓ h U τ :=
  eq_natTransLiftOfMono _ _ _ σ hσ

/-- The transition commutes with restriction. -/
theorem negTwistTransitionApp_restrict {U V : X.Etale} (g : V ⟶ U)
    (τ : EtaleHomOver (X.etaleTateTwistOne ℓ s) (X.constantTorsionEtaleSheaf ℓ s) U) :
    etaleHomOverRestrict _ _ g (X.negTwistTransitionApp ℓ h U τ) =
      X.negTwistTransitionApp ℓ h V (etaleHomOverRestrict _ _ g τ) := by
  apply eq_negTwistTransitionApp
  have := congrArg (Functor.whiskerLeft (CategoryTheory.Over.map g).op)
    (X.negTwistTransitionApp_comp ℓ h U τ)
  rw [Functor.whiskerLeft_comp, Functor.whiskerLeft_comp] at this
  exact this

/-- The transition morphism `ℤ/ℓ^s(-1) ⟶ ℤ/ℓ^r(-1)` for `r ≤ s`. -/
noncomputable def etaleTateTwistNegOneTransition :
    X.etaleTateTwistNegOne ℓ s ⟶ X.etaleTateTwistNegOne ℓ r :=
  ObjectProperty.homMk
    { app U := AddCommGrpCat.ofHom ((Shrink.addEquiv.{u}).symm.toAddMonoidHom.comp
        ((X.negTwistTransitionApp ℓ h U.unop).comp Shrink.addEquiv.toAddMonoidHom))
      naturality U V g := by
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro φ
        change (Shrink.addEquiv.{u}).symm (X.negTwistTransitionApp ℓ h V.unop
            (Shrink.addEquiv ((Shrink.addEquiv.{u}).symm
              (etaleHomOverRestrict _ _ g.unop (Shrink.addEquiv φ))))) =
          (Shrink.addEquiv.{u}).symm (etaleHomOverRestrict _ _ g.unop
            (Shrink.addEquiv ((Shrink.addEquiv.{u}).symm (X.negTwistTransitionApp ℓ h U.unop
              (Shrink.addEquiv φ)))))
        rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
          negTwistTransitionApp_restrict] }

omit [NeZero ℓ] in
/-- The inclusion `μ_{ℓ^r} ⊆ μ_{ℓ^r}` is the identity. -/
theorem etaleTateTwistOneIncl_refl (r : ℕ) :
    X.etaleTateTwistOneIncl ℓ (le_refl r) = 𝟙 _ := by
  ext V ζ
  rfl

omit [NeZero ℓ] in
/-- Inclusions of roots of unity compose. -/
theorem etaleTateTwistOneIncl_trans {r s t : ℕ} (hrs : r ≤ s) (hst : s ≤ t) :
    X.etaleTateTwistOneIncl ℓ (hrs.trans hst) =
      X.etaleTateTwistOneIncl ℓ hrs ≫ X.etaleTateTwistOneIncl ℓ hst := by
  ext V ζ
  rfl

omit [NeZero ℓ] in
/-- Multiplication by `ℓ ^ 0` is the identity. -/
theorem constantTorsionEtaleSheafMul_refl (r : ℕ) :
    X.constantTorsionEtaleSheafMul ℓ (le_refl r) = 𝟙 _ := by
  simp only [constantTorsionEtaleSheafMul, zmodPowShortComplex, zmodPowMulHom_refl]
  rw [AddCommGrpCat.ofHom_id, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  rfl

omit [NeZero ℓ] in
/-- Multiplications by powers of `ℓ` compose. -/
theorem constantTorsionEtaleSheafMul_trans {r s t : ℕ} (hrs : r ≤ s) (hst : s ≤ t) :
    X.constantTorsionEtaleSheafMul ℓ (hrs.trans hst) =
      X.constantTorsionEtaleSheafMul ℓ hrs ≫ X.constantTorsionEtaleSheafMul ℓ hst := by
  unfold constantTorsionEtaleSheafMul zmodPowShortComplex
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    ← AddCommGrpCat.ofHom_comp, ← zmodPowMulHom_trans]

/-- The transition from `ℤ/ℓ^r(-1)` to itself is the identity. -/
theorem negTwistTransitionApp_refl (r : ℕ) (U : X.Etale)
    (τ : EtaleHomOver (X.etaleTateTwistOne ℓ r) (X.constantTorsionEtaleSheaf ℓ r) U) :
    X.negTwistTransitionApp ℓ (le_refl r) U τ = τ := by
  refine (eq_negTwistTransitionApp X ℓ (le_refl r) U τ τ ?_).symm
  simp only [constantTorsionEtaleSheafMulOver, negTwistRestrictIncl,
    constantTorsionEtaleSheafMul_refl, etaleTateTwistOneIncl_refl]
  rfl

/-- Transitions of `ℤ_ℓ(-1)` compose. -/
theorem negTwistTransitionApp_trans {r s t : ℕ} (hrs : r ≤ s) (hst : s ≤ t) (U : X.Etale)
    (τ : EtaleHomOver (X.etaleTateTwistOne ℓ t) (X.constantTorsionEtaleSheaf ℓ t) U) :
    X.negTwistTransitionApp ℓ (hrs.trans hst) U τ =
      X.negTwistTransitionApp ℓ hrs U (X.negTwistTransitionApp ℓ hst U τ) := by
  refine (eq_negTwistTransitionApp X ℓ (hrs.trans hst) U τ _ ?_).symm
  have e1 : X.constantTorsionEtaleSheafMulOver ℓ (hrs.trans hst) U =
      X.constantTorsionEtaleSheafMulOver ℓ hrs U ≫ X.constantTorsionEtaleSheafMulOver ℓ hst U := by
    simp only [constantTorsionEtaleSheafMulOver]
    rw [constantTorsionEtaleSheafMul_trans X ℓ hrs hst]
    rfl
  rw [e1, ← Category.assoc, negTwistTransitionApp_comp, negTwistRestrictIncl, Category.assoc,
    negTwistTransitionApp_comp, negTwistRestrictIncl, negTwistRestrictIncl,
    etaleTateTwistOneIncl_trans X ℓ hrs hst, ← Category.assoc]
  rfl

/-- The transition morphism from `ℤ/ℓ^r(-1)` to itself is the identity. -/
theorem etaleTateTwistNegOneTransition_refl (r : ℕ) :
    X.etaleTateTwistNegOneTransition ℓ (le_refl r) = 𝟙 _ := by
  ext U φ
  change (Shrink.addEquiv.{u}).symm (X.negTwistTransitionApp ℓ (le_refl r) U.unop
    (Shrink.addEquiv φ)) = φ
  rw [negTwistTransitionApp_refl, AddEquiv.symm_apply_apply]

/-- Transition morphisms of `ℤ_ℓ(-1)` compose. -/
theorem etaleTateTwistNegOneTransition_trans {r s t : ℕ} (hrs : r ≤ s) (hst : s ≤ t) :
    X.etaleTateTwistNegOneTransition ℓ (hrs.trans hst) =
      X.etaleTateTwistNegOneTransition ℓ hst ≫ X.etaleTateTwistNegOneTransition ℓ hrs := by
  ext U φ
  change (Shrink.addEquiv.{u}).symm (X.negTwistTransitionApp ℓ (hrs.trans hst) U.unop
    (Shrink.addEquiv φ)) = (Shrink.addEquiv.{u}).symm (X.negTwistTransitionApp ℓ hrs U.unop
      (Shrink.addEquiv ((Shrink.addEquiv.{u}).symm (X.negTwistTransitionApp ℓ hst U.unop
        (Shrink.addEquiv φ)))))
  rw [AddEquiv.apply_symm_apply, negTwistTransitionApp_trans]

/-- The inverse system `r ↦ ℤ/ℓ^r(-1)` of sheaves on the small étale site of `X`; this is the
`ℓ`-adic sheaf `ℤ_ℓ(-1)`. -/
@[simps]
noncomputable def etaleTateTwistNegOneSystem : ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology Ab.{u} where
  obj r := X.etaleTateTwistNegOne ℓ r.unop
  map f := X.etaleTateTwistNegOneTransition ℓ (leOfHom f.unop)
  map_id r := X.etaleTateTwistNegOneTransition_refl ℓ r.unop
  map_comp f g := X.etaleTateTwistNegOneTransition_trans ℓ (leOfHom g.unop) (leOfHom f.unop)

end NegativeTwist

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

open Hartshorne

variable (X : Scheme.{u}) (ℓ : ℕ) [NeZero ℓ]

/-- The inverse system `r ↦ ℤ/ℓ^r(q)` of sheaves on the small étale site of `X`, for every integer
`q`: the `ℓ`-adic sheaf `ℤ_ℓ(q)`.  For `q ≥ 0` it is `etaleTateTwistNatSystem`; for `q < 0` it is
the `(-q)`-th tensor power of the inverse system `ℤ_ℓ(-1)`. -/
noncomputable def etaleTateTwistSystem : ℤ → ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology Ab.{u}
  | .ofNat q => X.etaleTateTwistNatSystem ℓ q
  | .negSucc k => X.etaleTateTwistNegOneSystem ℓ ⋙ sheafTensorPowSuccFunctor X.smallEtaleTopology k

/-- The `r`-th stage of `ℤ_ℓ(q)` is `ℤ/ℓ^r(q)`. -/
theorem etaleTateTwistSystem_obj (q : ℤ) (r : ℕᵒᵖ) :
    (X.etaleTateTwistSystem ℓ q).obj r = X.etaleTateTwist ℓ r.unop q := by
  rcases q with q | k
  · exact X.etaleTateTwistNatSystem_obj ℓ q r
  · rfl

/-- The inverse system `r ↦ H^i_et(X, ℤ/ℓ^r(q))` of torsion étale cohomology groups, for every
integer `q`. -/
noncomputable def ellAdicTwistCohomologySystem (q : ℤ) (i : ℕ) : ℕᵒᵖ ⥤ Ab.{u} :=
  X.etaleTateTwistSystem ℓ q ⋙ (Sheaf.Γ X.smallEtaleTopology Ab.{u}).rightDerived i

/-- The `ℓ`-adic cohomology group `H^i(X, ℤ_ℓ(q)) = lim_r H^i_et(X, ℤ/ℓ^r(q))` with Tate-twisted
coefficients, for every integer `q`: the ordinary inverse limit in abelian groups. -/
noncomputable def classicalEllAdicCohomologyTwist (q : ℤ) (i : ℕ) : Ab.{u} :=
  limit (X.ellAdicTwistCohomologySystem ℓ q i)

/-- With nonnegative twist this is the limit of `etaleTateTwistNat`-cohomology. -/
theorem classicalEllAdicCohomologyTwist_natCast (q i : ℕ) :
    X.classicalEllAdicCohomologyTwist ℓ q i = X.classicalEllAdicCohomologyTwistNat ℓ q i :=
  rfl

end AlgebraicGeometry.Scheme

namespace Hartshorne

section Killing

variable {C : Type w} [Category.{v} C]

/-- The pointwise tensor product is additive in the first variable. -/
theorem presheafTensorMap_nsmul_left {F F' G G' : Cᵒᵖ ⥤ Ab.{u}} (n : ℕ) (α : F ⟶ F')
    (β : G ⟶ G') : presheafTensorMap (n • α) β = n • presheafTensorMap α β := by
  ext U x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    change ((n • α.app U) a) ⊗ₜ[ℤ] (β.app U b) = n • ((α.app U a) ⊗ₜ[ℤ] (β.app U b))
    rw [TensorProduct.smul_tmul']
    simp
  | add x y hx hy => simp_all

variable (J : GrothendieckTopology C) [HasSheafify J Ab.{u}]

/-- The tensor product of sheaves is additive in the first variable. -/
theorem sheafTensorMap_nsmul_left {F F' G G' : Sheaf J Ab.{u}} (n : ℕ) (α : F ⟶ F')
    (β : G ⟶ G') : sheafTensorMap J (n • α) β = n • sheafTensorMap J α β := by
  simp only [sheafTensorMap]
  rw [← CategoryTheory.Functor.map_nsmul, ← presheafTensorMap_nsmul_left]
  rfl

/-- If `n` kills `F`, then `n` kills `F ⊗ G`. -/
theorem sheafTensor_nsmul_id_eq_zero {F : Sheaf J Ab.{u}} (G : Sheaf J Ab.{u}) {n : ℕ}
    (hF : n • 𝟙 F = 0) : n • 𝟙 (sheafTensor J F G) = 0 := by
  rw [← sheafTensorMap_id, ← sheafTensorMap_nsmul_left, hF, ← zero_smul ℕ (0 : F ⟶ F),
    sheafTensorMap_nsmul_left, zero_smul]

/-- If `n` kills `F`, then `n` kills every tensor power `F^{⊗(k+1)}`. -/
theorem sheafTensorPowSucc_nsmul_id_eq_zero {F : Sheaf J Ab.{u}} {n : ℕ}
    (hF : n • 𝟙 F = 0) (k : ℕ) : n • 𝟙 (sheafTensorPowSucc J F k) = 0 := by
  induction k with
  | zero => exact hF
  | succ k ih => exact sheafTensor_nsmul_id_eq_zero J F ih

omit [HasSheafify J Ab.{u}] in
/-- If `n` kills the target, `n` kills every morphism. -/
theorem nsmul_eq_zero_of_nsmul_id {D : Type*} [Category D] [Preadditive D] {A B : D}
    (t : A ⟶ B) {n : ℕ} (h : n • 𝟙 B = 0) : n • t = 0 := by
  rw [← Category.comp_id t, ← Preadditive.comp_nsmul, h, Limits.comp_zero]

omit [HasSheafify J Ab.{u}] in
/-- Multiples of morphisms of sheaves of abelian groups are computed sectionwise. -/
theorem sheaf_nsmul_hom_app {F G : Sheaf J Ab.{u}} (n : ℕ) (f : F ⟶ G) (U : Cᵒᵖ) :
    (n • f).hom.app U = n • f.hom.app U :=
  rfl

end Killing

end Hartshorne

namespace AlgebraicGeometry.Scheme

/-- `ℓ ^ r` kills `μ_{ℓ^r}`. -/
theorem etaleTateTwistOne_pow_nsmul_id (X : Scheme.{u}) (ℓ r : ℕ) :
    (ℓ ^ r) • 𝟙 (X.etaleTateTwistOne ℓ r) = 0 := by
  ext V ζ
  rw [Hartshorne.sheaf_nsmul_hom_app, AddCommGrpCat.hom_nsmul, AddMonoidHom.nsmul_apply]
  refine Subtype.ext ?_
  exact (mem_rootsOfUnity _ _).1 (Additive.toMul ζ).2

/-- If `n` kills `G`, then `n` kills the internal Hom sheaf `Hom(F, G)`. -/
theorem etaleSheafHom_nsmul_id_eq_zero {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology Ab.{u})
    {G : Sheaf X.smallEtaleTopology Ab.{u}} {n : ℕ} (hG : n • 𝟙 G = 0) :
    n • 𝟙 (etaleSheafHom F G) = 0 := by
  ext U φ
  rw [Hartshorne.sheaf_nsmul_hom_app, AddCommGrpCat.hom_nsmul, AddMonoidHom.nsmul_apply]
  change n • φ = 0
  apply (Shrink.addEquiv.{u} (α := EtaleHomOver F G U.unop)).injective
  rw [map_nsmul, map_zero]
  refine NatTrans.ext (funext fun Y ↦ ?_)
  rw [NatTrans.app_nsmul, NatTrans.app_zero]
  have hG' : n • 𝟙 (G.obj.obj (op Y.unop.left)) = 0 := by
    have := congrArg (fun f ↦ f.hom.app (op Y.unop.left)) hG
    simpa [Hartshorne.sheaf_nsmul_hom_app] using this
  exact Hartshorne.nsmul_eq_zero_of_nsmul_id _ hG'

/-- `ℓ ^ r` kills `ℤ/ℓ^r(q)` for every integer `q`. -/
theorem etaleTateTwist_pow_nsmul_id (X : Scheme.{u}) (ℓ r : ℕ) (q : ℤ) :
    (ℓ ^ r) • 𝟙 (X.etaleTateTwist ℓ r q) = 0 := by
  rcases q with q | k
  · cases q with
    | zero => exact X.constantTorsionEtaleSheaf_pow_nsmul_id ℓ r
    | succ q =>
      exact Hartshorne.sheafTensorPowSucc_nsmul_id_eq_zero X.smallEtaleTopology
        (X.etaleTateTwistOne_pow_nsmul_id ℓ r) q
  · exact Hartshorne.sheafTensorPowSucc_nsmul_id_eq_zero X.smallEtaleTopology
      (etaleSheafHom_nsmul_id_eq_zero _ (X.constantTorsionEtaleSheaf_pow_nsmul_id ℓ r)) k

/-- `ℓ ^ r` kills `H^i_et(X, ℤ/ℓ^r(q))`. -/
theorem ellAdicTwistCohomologySystem_pow_nsmul_id (X : Scheme.{u}) (ℓ : ℕ) [NeZero ℓ] (q : ℤ)
    (i r : ℕ) : (ℓ ^ r) • 𝟙 ((X.ellAdicTwistCohomologySystem ℓ q i).obj (op r)) = 0 := by
  have hsys : (ℓ ^ r) • 𝟙 ((X.etaleTateTwistSystem ℓ q).obj (op r)) = 0 := by
    rw [etaleTateTwistSystem_obj]
    exact X.etaleTateTwist_pow_nsmul_id ℓ r q
  change (ℓ ^ r) • 𝟙 (((Sheaf.Γ X.smallEtaleTopology Ab.{u}).rightDerived i).obj
    ((X.etaleTateTwistSystem ℓ q).obj (op r))) = 0
  rw [← CategoryTheory.Functor.map_id, ← CategoryTheory.Functor.map_nsmul, hsys,
    CategoryTheory.Functor.map_zero]

end AlgebraicGeometry.Scheme

namespace Hartshorne

section EllAdicLimitModule

/-- An inverse system `F` of abelian groups indexed by `ℕ` is an `ℓ`-power torsion system if
`ℓ ^ r` kills its `r`-th stage. -/
def IsEllPowerTorsionSystem (ℓ : ℕ) (F : ℕᵒᵖ ⥤ Ab.{u}) : Prop :=
  ∀ r : ℕ, (ℓ ^ r) • 𝟙 (F.obj (op r)) = 0

variable {ℓ : ℕ} {F : ℕᵒᵖ ⥤ Ab.{u}} (hF : IsEllPowerTorsionSystem ℓ F)
include hF

/-- On the `r`-th stage of an `ℓ`-power torsion system, multiplication by a natural number
depends only on its class modulo `ℓ ^ r`. -/
theorem IsEllPowerTorsionSystem.nsmul_id_congr {r m n : ℕ} (h : (m : ZMod (ℓ ^ r)) = n) :
    m • 𝟙 (F.obj (op r)) = n • 𝟙 (F.obj (op r)) := by
  have key : ∀ k : ℕ, k • 𝟙 (F.obj (op r)) = (k % ℓ ^ r) • 𝟙 (F.obj (op r)) := fun k ↦ by
    conv_lhs => rw [← Nat.mod_add_div k (ℓ ^ r)]
    rw [add_nsmul, mul_comm (ℓ ^ r), mul_smul, hF r, smul_zero, add_zero]
  rw [key m, key n, (ZMod.natCast_eq_natCast_iff' m n (ℓ ^ r)).mp h]

variable [Fact ℓ.Prime]

omit hF in
/-- The canonical lift of `a mod ℓ^r` reduces back to it. -/
private theorem natCast_val_toZModPow' (r : ℕ) (a : ℤ_[ℓ]) :
    ((PadicInt.toZModPow r a).val : ZMod (ℓ ^ r)) = PadicInt.toZModPow r a :=
  have : NeZero (ℓ ^ r) := ⟨pow_ne_zero r (Fact.out : ℓ.Prime).ne_zero⟩
  ZMod.natCast_zmod_val _

/-- The action of `ℤ_[ℓ]` on the `r`-th stage of an `ℓ`-power torsion system: an `ℓ`-adic
integer acts as multiplication by the canonical natural-number lift of its reduction modulo
`ℓ ^ r`.  For the classical inverse system this is the action of
`Hartshorne.Weil.RationalEllAdicCohomology`. -/
noncomputable def ellAdicStagePadicIntAction (r : ℕ) : ℤ_[ℓ] →+* End (F.obj (op r)) where
  toFun a := (PadicInt.toZModPow r a).val • 𝟙 _
  map_one' := by
    refine (hF.nsmul_id_congr (n := 1) ?_).trans (one_smul ℕ _)
    rw [natCast_val_toZModPow', map_one, Nat.cast_one]
  map_mul' a b := by
    rw [End.mul_def, Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.id_comp,
      ← mul_smul]
    refine hF.nsmul_id_congr ?_
    rw [Nat.cast_mul, natCast_val_toZModPow', natCast_val_toZModPow', natCast_val_toZModPow',
      map_mul, mul_comm]
  map_zero' := by
    change (PadicInt.toZModPow r 0).val • 𝟙 _ = 0
    rw [map_zero, ZMod.val_zero, zero_smul]
  map_add' a b := by
    refine (hF.nsmul_id_congr (n := _ + _) ?_).trans (add_nsmul _ _ _)
    rw [Nat.cast_add, natCast_val_toZModPow', natCast_val_toZModPow', natCast_val_toZModPow',
      map_add]

/-- The action of `a` on the `r`-th stage is multiplication by the lift of `a mod ℓ^r`. -/
theorem ellAdicStagePadicIntAction_apply (r : ℕ) (a : ℤ_[ℓ]) :
    ellAdicStagePadicIntAction hF r a = (PadicInt.toZModPow r a).val • 𝟙 _ :=
  rfl

/-- The action of `ℤ_[ℓ]` commutes with every morphism from a later stage to an earlier one. -/
theorem comp_ellAdicStagePadicIntAction {r s : ℕ} (h : r ≤ s)
    (g : F.obj (op s) ⟶ F.obj (op r)) (a : ℤ_[ℓ]) :
    g ≫ ellAdicStagePadicIntAction hF r a = ellAdicStagePadicIntAction hF s a ≫ g := by
  have hcast : ((PadicInt.toZModPow s a).val : ZMod (ℓ ^ r)) =
      ((PadicInt.toZModPow r a).val : ZMod (ℓ ^ r)) := by
    have : NeZero (ℓ ^ s) := ⟨pow_ne_zero s (Fact.out : ℓ.Prime).ne_zero⟩
    rw [natCast_val_toZModPow', ZMod.natCast_val, ← ZMod.castHom_apply (h := pow_dvd_pow ℓ h)]
    exact RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow r s h) a
  have e := congrArg (g ≫ ·) (hF.nsmul_id_congr hcast)
  simp only [Preadditive.comp_nsmul, Category.comp_id] at e
  rw [ellAdicStagePadicIntAction_apply, ellAdicStagePadicIntAction_apply,
    Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.comp_id, Category.id_comp]
  exact e.symm

/-- The action of `ℤ_[ℓ]` on an `ℓ`-power torsion system. -/
noncomputable def ellAdicSystemPadicIntAction : ℤ_[ℓ] →+* End F where
  toFun a :=
    { app r := ellAdicStagePadicIntAction hF r.unop a
      naturality _ _ f := comp_ellAdicStagePadicIntAction hF (leOfHom f.unop) _ a }
  map_one' := by
    refine NatTrans.ext (funext fun r ↦ ?_)
    exact map_one (ellAdicStagePadicIntAction hF r.unop)
  map_mul' a b := by
    refine NatTrans.ext (funext fun r ↦ ?_)
    exact map_mul (ellAdicStagePadicIntAction hF r.unop) a b
  map_zero' := by
    refine NatTrans.ext (funext fun r ↦ ?_)
    exact map_zero (ellAdicStagePadicIntAction hF r.unop)
  map_add' a b := by
    refine NatTrans.ext (funext fun r ↦ ?_)
    exact map_add (ellAdicStagePadicIntAction hF r.unop) a b

/-- The action of `ℤ_[ℓ]` on the inverse limit of an `ℓ`-power torsion system. -/
noncomputable def ellAdicLimitPadicIntAction : ℤ_[ℓ] →+* End (limit F) where
  toFun a := limMap (ellAdicSystemPadicIntAction hF a)
  map_one' := by
    rw [map_one]
    exact lim.map_id _
  map_mul' a b := by
    rw [map_mul]
    exact lim.map_comp _ _
  map_zero' := by
    change limMap (ellAdicSystemPadicIntAction hF 0) = (0 : limit F ⟶ limit F)
    refine limit.hom_ext fun r ↦ ?_
    rw [limMap_π, map_zero, NatTrans.app_zero, Limits.comp_zero, Limits.zero_comp]
  map_add' a b := by
    change limMap (ellAdicSystemPadicIntAction hF (a + b)) =
      (limMap (ellAdicSystemPadicIntAction hF a) + limMap (ellAdicSystemPadicIntAction hF b) :
        limit F ⟶ limit F)
    refine limit.hom_ext fun r ↦ ?_
    rw [Preadditive.add_comp, limMap_π, limMap_π, limMap_π, map_add, NatTrans.app_add,
      Preadditive.comp_add]

/-- The `ℤ_[ℓ]`-module structure on the inverse limit of an `ℓ`-power torsion system. -/
noncomputable abbrev ellAdicLimitModule : Module ℤ_[ℓ] ((limit F : Ab.{u}) : Type u) where
  smul a x := (ellAdicLimitPadicIntAction hF a).hom x
  one_smul x := by
    change (ellAdicLimitPadicIntAction hF 1).hom x = x
    rw [map_one]
    rfl
  mul_smul a b x := by
    change (ellAdicLimitPadicIntAction hF (a * b)).hom x = _
    rw [map_mul]
    rfl
  smul_zero a := map_zero _
  smul_add a x y := map_add _ x y
  add_smul a b x := by
    change (ellAdicLimitPadicIntAction hF (a + b)).hom x = _
    rw [map_add]
    rfl
  zero_smul x := by
    change (ellAdicLimitPadicIntAction hF 0).hom x = 0
    rw [map_zero]
    rfl

end EllAdicLimitModule

end Hartshorne

namespace AlgebraicGeometry.Scheme

open Hartshorne

variable (X : Scheme.{u}) (ℓ : ℕ)

/-- The inverse system `r ↦ H^i_et(X, ℤ/ℓ^r(q))` is an `ℓ`-power torsion system. -/
theorem isEllPowerTorsionSystem_ellAdicTwistCohomologySystem [NeZero ℓ] (q : ℤ) (i : ℕ) :
    IsEllPowerTorsionSystem ℓ (X.ellAdicTwistCohomologySystem ℓ q i) :=
  fun r ↦ X.ellAdicTwistCohomologySystem_pow_nsmul_id ℓ q i r

variable [Fact ℓ.Prime]

/-- The `ℤ_[ℓ]`-module structure on `H^i(X, ℤ_ℓ(q))`. -/
noncomputable instance classicalEllAdicCohomologyTwistModule (q : ℤ) (i : ℕ) :
    Module ℤ_[ℓ] (X.classicalEllAdicCohomologyTwist ℓ q i) :=
  ellAdicLimitModule (X.isEllPowerTorsionSystem_ellAdicTwistCohomologySystem ℓ q i)

/-- With the trivial twist this is the `ℤ_[ℓ]`-module structure of
`Hartshorne.Weil.RationalEllAdicCohomology`. -/
theorem classicalEllAdicCohomologyTwistModule_zero (i : ℕ) :
    X.classicalEllAdicCohomologyTwistModule ℓ 0 i = X.classicalEllAdicCohomologyModule ℓ i :=
  rfl

/-- Rational `ℓ`-adic cohomology with Tate-twisted coefficients
`H^i(X, ℚ_ℓ(q)) = H^i(X, ℤ_ℓ(q)) ⊗_{ℤ_ℓ} ℚ_ℓ`, for every integer `q`, as a `ℚ_[ℓ]`-module. -/
noncomputable def rationalEllAdicCohomologyTwist (q : ℤ) (i : ℕ) : ModuleCat.{u} ℚ_[ℓ] :=
  ModuleCat.of ℚ_[ℓ] (TensorProduct ℤ_[ℓ] ℚ_[ℓ] (X.classicalEllAdicCohomologyTwist ℓ q i))

/-- With the trivial twist this is the rational `ℓ`-adic cohomology `H^i_et(X, ℚ_ℓ)`. -/
theorem rationalEllAdicCohomologyTwist_zero (i : ℕ) :
    X.rationalEllAdicCohomologyTwist ℓ 0 i = X.rationalEllAdicCohomology ℓ i :=
  rfl

end AlgebraicGeometry.Scheme

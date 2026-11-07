/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Weil.ClassicalEllAdicCohomology
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Roots of unity and nonnegative Tate twists on the small étale site

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

No hypothesis on `ℓ` is needed for these constructions; invertibility of `ℓ` on `X` enters
only in theorems about them.  Negative twists (duals) are not constructed here.

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

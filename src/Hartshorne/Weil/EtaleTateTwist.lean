/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# Roots of unity on the small étale site

Scratch.
-/

open CategoryTheory Limits Opposite

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Hartshorne

/-- The group ring `ℤ[ℤ/n]`, which represents `n`-th roots of unity. -/
abbrev RootsOfUnityRing (n : ℕ) : Type := MonoidAlgebra ℤ (Multiplicative (ZMod n))

/-- The tautological `n`-th root of unity of `ℤ[ℤ/n]`: the image of the generator of `ℤ/n`. -/
noncomputable def universalRootOfUnity (n : ℕ) : rootsOfUnity n (RootsOfUnityRing n) :=
  ⟨(MonoidAlgebra.of ℤ (Multiplicative (ZMod n))).toHomUnits (Multiplicative.ofAdd 1), by
    rw [mem_rootsOfUnity, ← map_pow, ← ofAdd_nsmul, nsmul_one, ZMod.natCast_self, ofAdd_zero,
      map_one]⟩

lemma generator_zpowers (n : ℕ) (x : Multiplicative (ZMod n)) :
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
      (MonoidHom.eq_iff_eq_on_generator (generator_zpowers n) _ _).2
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
    let ψ := monoidHomOfForallMemZpowers (generator_zpowers n) hord
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
noncomputable def rootOfUnityOfHomSpec (n : ℕ) {U : Scheme.{u}} (g : U ⟶ Spec (rootsOfUnityRingCat n)) :
    rootsOfUnity n Γ(U, ⊤) :=
  restrictRootsOfUnity ((Scheme.ΓSpecIso _).inv ≫ g.appTop).hom n (universalRootOfUnityULift n)

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
    yoneda.obj (Spec (rootsOfUnityRingCat.{u} n)) ≅ rootsOfUnityPresheaf n ⋙ CategoryTheory.forget Ab.{u} :=
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

lemma etaleTopology_le_fpqcTopology : etaleTopology.{u} ≤ fpqcTopology :=
  etaleTopology_le_proetaleTopology.trans proetaleTopology_le_fpqcTopology

/-- The presheaf of `n`-th roots of unity is a sheaf for the étale topology on schemes. -/
theorem isSheaf_etaleTopology_rootsOfUnityPresheaf (n : ℕ) :
    Presheaf.IsSheaf etaleTopology (rootsOfUnityPresheaf.{u} n) :=
  (isSheaf_fpqcTopology_rootsOfUnityPresheaf n).of_le etaleTopology_le_fpqcTopology

instance (X : Scheme.{u}) : PreservesFiniteLimits (Etale.forget X) :=
  inferInstanceAs (PreservesFiniteLimits (MorphismProperty.Over.forget _ _ _))

instance (X : Scheme.{u}) : RepresentablyFlat (Etale.forget X) :=
  flat_of_preservesFiniteLimits _

instance isContinuous_etaleForget (X : Scheme.{u}) :
    (Etale.forget X).IsContinuous X.smallEtaleTopology (etaleTopology.over X) := by
  rw [Functor.isContinuous_iff_coverPreserving]
  exact Functor.coverPreserving_restrictedTopology (MorphismProperty.Over.forget _ ⊤ X) _

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
theorem etaleRootsOfUnitySheaf_val_obj (X : Scheme.{u}) (n : ℕ) (U : X.Etale) :
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

theorem etaleTateTwistOneSystem_obj (X : Scheme.{u}) (ℓ : ℕ) (r : ℕᵒᵖ) :
    (X.etaleTateTwistOneSystem ℓ).obj r = X.etaleTateTwistOne ℓ r.unop :=
  rfl

end AlgebraicGeometry.Scheme

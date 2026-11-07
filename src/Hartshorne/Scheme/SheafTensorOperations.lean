/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.TensorPower.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Hartshorne.Scheme.ModuleSheafTensor

/-!
# Tensor, symmetric and exterior powers of module sheaves

Hartshorne, *Algebraic Geometry*, II, Exercise 5.16 (printed p. 127).

Let `(X, 𝒪_X)` be a ringed space, given by a topological space `X` with a sheaf `R` of commutative
rings; `𝒪_X`-modules are `SheafOfModules (ringCatSheafOf R)` as in
`Hartshorne.Scheme.ModuleSheafTensor`. For an `𝒪_X`-module `F` and `r : ℕ` we define

* `moduleSheafTensorPower r F` (`T^r F`), the sheafification of `U ↦ ⨂^r_{𝒪_X(U)} F(U)`;
* `moduleSheafSymmetricPower r F` (`S^r F`), the sheafification of `U ↦ Sym^r_{𝒪_X(U)} F(U)`, where
  `Sym^r M = SymmetricPowerQuotient A M r` is the quotient of `⨂^r M` by the submodule spanned by
  the differences `m_{e(1)} ⊗ ⋯ ⊗ m_{e(r)} - m₁ ⊗ ⋯ ⊗ mᵣ` (the degree-`r` part of the symmetric
  algebra);
* `moduleSheafExteriorPower r F` (`⋀^r F`), the sheafification of `U ↦ ⋀^r_{𝒪_X(U)} F(U)`, with
  Mathlib's `exteriorPower` (the degree-`r` component of the exterior algebra).

The restriction maps of these presheaves are semilinear over the restriction maps of `𝒪_X`; they
come from the functoriality of `⨂^r`, `Sym^r`, `⋀^r` along semilinear maps (`tensorPowerMap`,
`symmetricPowerMap`, `exteriorPowerMap`).

Each power has a universal property: morphisms `T^r F ⟶ H` are the families of
`𝒪_X(U)`-multilinear maps `F(U)^r → H(U)` compatible with restriction (`ModuleSheafMultilinear`),
see `moduleSheafTensorPowerHomEquiv` and `moduleSheafTensorPower_universal`; for `S^r F` and
`⋀^r F` the families are required to be symmetric (`ModuleSheafMultilinear.IsSymmetric`) resp.
alternating (`ModuleSheafMultilinear.IsAlternating`).

Restriction to open subschemes: for schemes and an open immersion `f : Y ⟶ X`,
`moduleSheafTensorPowerRestrictIso` (and its symmetric and exterior analogues) identifies
`(T^r F)|_Y` with `T^r (F|_Y)`, compatibly with the universal multilinear maps
(`moduleSheafTensorPowerRestrictIso_multilinear`). This rests on the fact that sheafification of
presheaves of modules commutes with restriction to `Y` (`sheafificationRestrictHom` is an
isomorphism), deduced from Mathlib's compatibility of sheafification with the cocontinuous functor
`f.opensFunctor`.

The sheaves of graded algebras `T(F)`, `S(F)`, `⋀(F)`, whose homogeneous components are these
powers, are constructed in `Hartshorne.Scheme.SheafTensorAlgebras`.
-/

universe u

open scoped TensorProduct

namespace Hartshorne.SheafTensorOperations

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  {M N P : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module A M] [Module B N] [Module C P]

section Span

variable {ι : Type*} {σ : A →+* B} {τ : B →+* C} {ρ : A →+* C}

/-- Two composable semilinear maps agree with a third one if they do so on a spanning family. -/
theorem semilinear_eq_comp_of_span {u : ι → M} (hu : Submodule.span A (Set.range u) = ⊤)
    (F : M →ₛₗ[ρ] P) (G : M →ₛₗ[σ] N) (H : N →ₛₗ[τ] P) (hρ : ∀ a, ρ a = τ (σ a))
    (h : ∀ i, F (u i) = H (G (u i))) (x : M) : F x = H (G x) := by
  have hx : x ∈ Submodule.span A (Set.range u) := hu ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨i, rfl⟩ := hy; exact h i
  | zero => simp
  | add y z _ _ hy hz => simp [hy, hz]
  | smul a y _ hy => simp [hy, hρ]

/-- A semilinear endomorphism over a ring endomorphism acting trivially, fixing a spanning family,
is the identity. -/
theorem semilinear_eq_self_of_span {u : ι → M} (hu : Submodule.span A (Set.range u) = ⊤)
    {σ' : A →+* A} (F : M →ₛₗ[σ'] M) (hσ : ∀ a, σ' a = a) (h : ∀ i, F (u i) = u i) (x : M) :
    F x = x := by
  have hx : x ∈ Submodule.span A (Set.range u) := hu ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨i, rfl⟩ := hy; exact h i
  | zero => simp
  | add y z _ _ hy hz => simp [hy, hz]
  | smul a y _ hy => simp [hy, hσ]

end Span

variable (r : ℕ)

section TensorPower

/-- The `B`-multilinear map `m ↦ m₁ ⊗ ⋯ ⊗ mᵣ` precomposed with a `σ`-semilinear map in every
variable, as an `A`-multilinear map. -/
noncomputable def tensorPowerMapAux (σ : A →+* B) (f : M →ₛₗ[σ] N) :
    letI : Module A (⨂[B]^r N) := Module.compHom _ σ
    MultilinearMap A (fun _ : Fin r => M) (⨂[B]^r N) :=
  letI : Module A (⨂[B]^r N) := Module.compHom _ σ
  { toFun := fun m => PiTensorProduct.tprod B (fun i => f (m i))
    map_update_add' := fun m i x y => by
      simp only [Function.apply_update (fun _ => f), map_add]
      exact MultilinearMap.map_update_add _ _ _ _ _
    map_update_smul' := fun m i a x => by
      simp only [Function.apply_update (fun _ => f), map_smulₛₗ]
      exact MultilinearMap.map_update_smul _ _ _ _ _ }

/-- The `σ`-semilinear map `⨂[A]^r M → ⨂[B]^r N` induced by a `σ`-semilinear map `M → N`. -/
noncomputable def tensorPowerMap (σ : A →+* B) (f : M →ₛₗ[σ] N) :
    (⨂[A]^r M) →ₛₗ[σ] (⨂[B]^r N) :=
  letI : Module A (⨂[B]^r N) := Module.compHom _ σ
  { toFun := PiTensorProduct.lift (tensorPowerMapAux r σ f)
    map_add' := map_add _
    map_smul' := (PiTensorProduct.lift (tensorPowerMapAux r σ f)).map_smul }

@[simp]
theorem tensorPowerMap_tprod (σ : A →+* B) (f : M →ₛₗ[σ] N) (m : Fin r → M) :
    tensorPowerMap r σ f (PiTensorProduct.tprod A m) =
      PiTensorProduct.tprod B (fun i => f (m i)) := by
  let _ : Module A (⨂[B]^r N) := Module.compHom _ σ
  exact PiTensorProduct.lift.tprod m

theorem tensorPowerMap_id {σ : A →+* A} (hσ : ∀ a, σ a = a) (f : M →ₛₗ[σ] M)
    (hf : ∀ m, f m = m) (x : ⨂[A]^r M) : tensorPowerMap r σ f x = x :=
  semilinear_eq_self_of_span PiTensorProduct.span_tprod_eq_top _ hσ
    (fun m => by simp [hf]) x

theorem tensorPowerMap_comp {σ : A →+* B} {τ : B →+* C} {ρ : A →+* C}
    (hρ : ∀ a, ρ a = τ (σ a)) (f : M →ₛₗ[σ] N) (g : N →ₛₗ[τ] P) (h : M →ₛₗ[ρ] P)
    (hh : ∀ m, h m = g (f m)) (x : ⨂[A]^r M) :
    tensorPowerMap r ρ h x = tensorPowerMap r τ g (tensorPowerMap r σ f x) :=
  semilinear_eq_comp_of_span PiTensorProduct.span_tprod_eq_top _ _ _ hρ
    (fun m => by simp [hh]) x

end TensorPower

section SymmetricPower

variable (A M) in
/-- The submodule of `⨂[A]^r M` spanned by the differences `m_{e(1)} ⊗ ⋯ ⊗ m_{e(r)} - m₁ ⊗ ⋯ ⊗ mᵣ`
for permutations `e`. -/
noncomputable def symmetricPowerRel : Submodule A (⨂[A]^r M) :=
  Submodule.span A {x | ∃ (e : Equiv.Perm (Fin r)) (m : Fin r → M),
    x = PiTensorProduct.tprod A (m ∘ e) - PiTensorProduct.tprod A m}

variable (A M) in
/-- The `r`-th symmetric power of `M`, the quotient of `⨂[A]^r M` identifying tensors that differ
by a permutation of the factors. -/
abbrev SymmetricPowerQuotient := (⨂[A]^r M) ⧸ symmetricPowerRel A M r

variable (A M) in
/-- The universal symmetric multilinear map `M^r → Sym^r M`. -/
noncomputable def symmetricPowerTprod :
    MultilinearMap A (fun _ : Fin r => M) (SymmetricPowerQuotient A M r) :=
  (symmetricPowerRel A M r).mkQ.compMultilinearMap (PiTensorProduct.tprod A)

theorem symmetricPowerTprod_apply (m : Fin r → M) :
    symmetricPowerTprod A M r m =
      Submodule.Quotient.mk (PiTensorProduct.tprod A m) := rfl

theorem symmetricPowerTprod_perm (e : Equiv.Perm (Fin r)) (m : Fin r → M) :
    symmetricPowerTprod A M r (m ∘ e) = symmetricPowerTprod A M r m := by
  rw [symmetricPowerTprod_apply, symmetricPowerTprod_apply, Submodule.Quotient.eq]
  exact Submodule.subset_span ⟨e, m, rfl⟩

theorem span_symmetricPowerTprod :
    Submodule.span A (Set.range (symmetricPowerTprod A M r)) = ⊤ := by
  rw [symmetricPowerTprod, LinearMap.coe_compMultilinearMap, Set.range_comp,
    Submodule.span_image, PiTensorProduct.span_tprod_eq_top, Submodule.map_top,
    Submodule.range_mkQ]

/-- The linear map out of `Sym^r M` induced by a symmetric multilinear map. -/
noncomputable def symmetricPowerLift [Module A P] (φ : MultilinearMap A (fun _ : Fin r => M) P)
    (hφ : ∀ (e : Equiv.Perm (Fin r)) (m : Fin r → M), φ (m ∘ e) = φ m) :
    SymmetricPowerQuotient A M r →ₗ[A] P :=
  (symmetricPowerRel A M r).liftQ (PiTensorProduct.lift φ) (by
    rw [symmetricPowerRel, Submodule.span_le]
    rintro _ ⟨e, m, rfl⟩
    simp [hφ])

@[simp]
theorem symmetricPowerLift_tprod [Module A P] (φ : MultilinearMap A (fun _ : Fin r => M) P)
    (hφ : ∀ (e : Equiv.Perm (Fin r)) (m : Fin r → M), φ (m ∘ e) = φ m) (m : Fin r → M) :
    symmetricPowerLift r φ hφ (symmetricPowerTprod A M r m) = φ m := by
  simp [symmetricPowerLift, symmetricPowerTprod_apply]

theorem symmetricPower_linearMap_ext [Module A P] {f g : SymmetricPowerQuotient A M r →ₗ[A] P}
    (h : ∀ m, f (symmetricPowerTprod A M r m) = g (symmetricPowerTprod A M r m)) : f = g :=
  LinearMap.ext_on_range (span_symmetricPowerTprod r) h

/-- The `σ`-semilinear map `Sym^r_A M → Sym^r_B N` induced by a `σ`-semilinear map `M → N`. -/
noncomputable def symmetricPowerMap (σ : A →+* B) (f : M →ₛₗ[σ] N) :
    SymmetricPowerQuotient A M r →ₛₗ[σ] SymmetricPowerQuotient B N r :=
  (symmetricPowerRel A M r).mapQ (symmetricPowerRel B N r) (tensorPowerMap r σ f) (by
    rw [symmetricPowerRel, Submodule.span_le]
    rintro _ ⟨e, m, rfl⟩
    refine Submodule.subset_span ⟨e, fun i => f (m i), ?_⟩
    simp only [map_sub, tensorPowerMap_tprod]
    rfl)

@[simp]
theorem symmetricPowerMap_tprod (σ : A →+* B) (f : M →ₛₗ[σ] N) (m : Fin r → M) :
    symmetricPowerMap r σ f (symmetricPowerTprod A M r m) =
      symmetricPowerTprod B N r (fun i => f (m i)) := by
  simp [symmetricPowerMap, symmetricPowerTprod_apply]

theorem symmetricPowerMap_id {σ : A →+* A} (hσ : ∀ a, σ a = a) (f : M →ₛₗ[σ] M)
    (hf : ∀ m, f m = m) (x : SymmetricPowerQuotient A M r) : symmetricPowerMap r σ f x = x :=
  semilinear_eq_self_of_span (span_symmetricPowerTprod r) _ hσ
    (fun m => by simp [hf]) x

theorem symmetricPowerMap_comp {σ : A →+* B} {τ : B →+* C} {ρ : A →+* C}
    (hρ : ∀ a, ρ a = τ (σ a)) (f : M →ₛₗ[σ] N) (g : N →ₛₗ[τ] P) (h : M →ₛₗ[ρ] P)
    (hh : ∀ m, h m = g (f m)) (x : SymmetricPowerQuotient A M r) :
    symmetricPowerMap r ρ h x = symmetricPowerMap r τ g (symmetricPowerMap r σ f x) :=
  semilinear_eq_comp_of_span (span_symmetricPowerTprod r) _ _ _ hρ
    (fun m => by simp [hh]) x

end SymmetricPower

section ExteriorPower

/-- The `B`-alternating map `m ↦ m₁ ∧ ⋯ ∧ mᵣ` precomposed with a `σ`-semilinear map in every
variable, as an `A`-alternating map. -/
noncomputable def exteriorPowerMapAux (σ : A →+* B) (f : M →ₛₗ[σ] N) :
    letI : Module A (⋀[B]^r N) := Module.compHom _ σ
    M [⋀^Fin r]→ₗ[A] (⋀[B]^r N) :=
  letI : Module A (⋀[B]^r N) := Module.compHom _ σ
  { toFun := fun m => exteriorPower.ιMulti B r (fun i => f (m i))
    map_update_add' := fun m i x y => by
      simp only [Function.apply_update (fun _ => f), map_add]
      exact AlternatingMap.map_update_add _ _ _ _ _
    map_update_smul' := fun m i a x => by
      simp only [Function.apply_update (fun _ => f), map_smulₛₗ]
      exact AlternatingMap.map_update_smul _ _ _ _ _
    map_eq_zero_of_eq' := fun m i j hij hne =>
      AlternatingMap.map_eq_zero_of_eq _ _ (i := i) (j := j) (by simp [hij]) hne }

/-- The `σ`-semilinear map `⋀[A]^r M → ⋀[B]^r N` induced by a `σ`-semilinear map `M → N`. -/
noncomputable def exteriorPowerMap (σ : A →+* B) (f : M →ₛₗ[σ] N) :
    (⋀[A]^r M) →ₛₗ[σ] (⋀[B]^r N) :=
  letI : Module A (⋀[B]^r N) := Module.compHom _ σ
  { toFun := exteriorPower.alternatingMapLinearEquiv (exteriorPowerMapAux r σ f)
    map_add' := map_add _
    map_smul' := (exteriorPower.alternatingMapLinearEquiv (exteriorPowerMapAux r σ f)).map_smul }

@[simp]
theorem exteriorPowerMap_ιMulti (σ : A →+* B) (f : M →ₛₗ[σ] N) (m : Fin r → M) :
    exteriorPowerMap r σ f (exteriorPower.ιMulti A r m) =
      exteriorPower.ιMulti B r (fun i => f (m i)) := by
  let _ : Module A (⋀[B]^r N) := Module.compHom _ σ
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ m

theorem exteriorPowerMap_id {σ : A →+* A} (hσ : ∀ a, σ a = a) (f : M →ₛₗ[σ] M)
    (hf : ∀ m, f m = m) (x : ⋀[A]^r M) : exteriorPowerMap r σ f x = x :=
  semilinear_eq_self_of_span (exteriorPower.ιMulti_span A r M) _ hσ
    (fun m => by simp [hf]) x

theorem exteriorPowerMap_comp {σ : A →+* B} {τ : B →+* C} {ρ : A →+* C}
    (hρ : ∀ a, ρ a = τ (σ a)) (f : M →ₛₗ[σ] N) (g : N →ₛₗ[τ] P) (h : M →ₛₗ[ρ] P)
    (hh : ∀ m, h m = g (f m)) (x : ⋀[A]^r M) :
    exteriorPowerMap r ρ h x = exteriorPowerMap r τ g (exteriorPowerMap r σ f x) :=
  semilinear_eq_comp_of_span (exteriorPower.ιMulti_span A r M) _ _ _ hρ
    (fun m => by simp [hh]) x

end ExteriorPower

end Hartshorne.SheafTensorOperations

namespace Hartshorne

open CategoryTheory TopologicalSpace Opposite SheafTensorOperations

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

namespace SheafTensorOperations

/-- A presheaf of modules built from modules of sections and semilinear restriction maps. -/
noncomputable def presheafOfSemilinear
    (obj : ∀ U : (Opens X)ᵒᵖ, ModuleCat.{u} ((R.obj ⋙ forget₂ CommRingCat RingCat).obj U))
    (map : ∀ {U V : (Opens X)ᵒᵖ} (i : U ⟶ V),
      obj U →ₛₗ[((R.obj ⋙ forget₂ CommRingCat RingCat).map i).hom] obj V)
    (map_id : ∀ (U : (Opens X)ᵒᵖ) (x : obj U), map (𝟙 U) x = x)
    (map_comp : ∀ {U V W : (Opens X)ᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) (x : obj U),
      map (i ≫ j) x = map j (map i x)) :
    PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat) where
  obj := obj
  map {U V} i := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars ((R.obj ⋙ forget₂ CommRingCat RingCat).map i).hom).obj
      (obj V))
    { toFun := map i
      map_add' := map_add _
      map_smul' := (map i).map_smulₛₗ }
  map_id U := by
    ext x
    exact map_id U x
  map_comp i j := by
    ext x
    exact map_comp i j x

@[simp]
theorem presheafOfSemilinear_map_apply
    (obj : ∀ U : (Opens X)ᵒᵖ, ModuleCat.{u} ((R.obj ⋙ forget₂ CommRingCat RingCat).obj U))
    (map : ∀ {U V : (Opens X)ᵒᵖ} (i : U ⟶ V),
      obj U →ₛₗ[((R.obj ⋙ forget₂ CommRingCat RingCat).map i).hom] obj V)
    (map_id : ∀ (U : (Opens X)ᵒᵖ) (x : obj U), map (𝟙 U) x = x)
    (map_comp : ∀ {U V W : (Opens X)ᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) (x : obj U),
      map (i ≫ j) x = map j (map i x)) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (x : obj U) :
    (presheafOfSemilinear obj map map_id map_comp).map i x = map i x := rfl

theorem ringMap_id_apply (U : (Opens X)ᵒᵖ) (a : (R.obj ⋙ forget₂ CommRingCat RingCat).obj U) :
    ((R.obj ⋙ forget₂ CommRingCat RingCat).map (𝟙 U)).hom a = a := by
  simp

theorem ringMap_comp_apply {U V W : (Opens X)ᵒᵖ} (i : U ⟶ V) (j : V ⟶ W)
    (a : (R.obj ⋙ forget₂ CommRingCat RingCat).obj U) :
    ((R.obj ⋙ forget₂ CommRingCat RingCat).map (i ≫ j)).hom a =
      ((R.obj ⋙ forget₂ CommRingCat RingCat).map j).hom
        (((R.obj ⋙ forget₂ CommRingCat RingCat).map i).hom a) := by
  simp

theorem restrictₛₗ_id (M : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat))
    (U : (Opens X)ᵒᵖ) (x : M.obj U) : M.restrictₛₗ (𝟙 U) x = x := by
  rw [PresheafOfModules.restrictₛₗ_apply]
  simp

theorem restrictₛₗ_comp (M : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat))
    {U V W : (Opens X)ᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) (x : M.obj U) :
    M.restrictₛₗ (i ≫ j) x = M.restrictₛₗ j (M.restrictₛₗ i x) :=
  PresheafOfModules.map_comp_apply M i j x

end SheafTensorOperations

variable (r : ℕ)

section TensorPowerSheaf

/-- The presheaf of modules `U ↦ ⨂^r_{𝒪_X(U)} F(U)`. -/
noncomputable def moduleSheafTensorPowerPresheaf (F : SheafOfModules.{u} (ringCatSheafOf R)) :
    PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat) :=
  presheafOfSemilinear (fun U => ModuleCat.of _ (⨂[_]^r (F.val.obj U)))
    (fun i => tensorPowerMap r _ (F.val.restrictₛₗ i))
    (fun U x => tensorPowerMap_id r (ringMap_id_apply U) _ (restrictₛₗ_id F.val U) x)
    (fun i j x => tensorPowerMap_comp r (ringMap_comp_apply i j) _ _ _
      (restrictₛₗ_comp F.val i j) x)

variable (F : SheafOfModules.{u} (ringCatSheafOf R))

/-- **Tensor powers of a module sheaf.** The `𝒪_X`-module `T^r F`, the sheafification of the
presheaf `U ↦ ⨂^r_{𝒪_X(U)} F(U)`. -/
noncomputable def moduleSheafTensorPower : SheafOfModules.{u} (ringCatSheafOf R) :=
  (PresheafOfModules.sheafification (𝟙 (ringCatSheafOf R).obj)).obj
    (moduleSheafTensorPowerPresheaf r F)

/-- The canonical map from the presheaf `U ↦ ⨂^r F(U)` to its sheafification `T^r F`. -/
noncomputable def moduleSheafTensorPowerUnit :
    moduleSheafTensorPowerPresheaf r F ⟶ (moduleSheafTensorPower r F).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheafOf R).obj)).unit.app
    (moduleSheafTensorPowerPresheaf r F)

/-- An `r`-multilinear morphism `F^r → H` of `𝒪_X`-modules: for every open `U`, an
`𝒪_X(U)`-multilinear map `F(U)^r → H(U)`, compatible with restriction. -/
structure ModuleSheafMultilinear (H : SheafOfModules.{u} (ringCatSheafOf R)) where
  /-- The multilinear map on sections over `U`. -/
  app (U : (Opens X)ᵒᵖ) : MultilinearMap ((R.obj ⋙ forget₂ CommRingCat RingCat).obj U)
    (fun _ : Fin r => F.val.obj U) (H.val.obj U)
  /-- Compatibility with restriction. -/
  naturality {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (m : Fin r → F.val.obj U) :
    H.val.map i (app U m) = app V (fun k => F.val.map i (m k))

namespace ModuleSheafMultilinear

variable {r F} {H K L : SheafOfModules.{u} (ringCatSheafOf R)}

@[ext]
lemma ext {β γ : ModuleSheafMultilinear r F H} (h : ∀ U m, β.app U m = γ.app U m) : β = γ := by
  cases β; cases γ
  congr
  funext U
  exact MultilinearMap.ext (h U)

/-- Composition of a multilinear morphism with a morphism of `𝒪_X`-modules. -/
noncomputable def postcomp (β : ModuleSheafMultilinear r F H) (φ : H ⟶ K) :
    ModuleSheafMultilinear r F K where
  app U := (φ.val.app U).hom.compMultilinearMap (β.app U)
  naturality i m := by
    have h := congrArg (fun k => k.hom (β.app _ m)) (φ.val.naturality i)
    exact h.symm.trans (congrArg (fun y => (φ.val.app _).hom y) (β.naturality i m))

@[simp]
lemma postcomp_app (β : ModuleSheafMultilinear r F H) (φ : H ⟶ K) (U : (Opens X)ᵒᵖ)
    (m : Fin r → F.val.obj U) : (β.postcomp φ).app U m = φ.val.app U (β.app U m) := rfl

lemma postcomp_postcomp (β : ModuleSheafMultilinear r F H) (φ : H ⟶ K) (ψ : K ⟶ L) :
    (β.postcomp φ).postcomp ψ = β.postcomp (φ ≫ ψ) := by
  ext U m
  rfl

/-- A multilinear morphism is symmetric if on every open it is invariant under permuting its
arguments. -/
def IsSymmetric (β : ModuleSheafMultilinear r F H) : Prop :=
  ∀ (U : (Opens X)ᵒᵖ) (e : Equiv.Perm (Fin r)) (m : Fin r → F.val.obj U),
    β.app U (m ∘ e) = β.app U m

/-- A multilinear morphism is alternating if on every open it vanishes whenever two of its
arguments coincide. -/
def IsAlternating (β : ModuleSheafMultilinear r F H) : Prop :=
  ∀ (U : (Opens X)ᵒᵖ) (m : Fin r → F.val.obj U) (i j : Fin r), m i = m j → i ≠ j →
    β.app U m = 0

lemma IsSymmetric.postcomp {β : ModuleSheafMultilinear r F H} (hβ : β.IsSymmetric) (φ : H ⟶ K) :
    (β.postcomp φ).IsSymmetric := fun U e m => by
  rw [postcomp_app, postcomp_app, hβ U e m]

lemma IsAlternating.postcomp {β : ModuleSheafMultilinear r F H} (hβ : β.IsAlternating)
    (φ : H ⟶ K) : (β.postcomp φ).IsAlternating := fun U m i j h hne => by
  rw [postcomp_app, hβ U m i j h hne, map_zero]

end ModuleSheafMultilinear

namespace SheafTensorOperations

variable (H : SheafOfModules.{u} (ringCatSheafOf R))

/-- Morphisms out of the presheaf `U ↦ ⨂^r F(U)` are the multilinear morphisms. -/
noncomputable def tensorPowerPresheafHomEquiv :
    (moduleSheafTensorPowerPresheaf r F ⟶ H.val) ≃ ModuleSheafMultilinear r F H where
  toFun ψ :=
    { app U := (ψ.app U).hom.compMultilinearMap (PiTensorProduct.tprod _)
      naturality i m := by
        have h := congrArg (fun k => k.hom (PiTensorProduct.tprod _ m)) (ψ.naturality i)
        refine h.symm.trans ?_
        change (ψ.app _).hom (tensorPowerMap r _ (F.val.restrictₛₗ i) _) = _
        rw [tensorPowerMap_tprod]
        rfl }
  invFun β :=
    { app U := ModuleCat.ofHom (PiTensorProduct.lift (β.app U))
      naturality {U V} i := by
        ext x
        change PiTensorProduct.lift (β.app V) (tensorPowerMap r _ (F.val.restrictₛₗ i) x) =
          H.val.map i (PiTensorProduct.lift (β.app U) x)
        refine semilinear_eq_comp_of_span (u := PiTensorProduct.tprod _)
          PiTensorProduct.span_tprod_eq_top ((H.val.restrictₛₗ i).comp
            (PiTensorProduct.lift (β.app U)))
          (tensorPowerMap r _ (F.val.restrictₛₗ i)) (PiTensorProduct.lift (β.app V))
          (fun a => rfl) (fun m => ?_) x |>.symm
        simp only [LinearMap.comp_apply, PiTensorProduct.lift.tprod, tensorPowerMap_tprod]
        exact β.naturality i m }
  left_inv ψ := by
    ext U : 1
    ext : 1
    apply PiTensorProduct.ext
    ext m
    exact PiTensorProduct.lift.tprod m
  right_inv β := by
    ext U m
    exact PiTensorProduct.lift.tprod m

end SheafTensorOperations

variable {r F} {H K : SheafOfModules.{u} (ringCatSheafOf R)}

variable (r F H) in
/-- **Universal property of the tensor power.** Morphisms `T^r F ⟶ H` correspond bijectively to
`r`-multilinear morphisms `F^r → H`. -/
noncomputable def moduleSheafTensorPowerHomEquiv :
    (moduleSheafTensorPower r F ⟶ H) ≃ ModuleSheafMultilinear r F H :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheafOf R).obj)).homEquiv
    (moduleSheafTensorPowerPresheaf r F) H).trans (tensorPowerPresheafHomEquiv r F H)

variable (r F) in
/-- The universal multilinear morphism `F^r → T^r F`, `(f₁, …, fᵣ) ↦ f₁ ⊗ ⋯ ⊗ fᵣ`. -/
noncomputable def moduleSheafTensorPowerMultilinear :
    ModuleSheafMultilinear r F (moduleSheafTensorPower r F) :=
  tensorPowerPresheafHomEquiv r F _ (moduleSheafTensorPowerUnit r F)

lemma moduleSheafTensorPowerMultilinear_app (U : (Opens X)ᵒᵖ) (m : Fin r → F.val.obj U) :
    (moduleSheafTensorPowerMultilinear r F).app U m =
      (moduleSheafTensorPowerUnit r F).app U (PiTensorProduct.tprod _ m) :=
  rfl

lemma moduleSheafTensorPowerHomEquiv_apply (φ : moduleSheafTensorPower r F ⟶ H) :
    moduleSheafTensorPowerHomEquiv r F H φ =
      (moduleSheafTensorPowerMultilinear r F).postcomp φ := by
  ext U m
  rfl

/-- **Universal property of the tensor power.** Every multilinear morphism `F^r → H` factors
uniquely through the universal multilinear morphism `F^r → T^r F`. -/
theorem moduleSheafTensorPower_universal (β : ModuleSheafMultilinear r F H) :
    ∃! φ : moduleSheafTensorPower r F ⟶ H,
      (moduleSheafTensorPowerMultilinear r F).postcomp φ = β := by
  refine ⟨(moduleSheafTensorPowerHomEquiv r F H).symm β, ?_, fun φ hφ => ?_⟩
  · dsimp only
    rw [← moduleSheafTensorPowerHomEquiv_apply, Equiv.apply_symm_apply]
  · rw [← hφ, ← moduleSheafTensorPowerHomEquiv_apply, Equiv.symm_apply_apply]

end TensorPowerSheaf

end Hartshorne

namespace Hartshorne

open CategoryTheory TopologicalSpace Opposite SheafTensorOperations

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
variable (r : ℕ)

section SymmetricPowerSheaf

/-- The presheaf of modules `U ↦ Sym^r_{𝒪_X(U)} F(U)`. -/
noncomputable def moduleSheafSymmetricPowerPresheaf (F : SheafOfModules.{u} (ringCatSheafOf R)) :
    PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat) :=
  presheafOfSemilinear (fun U => ModuleCat.of _ (SymmetricPowerQuotient _ (F.val.obj U) r))
    (fun i => symmetricPowerMap r _ (F.val.restrictₛₗ i))
    (fun U x => symmetricPowerMap_id r (ringMap_id_apply U) _ (restrictₛₗ_id F.val U) x)
    (fun i j x => symmetricPowerMap_comp r (ringMap_comp_apply i j) _ _ _
      (restrictₛₗ_comp F.val i j) x)

variable (F : SheafOfModules.{u} (ringCatSheafOf R))

/-- **Symmetric powers of a module sheaf.** The `𝒪_X`-module `S^r F`, the sheafification of the
presheaf `U ↦ Sym^r_{𝒪_X(U)} F(U)`. -/
noncomputable def moduleSheafSymmetricPower : SheafOfModules.{u} (ringCatSheafOf R) :=
  (PresheafOfModules.sheafification (𝟙 (ringCatSheafOf R).obj)).obj
    (moduleSheafSymmetricPowerPresheaf r F)

/-- The canonical map from the presheaf `U ↦ Sym^r F(U)` to its sheafification `S^r F`. -/
noncomputable def moduleSheafSymmetricPowerUnit :
    moduleSheafSymmetricPowerPresheaf r F ⟶ (moduleSheafSymmetricPower r F).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheafOf R).obj)).unit.app
    (moduleSheafSymmetricPowerPresheaf r F)

namespace SheafTensorOperations

variable (H : SheafOfModules.{u} (ringCatSheafOf R))

/-- Morphisms out of the presheaf `U ↦ Sym^r F(U)` are the symmetric multilinear morphisms. -/
noncomputable def symmetricPowerPresheafHomEquiv :
    (moduleSheafSymmetricPowerPresheaf r F ⟶ H.val) ≃
      {β : ModuleSheafMultilinear r F H // β.IsSymmetric} where
  toFun ψ :=
    ⟨{ app U := (ψ.app U).hom.compMultilinearMap (symmetricPowerTprod _ _ r)
       naturality {U V} i m := by
         have h := congrArg (fun k => k.hom (symmetricPowerTprod
           ((R.obj ⋙ forget₂ CommRingCat RingCat).obj U) (F.val.obj U) r m)) (ψ.naturality i)
         refine h.symm.trans ?_
         change (ψ.app _).hom (symmetricPowerMap r _ (F.val.restrictₛₗ i) _) = _
         rw [symmetricPowerMap_tprod]
         rfl },
      fun U e m => congrArg (ψ.app U).hom (symmetricPowerTprod_perm r e m)⟩
  invFun β :=
    { app U := ModuleCat.ofHom (symmetricPowerLift r (β.1.app U) (β.2 U))
      naturality {U V} i := by
        ext x
        change symmetricPowerLift r (β.1.app V) (β.2 V)
            (symmetricPowerMap r _ (F.val.restrictₛₗ i) x) =
          H.val.map i (symmetricPowerLift r (β.1.app U) (β.2 U) x)
        refine semilinear_eq_comp_of_span (span_symmetricPowerTprod r)
          ((H.val.restrictₛₗ i).comp (symmetricPowerLift r (β.1.app U) (β.2 U)))
          (symmetricPowerMap r _ (F.val.restrictₛₗ i)) (symmetricPowerLift r (β.1.app V) (β.2 V))
          (fun a => rfl) (fun m => ?_) x |>.symm
        simp only [LinearMap.comp_apply, symmetricPowerLift_tprod, symmetricPowerMap_tprod]
        exact β.1.naturality i m }
  left_inv ψ := by
    ext U : 1
    ext : 1
    refine symmetricPower_linearMap_ext r (fun m => ?_)
    exact symmetricPowerLift_tprod r _
      (fun e m => congrArg (ψ.app U).hom (symmetricPowerTprod_perm r e m)) m
  right_inv β := by
    apply Subtype.ext
    ext U m
    exact symmetricPowerLift_tprod r _ (β.2 U) m

end SheafTensorOperations

variable {r F} {H K : SheafOfModules.{u} (ringCatSheafOf R)}

variable (r F H) in
/-- **Universal property of the symmetric power.** Morphisms `S^r F ⟶ H` correspond bijectively
to symmetric `r`-multilinear morphisms `F^r → H`. -/
noncomputable def moduleSheafSymmetricPowerHomEquiv :
    (moduleSheafSymmetricPower r F ⟶ H) ≃ {β : ModuleSheafMultilinear r F H // β.IsSymmetric} :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheafOf R).obj)).homEquiv
    (moduleSheafSymmetricPowerPresheaf r F) H).trans (symmetricPowerPresheafHomEquiv r F H)

variable (r F) in
/-- The universal symmetric multilinear morphism `F^r → S^r F`. -/
noncomputable def moduleSheafSymmetricPowerMultilinear :
    ModuleSheafMultilinear r F (moduleSheafSymmetricPower r F) :=
  (symmetricPowerPresheafHomEquiv r F _ (moduleSheafSymmetricPowerUnit r F)).1

lemma moduleSheafSymmetricPowerMultilinear_isSymmetric :
    (moduleSheafSymmetricPowerMultilinear r F).IsSymmetric :=
  (symmetricPowerPresheafHomEquiv r F _ (moduleSheafSymmetricPowerUnit r F)).2

lemma moduleSheafSymmetricPowerMultilinear_app (U : (Opens X)ᵒᵖ) (m : Fin r → F.val.obj U) :
    (moduleSheafSymmetricPowerMultilinear r F).app U m =
      (moduleSheafSymmetricPowerUnit r F).app U
        (symmetricPowerTprod ((R.obj ⋙ forget₂ CommRingCat RingCat).obj U) (F.val.obj U) r m) :=
  rfl

lemma moduleSheafSymmetricPowerHomEquiv_apply (φ : moduleSheafSymmetricPower r F ⟶ H) :
    (moduleSheafSymmetricPowerHomEquiv r F H φ).1 =
      (moduleSheafSymmetricPowerMultilinear r F).postcomp φ := by
  ext U m
  rfl

/-- **Universal property of the symmetric power.** Every symmetric multilinear morphism
`F^r → H` factors uniquely through the universal one `F^r → S^r F`. -/
theorem moduleSheafSymmetricPower_universal (β : ModuleSheafMultilinear r F H)
    (hβ : β.IsSymmetric) :
    ∃! φ : moduleSheafSymmetricPower r F ⟶ H,
      (moduleSheafSymmetricPowerMultilinear r F).postcomp φ = β := by
  refine ⟨(moduleSheafSymmetricPowerHomEquiv r F H).symm ⟨β, hβ⟩, ?_, fun φ hφ => ?_⟩
  · dsimp only
    rw [← moduleSheafSymmetricPowerHomEquiv_apply, Equiv.apply_symm_apply]
  · apply (moduleSheafSymmetricPowerHomEquiv r F H).injective
    rw [Equiv.apply_symm_apply]
    exact Subtype.ext ((moduleSheafSymmetricPowerHomEquiv_apply φ).trans hφ)

end SymmetricPowerSheaf

section ExteriorPowerSheaf

/-- The presheaf of modules `U ↦ ⋀^r_{𝒪_X(U)} F(U)`. -/
noncomputable def moduleSheafExteriorPowerPresheaf (F : SheafOfModules.{u} (ringCatSheafOf R)) :
    PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat) :=
  presheafOfSemilinear (fun U => ModuleCat.of _ (⋀[_]^r (F.val.obj U)))
    (fun i => exteriorPowerMap r _ (F.val.restrictₛₗ i))
    (fun U x => exteriorPowerMap_id r (ringMap_id_apply U) _ (restrictₛₗ_id F.val U) x)
    (fun i j x => exteriorPowerMap_comp r (ringMap_comp_apply i j) _ _ _
      (restrictₛₗ_comp F.val i j) x)

variable (F : SheafOfModules.{u} (ringCatSheafOf R))

/-- **Exterior powers of a module sheaf.** The `𝒪_X`-module `⋀^r F`, the sheafification of the
presheaf `U ↦ ⋀^r_{𝒪_X(U)} F(U)`. -/
noncomputable def moduleSheafExteriorPower : SheafOfModules.{u} (ringCatSheafOf R) :=
  (PresheafOfModules.sheafification (𝟙 (ringCatSheafOf R).obj)).obj
    (moduleSheafExteriorPowerPresheaf r F)

/-- The canonical map from the presheaf `U ↦ ⋀^r F(U)` to its sheafification `⋀^r F`. -/
noncomputable def moduleSheafExteriorPowerUnit :
    moduleSheafExteriorPowerPresheaf r F ⟶ (moduleSheafExteriorPower r F).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheafOf R).obj)).unit.app
    (moduleSheafExteriorPowerPresheaf r F)

namespace SheafTensorOperations

variable (H : SheafOfModules.{u} (ringCatSheafOf R))

/-- Morphisms out of the presheaf `U ↦ ⋀^r F(U)` are the alternating multilinear morphisms. -/
noncomputable def exteriorPowerPresheafHomEquiv :
    (moduleSheafExteriorPowerPresheaf r F ⟶ H.val) ≃
      {β : ModuleSheafMultilinear r F H // β.IsAlternating} where
  toFun ψ :=
    ⟨{ app U := ((ψ.app U).hom.compAlternatingMap (exteriorPower.ιMulti _ r)).toMultilinearMap
       naturality i m := by
         have h := congrArg (fun k => k.hom (exteriorPower.ιMulti _ r m)) (ψ.naturality i)
         refine h.symm.trans ?_
         change (ψ.app _).hom (exteriorPowerMap r _ (F.val.restrictₛₗ i) _) = _
         rw [exteriorPowerMap_ιMulti]
         rfl },
      fun U m i j h hne =>
        ((ψ.app U).hom.compAlternatingMap (exteriorPower.ιMulti _ r)).map_eq_zero_of_eq m h hne⟩
  invFun β :=
    { app U := ModuleCat.ofHom (exteriorPower.alternatingMapLinearEquiv
        { β.1.app U with map_eq_zero_of_eq' := β.2 U })
      naturality {U V} i := by
        ext x
        change exteriorPower.alternatingMapLinearEquiv
            { β.1.app V with map_eq_zero_of_eq' := β.2 V }
            (exteriorPowerMap r _ (F.val.restrictₛₗ i) x) =
          H.val.map i (exteriorPower.alternatingMapLinearEquiv
            { β.1.app U with map_eq_zero_of_eq' := β.2 U } x)
        refine semilinear_eq_comp_of_span (exteriorPower.ιMulti_span _ r _)
          ((H.val.restrictₛₗ i).comp (exteriorPower.alternatingMapLinearEquiv
            { β.1.app U with map_eq_zero_of_eq' := β.2 U }))
          (exteriorPowerMap r _ (F.val.restrictₛₗ i))
          (exteriorPower.alternatingMapLinearEquiv { β.1.app V with map_eq_zero_of_eq' := β.2 V })
          (fun a => rfl) (fun m => ?_) x |>.symm
        simp only [LinearMap.comp_apply, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
          exteriorPowerMap_ιMulti]
        exact β.1.naturality i m }
  left_inv ψ := by
    ext U : 1
    ext : 1
    apply exteriorPower.linearMap_ext
    ext m
    exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ m
  right_inv β := by
    apply Subtype.ext
    ext U m
    exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ m

end SheafTensorOperations

variable {r F} {H K : SheafOfModules.{u} (ringCatSheafOf R)}

variable (r F H) in
/-- **Universal property of the exterior power.** Morphisms `⋀^r F ⟶ H` correspond bijectively
to alternating `r`-multilinear morphisms `F^r → H`. -/
noncomputable def moduleSheafExteriorPowerHomEquiv :
    (moduleSheafExteriorPower r F ⟶ H) ≃ {β : ModuleSheafMultilinear r F H // β.IsAlternating} :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheafOf R).obj)).homEquiv
    (moduleSheafExteriorPowerPresheaf r F) H).trans (exteriorPowerPresheafHomEquiv r F H)

variable (r F) in
/-- The universal alternating multilinear morphism `F^r → ⋀^r F`,
`(f₁, …, fᵣ) ↦ f₁ ∧ ⋯ ∧ fᵣ`. -/
noncomputable def moduleSheafExteriorPowerMultilinear :
    ModuleSheafMultilinear r F (moduleSheafExteriorPower r F) :=
  (exteriorPowerPresheafHomEquiv r F _ (moduleSheafExteriorPowerUnit r F)).1

lemma moduleSheafExteriorPowerMultilinear_isAlternating :
    (moduleSheafExteriorPowerMultilinear r F).IsAlternating :=
  (exteriorPowerPresheafHomEquiv r F _ (moduleSheafExteriorPowerUnit r F)).2

lemma moduleSheafExteriorPowerMultilinear_app (U : (Opens X)ᵒᵖ) (m : Fin r → F.val.obj U) :
    (moduleSheafExteriorPowerMultilinear r F).app U m =
      (moduleSheafExteriorPowerUnit r F).app U (exteriorPower.ιMulti _ r m) :=
  rfl

lemma moduleSheafExteriorPowerHomEquiv_apply (φ : moduleSheafExteriorPower r F ⟶ H) :
    (moduleSheafExteriorPowerHomEquiv r F H φ).1 =
      (moduleSheafExteriorPowerMultilinear r F).postcomp φ := by
  ext U m
  rfl

/-- **Universal property of the exterior power.** Every alternating multilinear morphism
`F^r → H` factors uniquely through the universal one `F^r → ⋀^r F`. -/
theorem moduleSheafExteriorPower_universal (β : ModuleSheafMultilinear r F H)
    (hβ : β.IsAlternating) :
    ∃! φ : moduleSheafExteriorPower r F ⟶ H,
      (moduleSheafExteriorPowerMultilinear r F).postcomp φ = β := by
  refine ⟨(moduleSheafExteriorPowerHomEquiv r F H).symm ⟨β, hβ⟩, ?_, fun φ hφ => ?_⟩
  · dsimp only
    rw [← moduleSheafExteriorPowerHomEquiv_apply, Equiv.apply_symm_apply]
  · apply (moduleSheafExteriorPowerHomEquiv r F H).injective
    rw [Equiv.apply_symm_apply]
    exact Subtype.ext ((moduleSheafExteriorPowerHomEquiv_apply φ).trans hφ)

end ExteriorPowerSheaf

end Hartshorne

namespace Hartshorne

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry SheafTensorOperations

section Restriction

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]

namespace SheafTensorOperations


/-- The morphism of sheaves of rings along which modules are restricted to an open immersion. -/
noncomputable def restrictRingHom :
    ringCatSheafOf Y.sheaf ⟶ (f.opensFunctor.sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj (ringCatSheafOf X.sheaf) :=
  letI α : Y.presheaf ⟶ f.opensFunctor.op ⋙ X.presheaf := { app U := (f.appIso U.unop).inv }
  ⟨Functor.whiskerRight α (forget₂ CommRingCat RingCat)⟩

/-- Restriction of module sheaves along an open immersion `f : Y ⟶ X`. It is definitionally
`Scheme.Modules.restrictFunctor f`. -/
noncomputable abbrev restrictModule :
    SheafOfModules.{u} (ringCatSheafOf X.sheaf) ⥤ SheafOfModules.{u} (ringCatSheafOf Y.sheaf) :=
  SheafOfModules.pushforward (restrictRingHom f)

theorem restrictModule_eq : restrictModule f = Scheme.Modules.restrictFunctor f := rfl

/-- Restriction along an open immersion commutes with sheafification of presheaves of modules:
the comparison morphism. -/
noncomputable def sheafificationRestrictHom 
    (P : PresheafOfModules.{u} (ringCatSheafOf X.sheaf).obj) :
    (PresheafOfModules.sheafification (𝟙 (ringCatSheafOf Y.sheaf).obj)).obj
        ((PresheafOfModules.pushforward (restrictRingHom f).hom).obj P) ⟶
      (restrictModule f).obj
        ((PresheafOfModules.sheafification (𝟙 (ringCatSheafOf X.sheaf).obj)).obj P) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheafOf Y.sheaf).obj)).homEquiv _ _).symm
    ((PresheafOfModules.pushforward (restrictRingHom f).hom).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheafOf X.sheaf).obj)).unit.app P))

theorem toSheafify_sheafificationRestrictHom 
    (P : PresheafOfModules.{u} (ringCatSheafOf X.sheaf).obj) :
    toSheafify (Opens.grothendieckTopology Y) (f.opensFunctor.op ⋙ P.presheaf) ≫
      ((SheafOfModules.toSheaf _).map (sheafificationRestrictHom f P)).hom =
    Functor.whiskerLeft f.opensFunctor.op
      (toSheafify (Opens.grothendieckTopology X) P.presheaf) := by
  have h1 := PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def
    (𝟙 (ringCatSheafOf Y.sheaf).obj)
    (sheafificationRestrictHom f P)
  have h2 : PresheafOfModules.sheafificationHomEquiv (𝟙 (ringCatSheafOf Y.sheaf).obj)
      (sheafificationRestrictHom f P) = (PresheafOfModules.pushforward (restrictRingHom f).hom).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheafOf X.sheaf).obj)).unit.app
          P) :=
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (ringCatSheafOf Y.sheaf).obj)).homEquiv _ _).apply_symm_apply _
  rw [h2] at h1
  exact h1.symm

instance 
    (P : PresheafOfModules.{u} (ringCatSheafOf X.sheaf).obj) :
    IsIso (sheafificationRestrictHom f P) := by
  have h : (SheafOfModules.toSheaf _).map (sheafificationRestrictHom f P) =
      (f.opensFunctor.pushforwardContinuousSheafificationCompatibility AddCommGrpCat.{u}
        (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).hom.app P.presheaf := by
    ext1
    apply sheafify_hom_ext
    · exact ((presheafToSheaf _ _ ⋙ f.opensFunctor.sheafPushforwardContinuous _ _ _).obj
        P.presheaf).property
    · exact (toSheafify_sheafificationRestrictHom f P).trans
        (Functor.toSheafify_pullbackSheafificationCompatibility _ _ _ _ P.presheaf).symm
  have : IsIso ((SheafOfModules.toSheaf _).map (sheafificationRestrictHom f P)) := by
    rw [h]
    exact inferInstanceAs (IsIso ((f.opensFunctor.pushforwardContinuousSheafificationCompatibility
      AddCommGrpCat.{u} (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).app
        P.presheaf).hom)
  exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf _)

/-- The ring isomorphism `𝒪_Y(W) ≅ 𝒪_X(f(W))` used to restrict modules along `f`. -/
noncomputable def restrictRing (W : (Opens Y)ᵒᵖ) :
    (Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj W →+*
      (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (f.opensFunctor.op.obj W) :=
  (f.appIso W.unop).inv.hom

/-- The inverse of `restrictRing`. -/
noncomputable def restrictRingInv (W : (Opens Y)ᵒᵖ) :
    (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (f.opensFunctor.op.obj W) →+*
      (Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj W :=
  (f.appIso W.unop).hom.hom

theorem restrictRing_restrictRingInv (W : (Opens Y)ᵒᵖ)
    (b : (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (f.opensFunctor.op.obj W)) :
    restrictRing f W (restrictRingInv f W b) = b :=
  (f.appIso W.unop).hom_inv_id_apply b

theorem restrictRingInv_restrictRing (W : (Opens Y)ᵒᵖ)
    (a : (Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj W) :
    restrictRingInv f W (restrictRing f W a) = a :=
  (f.appIso W.unop).inv_hom_id_apply a

theorem restrictRing_naturality {W W' : (Opens Y)ᵒᵖ} (i : W ⟶ W')
    (a : (Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj W) :
    restrictRing f W' (((Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat).map i).hom a) =
      ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).map (f.opensFunctor.op.map i)).hom
        (restrictRing f W a) :=
  congrArg (fun k => k.hom a) ((restrictRingHom f).hom.naturality i)

theorem sheafificationRestrictHom_unit 
    (P : PresheafOfModules.{u} (ringCatSheafOf X.sheaf).obj)
    (W : (Opens Y)ᵒᵖ) (y : P.obj (f.opensFunctor.op.obj W)) :
    (sheafificationRestrictHom f P).val.app W
        (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheafOf Y.sheaf).obj)).unit.app
          ((PresheafOfModules.pushforward (restrictRingHom f).hom).obj P)).app W y) =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheafOf X.sheaf).obj)).unit.app
        P).app (f.opensFunctor.op.obj W) y := by
  have h := ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (ringCatSheafOf Y.sheaf).obj)).homEquiv_unit _ _ (sheafificationRestrictHom f P)).symm.trans
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 (ringCatSheafOf Y.sheaf).obj)).homEquiv _ _).apply_symm_apply _)
  exact congrArg (fun k => (k.app W).hom y) h

theorem inv_sheafificationRestrictHom_unit 
    (P : PresheafOfModules.{u} (ringCatSheafOf X.sheaf).obj)
    (W : (Opens Y)ᵒᵖ) (y : P.obj (f.opensFunctor.op.obj W)) :
    (inv (sheafificationRestrictHom f P)).val.app W
        (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheafOf X.sheaf).obj)).unit.app
          P).app (f.opensFunctor.op.obj W) y) =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheafOf Y.sheaf).obj)).unit.app
        ((PresheafOfModules.pushforward (restrictRingHom f).hom).obj P)).app W y := by
  rw [← sheafificationRestrictHom_unit]
  exact congrArg (fun k => (k.val.app W).hom
    (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheafOf Y.sheaf).obj)).unit.app
      ((PresheafOfModules.pushforward (restrictRingHom f).hom).obj P)).app W y))
    (IsIso.hom_inv_id (sheafificationRestrictHom f P))

variable (F : SheafOfModules.{u} (ringCatSheafOf X.sheaf)) (r : ℕ)

/-- Sections of the restriction `F|_Y` over `W` are the sections of `F` over `f(W)`; this is the
identity map, semilinear over `restrictRing`. -/
noncomputable def restrictSections (W : (Opens Y)ᵒᵖ) :
    ((restrictModule f).obj F).val.obj W →ₛₗ[restrictRing f W]
      F.val.obj (f.opensFunctor.op.obj W) where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The inverse of `restrictSections`, semilinear over `restrictRingInv`. -/
noncomputable def restrictSectionsInv (W : (Opens Y)ᵒᵖ) :
    F.val.obj (f.opensFunctor.op.obj W) →ₛₗ[restrictRingInv f W]
      ((restrictModule f).obj F).val.obj W where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' b x := by
    change b • x = restrictRing f W (restrictRingInv f W b) • x
    rw [restrictRing_restrictRingInv]

/-- Restriction `(F|_Y)(W) → F(f(W'))` for `W' ⊆ W`, semilinear over the composite ring map. -/
noncomputable def restrictSectionsMap {W W' : (Opens Y)ᵒᵖ} (i : W ⟶ W') :
    ((restrictModule f).obj F).val.obj W →ₛₗ[(restrictRing f W').comp
      ((Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat).map i).hom]
      F.val.obj (f.opensFunctor.op.obj W') where
  toFun x := restrictSections f F W' (((restrictModule f).obj F).val.restrictₛₗ i x)
  map_add' x y := by rw [map_add, map_add]
  map_smul' a x := by rw [map_smulₛₗ, map_smulₛₗ]; rfl

/-- Sections over `W` of the presheaf `W ↦ ⨂^r (F|_Y)(W)` agree with sections over `f(W)` of
the presheaf `U ↦ ⨂^r F(U)`. -/
noncomputable def tensorPowerRestrictEquiv (W : (Opens Y)ᵒᵖ) :
    (moduleSheafTensorPowerPresheaf r ((restrictModule f).obj F)).obj W ≃ₗ[
      (ringCatSheafOf Y.sheaf).obj.obj W]
      ((PresheafOfModules.pushforward (restrictRingHom f).hom).obj
        (moduleSheafTensorPowerPresheaf r F)).obj W where
  toFun := tensorPowerMap r (restrictRing f W) (restrictSections f F W)
  map_add' := map_add _
  map_smul' := (tensorPowerMap r (restrictRing f W) (restrictSections f F W)).map_smulₛₗ
  invFun := tensorPowerMap r (restrictRingInv f W) (restrictSectionsInv f F W)
  left_inv x := (tensorPowerMap_comp r (fun a => (restrictRingInv_restrictRing f W a).symm)
    _ _ LinearMap.id (fun _ => rfl) x).symm.trans
      (tensorPowerMap_id r (fun _ => rfl) _ (fun _ => rfl) x)
  right_inv x := (tensorPowerMap_comp r (fun b => (restrictRing_restrictRingInv f W b).symm)
    _ _ LinearMap.id (fun _ => rfl) x).symm.trans
      (tensorPowerMap_id r (fun _ => rfl) _ (fun _ => rfl) x)

/-- The presheaf `W ↦ ⨂^r (F|_Y)(W)` is the restriction to `Y` of the presheaf
`U ↦ ⨂^r F(U)`. -/
noncomputable def tensorPowerPresheafRestrictIso :
    moduleSheafTensorPowerPresheaf r ((restrictModule f).obj F) ≅
      (PresheafOfModules.pushforward (restrictRingHom f).hom).obj
        (moduleSheafTensorPowerPresheaf r F) :=
  PresheafOfModules.isoMk (fun W => (tensorPowerRestrictEquiv f F r W).toModuleIso)
    (fun W W' i => by
      ext x
      exact (tensorPowerMap_comp r (fun a => rfl) (((restrictModule f).obj F).val.restrictₛₗ i)
        (restrictSections f F W') (restrictSectionsMap f F i) (fun _ => rfl) x).symm.trans
        (tensorPowerMap_comp r (fun a => restrictRing_naturality f i a) (restrictSections f F W)
          (F.val.restrictₛₗ (f.opensFunctor.op.map i)) _ (fun _ => rfl) x))

/-- Sections over `W` of the presheaf `W ↦ Sym^r (F|_Y)(W)` agree with sections over `f(W)` of
the presheaf `U ↦ Sym^r F(U)`. -/
noncomputable def symmetricPowerRestrictEquiv (W : (Opens Y)ᵒᵖ) :
    (moduleSheafSymmetricPowerPresheaf r ((restrictModule f).obj F)).obj W ≃ₗ[
      (ringCatSheafOf Y.sheaf).obj.obj W]
      ((PresheafOfModules.pushforward (restrictRingHom f).hom).obj
        (moduleSheafSymmetricPowerPresheaf r F)).obj W where
  toFun := symmetricPowerMap r (restrictRing f W) (restrictSections f F W)
  map_add' := map_add _
  map_smul' := (symmetricPowerMap r (restrictRing f W) (restrictSections f F W)).map_smulₛₗ
  invFun := symmetricPowerMap r (restrictRingInv f W) (restrictSectionsInv f F W)
  left_inv x := (symmetricPowerMap_comp r (fun a => (restrictRingInv_restrictRing f W a).symm)
    _ _ LinearMap.id (fun _ => rfl) x).symm.trans
      (symmetricPowerMap_id r (fun _ => rfl) _ (fun _ => rfl) x)
  right_inv x := (symmetricPowerMap_comp r (fun b => (restrictRing_restrictRingInv f W b).symm)
    _ _ LinearMap.id (fun _ => rfl) x).symm.trans
      (symmetricPowerMap_id r (fun _ => rfl) _ (fun _ => rfl) x)

/-- The presheaf `W ↦ Sym^r (F|_Y)(W)` is the restriction to `Y` of the presheaf
`U ↦ Sym^r F(U)`. -/
noncomputable def symmetricPowerPresheafRestrictIso :
    moduleSheafSymmetricPowerPresheaf r ((restrictModule f).obj F) ≅
      (PresheafOfModules.pushforward (restrictRingHom f).hom).obj
        (moduleSheafSymmetricPowerPresheaf r F) :=
  PresheafOfModules.isoMk (fun W => (symmetricPowerRestrictEquiv f F r W).toModuleIso)
    (fun W W' i => by
      ext x
      exact (symmetricPowerMap_comp r (fun a => rfl) (((restrictModule f).obj F).val.restrictₛₗ i)
        (restrictSections f F W') (restrictSectionsMap f F i) (fun _ => rfl) x).symm.trans
        (symmetricPowerMap_comp r (fun a => restrictRing_naturality f i a) (restrictSections f F W)
          (F.val.restrictₛₗ (f.opensFunctor.op.map i)) _ (fun _ => rfl) x))

/-- Sections over `W` of the presheaf `W ↦ ⋀^r (F|_Y)(W)` agree with sections over `f(W)` of
the presheaf `U ↦ ⋀^r F(U)`. -/
noncomputable def exteriorPowerRestrictEquiv (W : (Opens Y)ᵒᵖ) :
    (moduleSheafExteriorPowerPresheaf r ((restrictModule f).obj F)).obj W ≃ₗ[
      (ringCatSheafOf Y.sheaf).obj.obj W]
      ((PresheafOfModules.pushforward (restrictRingHom f).hom).obj
        (moduleSheafExteriorPowerPresheaf r F)).obj W where
  toFun := exteriorPowerMap r (restrictRing f W) (restrictSections f F W)
  map_add' := map_add _
  map_smul' := (exteriorPowerMap r (restrictRing f W) (restrictSections f F W)).map_smulₛₗ
  invFun := exteriorPowerMap r (restrictRingInv f W) (restrictSectionsInv f F W)
  left_inv x := (exteriorPowerMap_comp r (fun a => (restrictRingInv_restrictRing f W a).symm)
    _ _ LinearMap.id (fun _ => rfl) x).symm.trans
      (exteriorPowerMap_id r (fun _ => rfl) _ (fun _ => rfl) x)
  right_inv x := (exteriorPowerMap_comp r (fun b => (restrictRing_restrictRingInv f W b).symm)
    _ _ LinearMap.id (fun _ => rfl) x).symm.trans
      (exteriorPowerMap_id r (fun _ => rfl) _ (fun _ => rfl) x)

/-- The presheaf `W ↦ ⋀^r (F|_Y)(W)` is the restriction to `Y` of the presheaf
`U ↦ ⋀^r F(U)`. -/
noncomputable def exteriorPowerPresheafRestrictIso :
    moduleSheafExteriorPowerPresheaf r ((restrictModule f).obj F) ≅
      (PresheafOfModules.pushforward (restrictRingHom f).hom).obj
        (moduleSheafExteriorPowerPresheaf r F) :=
  PresheafOfModules.isoMk (fun W => (exteriorPowerRestrictEquiv f F r W).toModuleIso)
    (fun W W' i => by
      ext x
      exact (exteriorPowerMap_comp r (fun a => rfl) (((restrictModule f).obj F).val.restrictₛₗ i)
        (restrictSections f F W') (restrictSectionsMap f F i) (fun _ => rfl) x).symm.trans
        (exteriorPowerMap_comp r (fun a => restrictRing_naturality f i a) (restrictSections f F W)
          (F.val.restrictₛₗ (f.opensFunctor.op.map i)) _ (fun _ => rfl) x))

end SheafTensorOperations

variable (F : SheafOfModules.{u} (ringCatSheafOf X.sheaf)) (r : ℕ)

/-- **Tensor powers restrict compatibly to open subschemes.** For an open immersion
`f : Y ⟶ X`, the restriction of `T^r F` to `Y` is `T^r (F|_Y)`. -/
noncomputable def moduleSheafTensorPowerRestrictIso :
    (restrictModule f).obj (moduleSheafTensorPower r F) ≅
      moduleSheafTensorPower r ((restrictModule f).obj F) :=
  (asIso (sheafificationRestrictHom f (moduleSheafTensorPowerPresheaf r F))).symm ≪≫
    (PresheafOfModules.sheafification (𝟙 (ringCatSheafOf Y.sheaf).obj)).mapIso
      (tensorPowerPresheafRestrictIso f F r).symm

/-- The isomorphism `moduleSheafTensorPowerRestrictIso` is compatible with the universal maps: it
sends `f₁ ⊗ ⋯ ⊗ fᵣ` formed from sections over `f(W)` to the same expression over `W`. -/
theorem moduleSheafTensorPowerRestrictIso_multilinear (W : (Opens Y)ᵒᵖ)
    (m : Fin r → F.val.obj (f.opensFunctor.op.obj W)) :
    (moduleSheafTensorPowerRestrictIso f F r).hom.val.app W
        ((moduleSheafTensorPowerMultilinear r F).app (f.opensFunctor.op.obj W) m) =
      (moduleSheafTensorPowerMultilinear r ((restrictModule f).obj F)).app W m := by
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheafOf Y.sheaf).obj)).unit
  let m' : Fin r → ((restrictModule f).obj F).val.obj W := m
  let e := (tensorPowerPresheafRestrictIso f F r).inv
  let x : (moduleSheafTensorPowerPresheaf r F).obj (f.opensFunctor.op.obj W) :=
    PiTensorProduct.tprod _ m
  have h1 := inv_sheafificationRestrictHom_unit f (moduleSheafTensorPowerPresheaf r F) W x
  have h2 : (η.app (moduleSheafTensorPowerPresheaf r ((restrictModule f).obj F))).app W
        (e.app W x) =
      ((PresheafOfModules.sheafification (𝟙 (ringCatSheafOf Y.sheaf).obj)).map e).val.app W
        ((η.app ((PresheafOfModules.pushforward (restrictRingHom f).hom).obj
          (moduleSheafTensorPowerPresheaf r F))).app W x) :=
    congrArg (fun k => (k.app W).hom x) (η.naturality e)
  have h3 : e.app W x = PiTensorProduct.tprod _ m' := tensorPowerMap_tprod r _ _ m
  rw [h3] at h2
  exact (congrArg _ h1).trans h2.symm

/-- **Symmetric powers restrict compatibly to open subschemes.** For an open immersion
`f : Y ⟶ X`, the restriction of `S^r F` to `Y` is `S^r (F|_Y)`. -/
noncomputable def moduleSheafSymmetricPowerRestrictIso :
    (restrictModule f).obj (moduleSheafSymmetricPower r F) ≅
      moduleSheafSymmetricPower r ((restrictModule f).obj F) :=
  (asIso (sheafificationRestrictHom f (moduleSheafSymmetricPowerPresheaf r F))).symm ≪≫
    (PresheafOfModules.sheafification (𝟙 (ringCatSheafOf Y.sheaf).obj)).mapIso
      (symmetricPowerPresheafRestrictIso f F r).symm

/-- The isomorphism `moduleSheafSymmetricPowerRestrictIso` is compatible with the universal maps: it
sends the symmetric product `f₁ ⋯ fᵣ` formed from sections over `f(W)` to the same expression
over `W`. -/
theorem moduleSheafSymmetricPowerRestrictIso_multilinear (W : (Opens Y)ᵒᵖ)
    (m : Fin r → F.val.obj (f.opensFunctor.op.obj W)) :
    (moduleSheafSymmetricPowerRestrictIso f F r).hom.val.app W
        ((moduleSheafSymmetricPowerMultilinear r F).app (f.opensFunctor.op.obj W) m) =
      (moduleSheafSymmetricPowerMultilinear r ((restrictModule f).obj F)).app W m := by
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheafOf Y.sheaf).obj)).unit
  let m' : Fin r → ((restrictModule f).obj F).val.obj W := m
  let e := (symmetricPowerPresheafRestrictIso f F r).inv
  let x : (moduleSheafSymmetricPowerPresheaf r F).obj (f.opensFunctor.op.obj W) :=
    symmetricPowerTprod _ (F.val.obj (f.opensFunctor.op.obj W)) r m
  have h1 := inv_sheafificationRestrictHom_unit f (moduleSheafSymmetricPowerPresheaf r F) W x
  have h2 : (η.app (moduleSheafSymmetricPowerPresheaf r ((restrictModule f).obj F))).app W
        (e.app W x) =
      ((PresheafOfModules.sheafification (𝟙 (ringCatSheafOf Y.sheaf).obj)).map e).val.app W
        ((η.app ((PresheafOfModules.pushforward (restrictRingHom f).hom).obj
          (moduleSheafSymmetricPowerPresheaf r F))).app W x) :=
    congrArg (fun k => (k.app W).hom x) (η.naturality e)
  have h3 : e.app W x = symmetricPowerTprod _ (((restrictModule f).obj F).val.obj W) r m' :=
    symmetricPowerMap_tprod r _ _ m
  rw [h3] at h2
  exact (congrArg _ h1).trans h2.symm

/-- **Exterior powers restrict compatibly to open subschemes.** For an open immersion
`f : Y ⟶ X`, the restriction of `⋀^r F` to `Y` is `⋀^r (F|_Y)`. -/
noncomputable def moduleSheafExteriorPowerRestrictIso :
    (restrictModule f).obj (moduleSheafExteriorPower r F) ≅
      moduleSheafExteriorPower r ((restrictModule f).obj F) :=
  (asIso (sheafificationRestrictHom f (moduleSheafExteriorPowerPresheaf r F))).symm ≪≫
    (PresheafOfModules.sheafification (𝟙 (ringCatSheafOf Y.sheaf).obj)).mapIso
      (exteriorPowerPresheafRestrictIso f F r).symm

/-- The isomorphism `moduleSheafExteriorPowerRestrictIso` is compatible with the universal maps: it
sends `f₁ ∧ ⋯ ∧ fᵣ` formed from sections over `f(W)` to the same expression over `W`. -/
theorem moduleSheafExteriorPowerRestrictIso_multilinear (W : (Opens Y)ᵒᵖ)
    (m : Fin r → F.val.obj (f.opensFunctor.op.obj W)) :
    (moduleSheafExteriorPowerRestrictIso f F r).hom.val.app W
        ((moduleSheafExteriorPowerMultilinear r F).app (f.opensFunctor.op.obj W) m) =
      (moduleSheafExteriorPowerMultilinear r ((restrictModule f).obj F)).app W m := by
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheafOf Y.sheaf).obj)).unit
  let m' : Fin r → ((restrictModule f).obj F).val.obj W := m
  let e := (exteriorPowerPresheafRestrictIso f F r).inv
  let x : (moduleSheafExteriorPowerPresheaf r F).obj (f.opensFunctor.op.obj W) :=
    exteriorPower.ιMulti _ r m
  have h1 := inv_sheafificationRestrictHom_unit f (moduleSheafExteriorPowerPresheaf r F) W x
  have h2 : (η.app (moduleSheafExteriorPowerPresheaf r ((restrictModule f).obj F))).app W
        (e.app W x) =
      ((PresheafOfModules.sheafification (𝟙 (ringCatSheafOf Y.sheaf).obj)).map e).val.app W
        ((η.app ((PresheafOfModules.pushforward (restrictRingHom f).hom).obj
          (moduleSheafExteriorPowerPresheaf r F))).app W x) :=
    congrArg (fun k => (k.app W).hom x) (η.naturality e)
  have h3 : e.app W x = exteriorPower.ιMulti _ r m' := exteriorPowerMap_ιMulti r _ _ m
  rw [h3] at h2
  exact (congrArg _ h1).trans h2.symm

end Restriction

end Hartshorne

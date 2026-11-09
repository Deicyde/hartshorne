/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Flat.Localization

/-!
# Local rings of a fibre product

Hartshorne, *Algebraic Geometry*, II, Theorem 3.3 (construction of fibre products, pp. 87–88):
the local computation on an affine open `Spec (A ⊗_R B)` of `X ×_Y Y'`.

Let `f : X ⟶ Y` and `g : Y' ⟶ Y` be morphisms of schemes, `x'` a point of `X' = X ×_Y Y'`, and
`x`, `y'`, `y` its images in `X`, `Y'`, `Y`. The stalk maps of the two projections agree on
`𝒪_{Y,y}`, so they induce a ring homomorphism
`Hartshorne.FiberProductStalk.tensorToStalk f g x' : 𝒪_{X,x} ⊗[𝒪_{Y,y}] 𝒪_{Y',y'} →+* 𝒪_{X',x'}`.

* `Hartshorne.FiberProductStalk.isLocalizationMap_tensorToStalk`: this homomorphism is a
  localization at the prime ideal lying under the maximal ideal of `𝒪_{X',x'}`;
* `Hartshorne.FiberProductStalk.flat_tensorToStalk`: hence `𝒪_{X',x'}` is flat over the tensor
  product.

The proof chooses affine opens `W = Spec R ∋ y`, `V = Spec A ∋ x` over `W` and
`V' = Spec B ∋ y'` over `W`. Then `Spec (A ⊗_R B)` is an open subscheme of `X'` through `x'`, so
`𝒪_{X',x'}` is a localization of `A ⊗_R B`, and every element of the tensor product of stalks is a
fraction whose numerator and denominator come from `A ⊗_R B`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Opposite

namespace Hartshorne

universe u

namespace FiberProductStalk

section Algebra

/-- A localization map into a local ring is also a localization at the prime ideal lying under
the maximal ideal. -/
theorem isLocalizationMap_comap_maximalIdeal_of_isLocalizationMap {C S : Type*} [CommRing C]
    [CommRing S] [IsLocalRing S] (ψ : C →+* S) (M : Submonoid C) (hM : M.IsLocalizationMap ψ) :
    ((IsLocalRing.maximalIdeal S).comap ψ).primeCompl.IsLocalizationMap ψ where
  map_units y := by
    have := y.2
    simpa [Ideal.primeCompl, IsLocalRing.mem_maximalIdeal] using this
  surj z := by
    obtain ⟨⟨c, u⟩, h⟩ := hM.surj z
    refine ⟨⟨c, ⟨u, ?_⟩⟩, h⟩
    simpa [Ideal.primeCompl, IsLocalRing.mem_maximalIdeal] using hM.map_units u
  exists_of_eq {x y} hxy := by
    obtain ⟨⟨m, hm⟩, h⟩ := hM.exists_of_eq hxy
    refine ⟨⟨m, ?_⟩, h⟩
    simpa [Ideal.primeCompl, IsLocalRing.mem_maximalIdeal] using hM.map_units ⟨m, hm⟩

/-- If every element of `T` is a fraction `ι(c) / ι(u)` of elements in the image of a ring map
`ι : C → T`, and `φ ∘ ι` is a localization map into a local ring, then `φ` is a localization at
the prime ideal lying under the maximal ideal. -/
theorem isLocalizationMap_comap_maximalIdeal_of_comp {C T S : Type*} [CommRing C] [CommRing T]
    [CommRing S] [IsLocalRing S] (ι : C →+* T) (φ : T →+* S)
    (hι : ∀ t : T, ∃ c u : C, IsUnit (ι u) ∧ t * ι u = ι c)
    (hψ : ((IsLocalRing.maximalIdeal S).comap (φ.comp ι)).primeCompl.IsLocalizationMap
      (φ.comp ι)) :
    ((IsLocalRing.maximalIdeal S).comap φ).primeCompl.IsLocalizationMap φ where
  map_units y := by
    have := y.2
    simpa [Ideal.primeCompl, IsLocalRing.mem_maximalIdeal] using this
  surj z := by
    obtain ⟨⟨c, u⟩, h⟩ := hψ.surj z
    exact ⟨⟨ι c, ⟨ι u, u.2⟩⟩, h⟩
  exists_of_eq {x y} hxy := by
    obtain ⟨c, u, hu, hc⟩ := hι (x - y)
    have h0 : (φ.comp ι) c = (φ.comp ι) 0 := by
      simp [← hc, map_sub, hxy]
    obtain ⟨⟨m, hm⟩, hm0⟩ := hψ.exists_of_eq h0
    refine ⟨⟨ι m, hm⟩, ?_⟩
    have h1 : ι m * ι c = 0 := by rw [← map_mul, hm0, mul_zero, map_zero]
    rw [← hc] at h1
    have h2 : ι m * (x - y) = 0 := hu.mul_left_eq_zero.1 (by rw [← h1]; ring)
    change ι m * x = ι m * y
    simpa [mul_sub, sub_eq_zero] using h2

/-- In a tensor product `Sx ⊗[Sy] Sy'`, if every pure tensor is a fraction `ι(c) / ι(u)` with
`ι(u)` a unit, then so is every element. -/
theorem exists_mul_eq_of_tmul {Sy Sx Sy' C : Type*} [CommRing Sy] [CommRing Sx] [CommRing Sy']
    [Algebra Sy Sx] [Algebra Sy Sy'] [CommRing C] (ι : C →+* Sx ⊗[Sy] Sy')
    (h : ∀ (α : Sx) (β : Sy'), ∃ c u : C, IsUnit (ι u) ∧ α ⊗ₜ[Sy] β * ι u = ι c)
    (t : Sx ⊗[Sy] Sy') : ∃ c u : C, IsUnit (ι u) ∧ t * ι u = ι c := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, 1, by simp, by simp⟩
  | tmul α β => exact h α β
  | add t₁ t₂ h₁ h₂ =>
    obtain ⟨c₁, u₁, hu₁, e₁⟩ := h₁
    obtain ⟨c₂, u₂, hu₂, e₂⟩ := h₂
    refine ⟨c₁ * u₂ + c₂ * u₁, u₁ * u₂, by rw [map_mul]; exact hu₁.mul hu₂, ?_⟩
    rw [map_add, map_mul, map_mul, map_mul, ← e₁, ← e₂]
    ring

theorem algebraMap_tmul_one_eq {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (c : R) :
    algebraMap R A c ⊗ₜ[R] (1 : B) = 1 ⊗ₜ algebraMap R B c := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem tmul_one_mul_one_tmul {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (a : A) (b : B) : (a ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ b) = a ⊗ₜ b := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem tmul_mul_tmul' {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (a a' : A) (b b' : B) :
    (a ⊗ₜ[R] b) * (a' ⊗ₜ b') = (a * a') ⊗ₜ (b * b') :=
  Algebra.TensorProduct.tmul_mul_tmul _ _ _ _

theorem isUnit_tmul {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] {a : A} {b : B} (ha : IsUnit a) (hb : IsUnit b) :
    IsUnit (a ⊗ₜ[R] b) := by
  rw [← tmul_one_mul_one_tmul]
  exact (ha.map Algebra.TensorProduct.includeLeftRingHom).mul
    (hb.map Algebra.TensorProduct.includeRight)

theorem tmul_one_eq_algebraMap {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (c : R) (a : A) (h : a = algebraMap R A c) :
    a ⊗ₜ[R] (1 : B) = algebraMap R (A ⊗[R] B) c := by
  rw [h, Algebra.TensorProduct.algebraMap_apply]

theorem one_tmul_eq_algebraMap {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (c : R) (b : B) (h : b = algebraMap R B c) :
    (1 : A) ⊗ₜ[R] b = algebraMap R (A ⊗[R] B) c := by
  rw [h, Algebra.TensorProduct.algebraMap_apply, algebraMap_tmul_one_eq]

theorem ringHom_tmul_of_left_right {R A B K : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [CommRing K] (κ₁ κ₂ : A ⊗[R] B →+* K) (a : A) (b : B)
    (hL : κ₁ (a ⊗ₜ 1) = κ₂ (a ⊗ₜ 1)) (hR : κ₁ (1 ⊗ₜ b) = κ₂ (1 ⊗ₜ b)) :
    κ₁ (a ⊗ₜ b) = κ₂ (a ⊗ₜ b) := by
  rw [← tmul_one_mul_one_tmul, map_mul, map_mul, hL, hR]

end Algebra

section Points

variable {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (x' : ↑(pullback f g))

lemma base_eq : f (pullback.fst f g x') = g (pullback.snd f g x') := by
  rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]

/-- The `𝒪_{Y,y}`-algebra structure on `𝒪_{X,x}` given by the stalk map of `f`. -/
noncomputable abbrev algebraLeft :
    Algebra (Y.presheaf.stalk (f (pullback.fst f g x')))
      (X.presheaf.stalk (pullback.fst f g x')) :=
  (f.stalkMap _).hom.toAlgebra

/-- The `𝒪_{Y,y}`-algebra structure on `𝒪_{Y',y'}` given by the stalk map of `g`. -/
noncomputable abbrev algebraRight :
    Algebra (Y.presheaf.stalk (f (pullback.fst f g x')))
      (Y'.presheaf.stalk (pullback.snd f g x')) :=
  ((Y.presheaf.stalkCongr (.of_eq (base_eq f g x'))).hom ≫ g.stalkMap _).hom.toAlgebra

lemma stalkMap_compat (r : Y.presheaf.stalk (f (pullback.fst f g x'))) :
    (pullback.snd f g).stalkMap x'
        (g.stalkMap _ ((Y.presheaf.stalkCongr (.of_eq (base_eq f g x'))).hom r)) =
      (pullback.fst f g).stalkMap x' (f.stalkMap _ r) := by
  have h := Scheme.Hom.stalkMap_congr_hom _ _ (pullback.condition (f := f) (g := g)) x'
  rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at h
  exact (congrArg (fun φ => φ.hom r) h).symm

/-- The ring homomorphism `𝒪_{X,x} ⊗[𝒪_{Y,y}] 𝒪_{Y',y'} → 𝒪_{X',x'}` induced by the stalk maps
of the two projections of the fibre product `X' = X ×_Y Y'`. -/
noncomputable def tensorToStalk :
    letI := algebraLeft f g x'
    letI := algebraRight f g x'
    X.presheaf.stalk (pullback.fst f g x') ⊗[Y.presheaf.stalk (f (pullback.fst f g x'))]
      Y'.presheaf.stalk (pullback.snd f g x') →+* (pullback f g).presheaf.stalk x' :=
  letI := algebraLeft f g x'
  letI := algebraRight f g x'
  letI : Algebra (Y.presheaf.stalk (f (pullback.fst f g x')))
      ((pullback f g).presheaf.stalk x') :=
    (f.stalkMap _ ≫ (pullback.fst f g).stalkMap x').hom.toAlgebra
  let fA : X.presheaf.stalk (pullback.fst f g x') →ₐ[Y.presheaf.stalk (f (pullback.fst f g x'))]
      (pullback f g).presheaf.stalk x' :=
    { toRingHom := ((pullback.fst f g).stalkMap x').hom, commutes' := fun _ => rfl }
  let fB : Y'.presheaf.stalk (pullback.snd f g x') →ₐ[Y.presheaf.stalk (f (pullback.fst f g x'))]
      (pullback f g).presheaf.stalk x' :=
    { toRingHom := ((pullback.snd f g).stalkMap x').hom
      commutes' := fun r => stalkMap_compat f g x' r }
  (Algebra.TensorProduct.lift fA fB (fun _ _ => Commute.all _ _)).toRingHom

lemma tensorToStalk_tmul (α : X.presheaf.stalk (pullback.fst f g x'))
    (β : Y'.presheaf.stalk (pullback.snd f g x')) :
    letI := algebraLeft f g x'
    letI := algebraRight f g x'
    tensorToStalk f g x' (α ⊗ₜ β) =
      (pullback.fst f g).stalkMap x' α * (pullback.snd f g).stalkMap x' β := by
  simp only [tensorToStalk, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.lift_tmul]
  rfl

end Points

section Affine

variable {X : Scheme.{u}}

lemma germ_appLE {Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} {V : X.Opens} (e : V ≤ f ⁻¹ᵁ U)
    (x : X) (hx : x ∈ V) (r : Γ(Y, U)) :
    X.presheaf.germ V x hx (f.appLE U V e r) = f.stalkMap x (Y.presheaf.germ U (f x) (e hx) r) := by
  erw [Scheme.Hom.germ_stalkMap_apply]
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply]
  erw [TopCat.Presheaf.germ_res_apply]

lemma stalkCongr_hom_germ {x y : X} (h : x = y) (U : X.Opens) (hx : x ∈ U) (hy : y ∈ U)
    (r : Γ(X, U)) :
    (X.presheaf.stalkCongr (.of_eq h)).hom (X.presheaf.germ U x hx r) =
      X.presheaf.germ U y hy r := by
  subst h
  simp

lemma germ_stalkMap_congr {T : Scheme.{u}} {k₁ k₂ : T ⟶ X} (e : k₁ = k₂) (z : T) (U : X.Opens)
    (h₁ : k₁ z ∈ U) (h₂ : k₂ z ∈ U) :
    X.presheaf.germ U _ h₁ ≫ k₁.stalkMap z = X.presheaf.germ U _ h₂ ≫ k₂.stalkMap z := by
  subst e
  rfl

lemma fromSpec_stalkMap_germ {V : X.Opens} (hV : IsAffineOpen V) (w : Spec Γ(X, V))
    (hw : hV.fromSpec w ∈ V) (a : Γ(X, V)) :
    hV.fromSpec.stalkMap w (X.presheaf.germ V _ hw a) =
      (Spec Γ(X, V)).presheaf.germ ⊤ w trivial ((Scheme.ΓSpecIso Γ(X, V)).inv a) := by
  erw [Scheme.Hom.germ_stalkMap_apply]
  rw [hV.fromSpec_app_self_apply]
  erw [TopCat.Presheaf.germ_res_apply]

lemma fromSpec_stalkMap_germ_hom {V : X.Opens} (hV : IsAffineOpen V) (w : Spec Γ(X, V))
    (hw : hV.fromSpec w ∈ V) :
    X.presheaf.germ V _ hw ≫ hV.fromSpec.stalkMap w =
      (Scheme.ΓSpecIso Γ(X, V)).inv ≫ (Spec Γ(X, V)).presheaf.germ ⊤ w trivial := by
  ext a
  exact fromSpec_stalkMap_germ hV w hw a

lemma SpecMap_stalkMap_germ_top {R S : CommRingCat.{u}} (φ : R ⟶ S) (z : Spec S) (a : R) :
    (Spec.map φ).stalkMap z
        ((Spec R).presheaf.germ ⊤ (Spec.map φ z) trivial ((Scheme.ΓSpecIso R).inv a)) =
      (Spec S).presheaf.germ ⊤ z trivial ((Scheme.ΓSpecIso S).inv (φ a)) := by
  erw [Scheme.Hom.germ_stalkMap_apply]
  have := congrArg (fun h => h.hom a) (Scheme.ΓSpecIso_inv_naturality φ)
  simp only [CommRingCat.comp_apply] at this
  rw [this]
  rfl

lemma SpecMap_stalkMap_germ_top_hom {R S : CommRingCat.{u}} (φ : R ⟶ S) (z : Spec S) :
    (Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ (Spec.map φ z) trivial ≫
        (Spec.map φ).stalkMap z =
      φ ≫ (Scheme.ΓSpecIso S).inv ≫ (Spec S).presheaf.germ ⊤ z trivial := by
  ext a
  exact SpecMap_stalkMap_germ_top φ z a

/-- If `G : Spec S ⟶ Z` followed by `h : Z ⟶ X` is `Spec.map φA` followed by the inclusion of an
affine open `V = Spec Γ(X, V)`, then on germs of sections over `V` the stalk maps of `h` and `G`
compose to the germ at `z` of `φA a`. -/
lemma stalkMap_stalkMap_germ_of_comp_eq {Z : Scheme.{u}} {V : X.Opens} (hV : IsAffineOpen V)
    {S : CommRingCat.{u}} {φA : Γ(X, V) ⟶ S} {h : Z ⟶ X} {G : Spec S ⟶ Z}
    (hG : G ≫ h = Spec.map φA ≫ hV.fromSpec) (z : Spec S) (hz : h (G z) ∈ V) (a : Γ(X, V)) :
    G.stalkMap z (h.stalkMap (G z) (X.presheaf.germ V _ hz a)) =
      (Spec S).presheaf.germ ⊤ z trivial ((Scheme.ΓSpecIso S).inv (φA a)) := by
  have hz' : hV.fromSpec (Spec.map φA z) ∈ V := by
    have := hz
    rwa [← Scheme.Hom.comp_apply, hG, Scheme.Hom.comp_apply] at this
  have key : X.presheaf.germ V _ hz ≫ h.stalkMap (G z) ≫ G.stalkMap z =
      φA ≫ (Scheme.ΓSpecIso S).inv ≫ (Spec S).presheaf.germ ⊤ z trivial := by
    calc X.presheaf.germ V _ hz ≫ h.stalkMap (G z) ≫ G.stalkMap z
        = X.presheaf.germ V ((G ≫ h) z) hz ≫ (G ≫ h).stalkMap z := by
          rw [Scheme.Hom.stalkMap_comp]; rfl
      _ = X.presheaf.germ V ((Spec.map φA ≫ hV.fromSpec) z) hz' ≫
          (Spec.map φA ≫ hV.fromSpec).stalkMap z := germ_stalkMap_congr hG z V _ _
      _ = X.presheaf.germ V (hV.fromSpec (Spec.map φA z)) hz' ≫
          hV.fromSpec.stalkMap (Spec.map φA z) ≫ (Spec.map φA).stalkMap z := by
          rw [Scheme.Hom.stalkMap_comp]; rfl
      _ = _ := by
          rw [reassoc_of% (fromSpec_stalkMap_germ_hom hV _ hz'), SpecMap_stalkMap_germ_top_hom]
  exact congrArg (fun k => k.hom a) key

lemma exists_germ_frac {V : X.Opens} (hV : IsAffineOpen V) (x : X) (hx : x ∈ V)
    (α : X.presheaf.stalk x) :
    ∃ a s : Γ(X, V), IsUnit (X.presheaf.germ V x hx s) ∧
      α * X.presheaf.germ V x hx s = X.presheaf.germ V x hx a := by
  let := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have := hV.isLocalization_stalk ⟨x, hx⟩
  obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl α
  exact ⟨a, s, IsLocalization.map_units _ s, h⟩

lemma isLocalizationMap_SpecGerm (S : CommRingCat.{u}) (z : PrimeSpectrum S) :
    z.asIdeal.primeCompl.IsLocalizationMap
      ((Scheme.ΓSpecIso S).inv ≫ (Spec S).presheaf.germ ⊤ (z : Spec S) trivial).hom :=
  (@isLocalization_iff_isLocalizationMap _ _ _ _ _ (StructureSheaf.stalkAlgebra S z)).1
    (@StructureSheaf.IsLocalization.to_stalk S _ z)

end Affine

lemma ringHom_ext_tensor {R A B S : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] [CommRing S] (φ₁ φ₂ : A ⊗[R] B →+* S)
    (h : ∀ a b, φ₁ (a ⊗ₜ b) = φ₂ (a ⊗ₜ b)) : φ₁ = φ₂ := by
  refine RingHom.ext fun t => ?_
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => exact h a b
  | add t₁ t₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]

section Main

variable {X Y Y' : Scheme.{u}}

lemma germ_appLE_snd (f : X ⟶ Y) (g : Y' ⟶ Y) (x' : ↑(pullback f g)) {W : Y.Opens}
    (hyW : f (pullback.fst f g x') ∈ W) {V' : Y'.Opens} (hV'W : V' ≤ g ⁻¹ᵁ W)
    (hxV' : pullback.snd f g x' ∈ V') (r : Γ(Y, W)) :
    Y'.presheaf.germ V' _ hxV' (g.appLE W V' hV'W r) =
      @algebraMap _ _ _ _ (algebraRight f g x') (Y.presheaf.germ W _ hyW r) := by
  rw [germ_appLE g hV'W (pullback.snd f g x') hxV' r]
  change _ = g.stalkMap _ ((Y.presheaf.stalkCongr _).hom (Y.presheaf.germ W _ hyW r))
  rw [stalkCongr_hom_germ (base_eq f g x') W hyW (hV'W hxV')]

set_option maxHeartbeats 400000 in
-- The stalk and tensor-product types here make instance unification slow.
/-- The local computation behind `isLocalizationMap_tensorToStalk`, at a point `G z` of the open
subscheme `G : Spec (A ⊗_R B) ⟶ X ×_Y Y'` built from affine opens `W = Spec R` of `Y`,
`V = Spec A` of `X` over `W` and `V' = Spec B` of `Y'` over `W`. -/
lemma isLocalizationMap_tensorToStalk_aux (f : X ⟶ Y) (g : Y' ⟶ Y) {W : Y.Opens}
    {V : X.Opens} {V' : Y'.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    (hVW : V ≤ f ⁻¹ᵁ W) (hV'W : V' ≤ g ⁻¹ᵁ W) :
    letI : Algebra Γ(Y, W) Γ(X, V) := (f.appLE W V hVW).hom.toAlgebra
    letI : Algebra Γ(Y, W) Γ(Y', V') := (g.appLE W V' hV'W).hom.toAlgebra
    ∀ (G : Spec (.of (Γ(X, V) ⊗[Γ(Y, W)] Γ(Y', V'))) ⟶ pullback f g) [IsOpenImmersion G],
      G ≫ pullback.fst f g =
        Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫ hV.fromSpec →
      G ≫ pullback.snd f g =
        Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) ≫
          hV'.fromSpec →
      ∀ z, pullback.fst f g (G z) ∈ V → pullback.snd f g (G z) ∈ V' →
        f (pullback.fst f g (G z)) ∈ W →
        ((IsLocalRing.maximalIdeal _).comap (tensorToStalk f g (G z))).primeCompl.IsLocalizationMap
          (tensorToStalk f g (G z)) := by
  let : Algebra Γ(Y, W) Γ(X, V) := (f.appLE W V hVW).hom.toAlgebra
  let : Algebra Γ(Y, W) Γ(Y', V') := (g.appLE W V' hV'W).hom.toAlgebra
  intro G _ hGp hGq z hxV hxV' hyW
  choose aA sA hsA haA using exists_germ_frac hV (pullback.fst f g (G z)) hxV
  choose aB sB hsB haB using exists_germ_frac hV' (pullback.snd f g (G z)) hxV'
  set C := Γ(X, V) ⊗[Γ(Y, W)] Γ(Y', V')
  let := algebraLeft f g (G z)
  let := algebraRight f g (G z)
  let : Algebra Γ(Y, W) (X.presheaf.stalk (pullback.fst f g (G z)) ⊗[Y.presheaf.stalk
      (f (pullback.fst f g (G z)))] Y'.presheaf.stalk (pullback.snd f g (G z))) :=
    ((algebraMap _ _).comp (Y.presheaf.germ W _ hyW).hom).toAlgebra
  let iA : Γ(X, V) →ₐ[Γ(Y, W)] (X.presheaf.stalk (pullback.fst f g (G z)) ⊗[Y.presheaf.stalk
      (f (pullback.fst f g (G z)))] Y'.presheaf.stalk (pullback.snd f g (G z))) :=
    { toRingHom := Algebra.TensorProduct.includeLeftRingHom.comp (X.presheaf.germ V _ hxV).hom
      commutes' := fun r => by
        change X.presheaf.germ V _ hxV (f.appLE W V hVW r) ⊗ₜ[Y.presheaf.stalk
            (f (pullback.fst f g (G z)))] 1 =
          algebraMap _ _ (Y.presheaf.germ W _ hyW r)
        exact tmul_one_eq_algebraMap _ _ (germ_appLE f hVW _ hxV r) }
  have hB1 : V' ≤ g ⁻¹ᵁ W := hV'W
  have hB2 : pullback.snd f g (G z) ∈ V' := hxV'
  have hB3 : f (pullback.fst f g (G z)) ∈ W := hyW
  have keyB := germ_appLE_snd f g (G z) hB3 hB1 hB2
  let iB : Γ(Y', V') →ₐ[Γ(Y, W)] (X.presheaf.stalk (pullback.fst f g (G z)) ⊗[Y.presheaf.stalk
      (f (pullback.fst f g (G z)))] Y'.presheaf.stalk (pullback.snd f g (G z))) :=
    { toRingHom := Algebra.TensorProduct.includeRight.toRingHom.comp
        (Y'.presheaf.germ V' _ hxV').hom
      commutes' := fun r => by
        change (1 : X.presheaf.stalk (pullback.fst f g (G z))) ⊗ₜ[Y.presheaf.stalk
            (f (pullback.fst f g (G z)))] Y'.presheaf.germ V' _ hxV' (g.appLE W V' hV'W r) =
          algebraMap _ _ (Y.presheaf.germ W _ hyW r)
        exact one_tmul_eq_algebraMap _ _ (keyB r) }
  let ι : C →+* _ := (Algebra.TensorProduct.lift iA iB (fun _ _ => Commute.all _ _)).toRingHom
  have hι : ∀ a b, ι (a ⊗ₜ[Γ(Y, W)] b) =
      X.presheaf.germ V _ hxV a ⊗ₜ[Y.presheaf.stalk (f (pullback.fst f g (G z)))]
        Y'.presheaf.germ V' _ hxV' b := by
    intro a b
    exact (Algebra.TensorProduct.lift_tmul iA iB _ a b).trans (tmul_one_mul_one_tmul _ _)
  refine isLocalizationMap_comap_maximalIdeal_of_comp ι (tensorToStalk f g (G z)) ?_ ?_
  · have hgen : ∀ (α : X.presheaf.stalk (pullback.fst f g (G z)))
        (β : Y'.presheaf.stalk (pullback.snd f g (G z))), ∃ c u : C, IsUnit (ι u) ∧
          α ⊗ₜ[Y.presheaf.stalk (f (pullback.fst f g (G z)))] β * ι u = ι c := by
      intro α β
      refine ⟨aA α ⊗ₜ aB β, sA α ⊗ₜ sB β, ?_, ?_⟩
      · exact (congrArg IsUnit (hι _ _)).mpr (isUnit_tmul (hsA α) (hsB β))
      · refine (congrArg (fun t => α ⊗ₜ[Y.presheaf.stalk (f (pullback.fst f g (G z)))] β * t)
          (hι _ _)).trans ?_
        refine (tmul_mul_tmul' _ _ _ _).trans (Eq.trans ?_ (hι _ _).symm)
        exact congrArg₂ (TensorProduct.tmul _) (haA α) (haB β)
    exact exists_mul_eq_of_tmul ι hgen
  · have hθ : ((G.stalkMap z).hom.comp ((tensorToStalk f g (G z)).comp ι)) =
        ((Scheme.ΓSpecIso (CommRingCat.of C)).inv ≫
          (Spec (CommRingCat.of C)).presheaf.germ ⊤ z trivial).hom := by
      refine ringHom_ext_tensor _ _ fun a b => ringHom_tmul_of_left_right _ _ a b ?_ ?_
      · refine (congrArg (fun t => (G.stalkMap z) (tensorToStalk f g (G z) t)) (hι a 1)).trans ?_
        refine (congrArg (G.stalkMap z) (tensorToStalk_tmul f g (G z) _ _)).trans ?_
        rw [map_one, map_one, mul_one]
        exact stalkMap_stalkMap_germ_of_comp_eq hV hGp z hxV a
      · refine (congrArg (fun t => (G.stalkMap z) (tensorToStalk f g (G z) t)) (hι 1 b)).trans ?_
        refine (congrArg (G.stalkMap z) (tensorToStalk_tmul f g (G z) _ _)).trans ?_
        rw [map_one, map_one, one_mul]
        exact stalkMap_stalkMap_germ_of_comp_eq hV' hGq z hxV' b
    let e := (asIso (G.stalkMap z)).commRingCatIsoToRingEquiv.symm
    have hM := (isLocalizationMap_SpecGerm (CommRingCat.of C) z).mulEquiv_comp e
    have key : ⇑((tensorToStalk f g (G z)).comp ι) =
        ⇑e ∘ ⇑((Scheme.ΓSpecIso (CommRingCat.of C)).inv ≫
          (Spec (CommRingCat.of C)).presheaf.germ ⊤ z trivial).hom := by
      funext c
      have h1 := congrArg (fun φ => φ c) hθ
      exact ((congrArg e h1.symm).trans (e.apply_symm_apply _)).symm
    exact isLocalizationMap_comap_maximalIdeal_of_isLocalizationMap _ _
      ((congrArg (Submonoid.IsLocalizationMap _) key).mpr hM)

/-- **Local rings of a fibre product.** For `x'` in `X' = X ×_Y Y'` with images `x`, `y'`, `y`,
the ring homomorphism `𝒪_{X,x} ⊗[𝒪_{Y,y}] 𝒪_{Y',y'} → 𝒪_{X',x'}` induced by the projections is a
localization at the prime ideal lying under the maximal ideal of `𝒪_{X',x'}`. -/
theorem isLocalizationMap_tensorToStalk (f : X ⟶ Y) (g : Y' ⟶ Y) (x' : ↑(pullback f g)) :
    ((IsLocalRing.maximalIdeal _).comap (tensorToStalk f g x')).primeCompl.IsLocalizationMap
      (tensorToStalk f g x') := by
  obtain ⟨_, ⟨W, hW : IsAffineOpen W, rfl⟩, hyW, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f (pullback.fst f g x')))
      isOpen_univ
  obtain ⟨_, ⟨V, hV : IsAffineOpen V, rfl⟩, hxV, hVW⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show pullback.fst f g x' ∈ f ⁻¹ᵁ W from hyW) (f ⁻¹ᵁ W).isOpen
  obtain ⟨_, ⟨V', hV' : IsAffineOpen V', rfl⟩, hxV', hV'W⟩ :=
    Y'.isBasis_affineOpens.exists_subset_of_mem_open
      (show g (pullback.snd f g x') ∈ W from base_eq f g x' ▸ hyW) (g ⁻¹ᵁ W).isOpen
  replace hVW : V ≤ f ⁻¹ᵁ W := hVW
  replace hV'W : V' ≤ g ⁻¹ᵁ W := hV'W
  let : Algebra Γ(Y, W) Γ(X, V) := (f.appLE W V hVW).hom.toAlgebra
  let : Algebra Γ(Y, W) Γ(Y', V') := (g.appLE W V' hV'W).hom.toAlgebra
  let m := pullback.map (Spec.map (f.appLE W V hVW)) (Spec.map (g.appLE W V' hV'W)) f g
    hV.fromSpec hV'.fromSpec hW.fromSpec (IsAffineOpen.SpecMap_appLE_fromSpec f hW hV hVW)
    (IsAffineOpen.SpecMap_appLE_fromSpec g hW hV' hV'W)
  let G : Spec (.of (Γ(X, V) ⊗[Γ(Y, W)] Γ(Y', V'))) ⟶ pullback f g :=
    (pullbackSpecIso Γ(Y, W) Γ(X, V) Γ(Y', V')).inv ≫ m
  have hGp : G ≫ pullback.fst f g =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫ hV.fromSpec := by
    simp only [G, m, Category.assoc, pullback.lift_fst]
    exact pullbackSpecIso_inv_fst_assoc _ _ _ _
  have hGq : G ≫ pullback.snd f g =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) ≫
        hV'.fromSpec := by
    simp only [G, m, Category.assoc, pullback.lift_snd]
    exact pullbackSpecIso_inv_snd_assoc _ _ _ _
  obtain ⟨w, hw⟩ : x' ∈ Set.range m := by
    rw [Scheme.Pullback.range_map]
    exact ⟨by rw [hV.range_fromSpec]; exact hxV, by rw [hV'.range_fromSpec]; exact hxV'⟩
  obtain ⟨z, rfl⟩ : x' ∈ Set.range G := by
    refine ⟨(pullbackSpecIso Γ(Y, W) Γ(X, V) Γ(Y', V')).hom w, ?_⟩
    rw [← hw, ← Scheme.Hom.comp_apply, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have : IsOpenImmersion G := by dsimp only [G]; infer_instance
  exact isLocalizationMap_tensorToStalk_aux f g hV hV' hVW hV'W G hGp hGq z hxV hxV' hyW

/-- The local ring `𝒪_{X',x'}` of the fibre product is the localization of
`𝒪_{X,x} ⊗[𝒪_{Y,y}] 𝒪_{Y',y'}` at the prime ideal lying under its maximal ideal. -/
theorem isLocalization_tensorToStalk (f : X ⟶ Y) (g : Y' ⟶ Y) (x' : ↑(pullback f g)) :
    letI := algebraLeft f g x'
    letI := algebraRight f g x'
    letI := (tensorToStalk f g x').toAlgebra
    IsLocalization.AtPrime ((pullback f g).presheaf.stalk x')
      ((IsLocalRing.maximalIdeal _).comap (tensorToStalk f g x')) := by
  let := algebraLeft f g x'
  let := algebraRight f g x'
  let := (tensorToStalk f g x').toAlgebra
  exact (isLocalization_iff_isLocalizationMap _ _).2 (isLocalizationMap_tensorToStalk f g x')

/-- The local ring `𝒪_{X',x'}` of the fibre product is flat over
`𝒪_{X,x} ⊗[𝒪_{Y,y}] 𝒪_{Y',y'}`. -/
theorem flat_tensorToStalk (f : X ⟶ Y) (g : Y' ⟶ Y) (x' : ↑(pullback f g)) :
    letI := algebraLeft f g x'
    letI := algebraRight f g x'
    letI := (tensorToStalk f g x').toAlgebra
    Module.Flat (X.presheaf.stalk (pullback.fst f g x') ⊗[Y.presheaf.stalk
      (f (pullback.fst f g x'))] Y'.presheaf.stalk (pullback.snd f g x'))
      ((pullback f g).presheaf.stalk x') := by
  let := algebraLeft f g x'
  let := algebraRight f g x'
  let := (tensorToStalk f g x').toAlgebra
  have := isLocalization_tensorToStalk f g x'
  exact IsLocalization.flat _ ((IsLocalRing.maximalIdeal _).comap (tensorToStalk f g x')).primeCompl

end Main

end FiberProductStalk

end Hartshorne

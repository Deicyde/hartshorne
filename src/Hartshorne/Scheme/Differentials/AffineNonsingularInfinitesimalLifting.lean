/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Hartshorne.Scheme.Differentials.DifferentialsCharacterizeNonsingular
import Hartshorne.Scheme.Differentials.NonsingularClosedImmersionConormal

/-!
# Infinitesimal lifting for a nonsingular affine scheme

Hartshorne, *Algebraic Geometry*, II, Exercise 8.6 (pp. 188–189).

Let `k` be an algebraically closed field and `A` a finitely generated `k`-algebra such that
`Spec A` is nonsingular (regular at every point). For every surjection of `k`-algebras
`B' → B` whose kernel has square zero and every `k`-algebra map `A → B`, there is a lift
`A → B'` (`Hartshorne.AffineNonsingularLifting.exists_lift_of_isRegular`).

## Proof

We follow the steps printed in the exercise.

* (a) Two lifts `A → B'` of `A → B` differ by a homomorphism `Ω_{A/k} → I`, `I` the kernel of
  `B' → B` (`Hartshorne.AffineNonsingularLifting.exists_kaehler_hom_eq_sub`); conversely,
  subtracting a derivation into `I` from a `k`-algebra map gives a `k`-algebra map
  (`Hartshorne.AffineNonsingularLifting.subDerivation`).
* (b) Write `A = P/J` with `P = k[x_1, …, x_n]`; the map `P → A → B` lifts to `h : P → B'`.
* (c) If `0 → J/J² → A ⊗_P Ω_{P/k} → Ω_{A/k} → 0` is exact and `Ω_{A/k}` is projective, then
  `Hom_A(A ⊗_P Ω_{P/k}, I) → Hom_A(J/J², I)` is surjective, and subtracting from `h` the
  derivation `θ` extending `h|_J` gives a lift `A → B'`
  (`Hartshorne.AffineNonsingularLifting.exists_lift_of_presentation`).

The hypotheses of (c) come from Theorems 8.17 and 8.15, applied on stalks.

* The stalk at `z` of the conormal map `i^* I → i^* Ω_{X/k}` of a closed immersion `i : Z → X`
  is injective exactly when, for `B = 𝒪_{X,i z} → C = 𝒪_{Z,z}` with kernel `K`, the algebraic map
  `K/K² → C ⊗_B Ω_{B/k}` is injective
  (`Hartshorne.AffineNonsingularLifting.injective_kerCotangentToTensor_stalk`); and the stalk of
  `Ω_{Z/k}` at `z` is `Ω_{C/k}` (`Hartshorne.AffineNonsingularLifting.free_kaehler_of_free_stalk`).
* For a minimal prime `𝔭₀ ⊆ q` of `A`, the closed subscheme `Spec A/𝔭₀ ⊆ Spec A` is an integral
  nonsingular closed subvariety of `𝔸^n_k = Spec P` with the same local ring at `q`, since `A_q`
  is a domain. Theorem 8.17 for `Spec A/𝔭₀ ⊆ 𝔸^n_k` gives `H¹(L_{A_q/k}) = 0`, i.e. injectivity of
  `K/K² → A_q ⊗ Ω_{P_𝔭/k}`, and Theorem 8.15 for `Spec A/𝔭₀` gives that `Ω_{A_q/k}` is free
  (`Hartshorne.AffineNonsingularLifting.subsingleton_h1Cotangent_and_mem_freeLocus`).
* Both properties are local on `Spec A`, so `J/J² → A ⊗_P Ω_{P/k}` is injective and `Ω_{A/k}` is
  projective.
-/

universe u v

open TensorProduct KaehlerDifferential

namespace Hartshorne

namespace AffineNonsingularLifting

section Lifting

variable {k : Type u} [CommRing k] {B' B : Type v} [CommRing B'] [CommRing B] [Algebra k B']
  [Algebra k B] (g : B' →ₐ[k] B)

/-- **Hartshorne II, Exercise 8.6(a).** Two lifts `u, v : C → B'` of the same map `C → B`
differ by a homomorphism `Ω_{C/k} → I` into the square-zero kernel `I` of `g`; here `I` is a
`C`-module through `u`. -/
theorem exists_kaehler_hom_eq_sub {C : Type*} [CommRing C] [Algebra k C]
    (hI : RingHom.ker g ^ 2 = ⊥) (u v : C →ₐ[k] B') (huv : g.comp u = g.comp v) :
    letI : Module C (RingHom.ker g) := Module.compHom _ u.toRingHom
    letI : IsScalarTower k C (RingHom.ker g) := ⟨fun r c m => by
      change u (r • c) • m = r • (u c • m)
      rw [map_smul, smul_assoc]⟩
    ∃ φ : Ω[C⁄k] →ₗ[C] RingHom.ker g, ∀ x, (φ (D k C x) : B') = u x - v x := by
  let _ : Module C (RingHom.ker g) := Module.compHom _ u.toRingHom
  have _ : IsScalarTower k C (RingHom.ker g) := ⟨fun r c m => by
    change u (r • c) • m = r • (u c • m)
    rw [map_smul, smul_assoc]⟩
  have hmem : ∀ x, u x - v x ∈ RingHom.ker g := fun x => by
    rw [RingHom.mem_ker, map_sub, sub_eq_zero]
    exact congr($huv x)
  have hsq : ∀ a ∈ RingHom.ker g, ∀ b ∈ RingHom.ker g, a * b = 0 := fun a ha b hb => by
    have : a * b ∈ RingHom.ker g ^ 2 := pow_two (RingHom.ker g) ▸ Ideal.mul_mem_mul ha hb
    rwa [hI, Ideal.mem_bot] at this
  let d : Derivation k C (RingHom.ker g) :=
    { toFun := fun x => ⟨u x - v x, hmem x⟩
      map_add' := fun x y => Subtype.ext (by
        change u (x + y) - v (x + y) = (u x - v x) + (u y - v y)
        simp only [map_add]; ring)
      map_smul' := fun r x => Subtype.ext (by
        change u (r • x) - v (r • x) = r • (u x - v x)
        simp [smul_sub])
      map_one_eq_zero' := Subtype.ext (by
        change u 1 - v 1 = 0
        simp)
      leibniz' := fun x y => Subtype.ext (by
        change u (x * y) - v (x * y) = u x * (u y - v y) + u y * (u x - v x)
        have h := hsq _ (hmem x) _ (hmem y)
        simp only [map_mul]
        linear_combination -h) }
  exact ⟨d.liftKaehlerDifferential, fun x => by
    rw [Derivation.liftKaehlerDifferential_comp_D]; rfl⟩

/-- Subtracting from a `k`-algebra map `h : C → B'` a `k`-linear map `θ : C → I` into a
square-zero ideal which is a derivation for the `C`-module structure given by `h` gives again a
`k`-algebra map. -/
def subDerivation {C : Type*} [CommRing C] [Algebra k C] (I : Ideal B') (hI : I ^ 2 = ⊥)
    (h : C →ₐ[k] B') (θ : C →+ B') (hθI : ∀ x, θ x ∈ I)
    (hθ : ∀ x y, θ (x * y) = h x * θ y + h y * θ x) (hθk : ∀ r : k, θ (algebraMap k C r) = 0) :
    C →ₐ[k] B' where
  toFun x := h x - θ x
  map_one' := by
    have := hθ 1 1
    rw [mul_one, map_one h, one_mul] at this
    rw [map_one h, show θ 1 = 0 by linear_combination -this, sub_zero]
  map_mul' x y := by
    have h0 : θ x * θ y = 0 := by
      have : θ x * θ y ∈ I ^ 2 := pow_two I ▸ Ideal.mul_mem_mul (hθI x) (hθI y)
      rwa [hI, Ideal.mem_bot] at this
    rw [hθ, map_mul]
    linear_combination -h0
  map_zero' := by simp
  map_add' x y := by simp only [map_add]; ring
  commutes' r := by simp [hθk]

variable {A : Type u} [CommRing A] [Algebra k A]

/-- **Hartshorne II, Exercise 8.6(b), (c).** Let `π : P = k[x_1, …, x_n] → A` be a surjection of
`k`-algebras with kernel `J`, such that `J/J² → A ⊗_P Ω_{P/k}` is injective and `Ω_{A/k}` is
projective. Then every `k`-algebra map `f : A → B` lifts along a surjection `g : B' → B` with
square-zero kernel `I`.

(b) The composite `P → A → B` lifts to `h : P → B'`, since `P` is a polynomial ring.
(c) The sequence `0 → J/J² → A ⊗_P Ω_{P/k} → Ω_{A/k} → 0` is exact and splits, as `Ω_{A/k}` is
projective, so `Hom(A ⊗_P Ω_{P/k}, I) → Hom(J/J², I)` is surjective: the map `J/J² → I` induced
by `h` extends to `ψ : A ⊗_P Ω_{P/k} → I`. Then `θ = ψ ∘ (1 ⊗ d)` is a derivation `P → I` and
`h - θ` is a `k`-algebra map killing `J`, hence a lift of `f`. -/
theorem exists_lift_of_presentation {n : ℕ} (π : MvPolynomial (Fin n) k →ₐ[k] A)
    (hπ : Function.Surjective π)
    (hinj : letI := π.toRingHom.toAlgebra
      Function.Injective (kerCotangentToTensor k (MvPolynomial (Fin n) k) A))
    (hproj : Module.Projective A Ω[A⁄k]) (hg : Function.Surjective g)
    (hI : RingHom.ker g ^ 2 = ⊥) (f : A →ₐ[k] B) :
    ∃ f' : A →ₐ[k] B', g.comp f' = f := by
  classical
  let P := MvPolynomial (Fin n) k
  let : Algebra P A := π.toRingHom.toAlgebra
  have : IsScalarTower k P A := IsScalarTower.of_algebraMap_eq' π.comp_algebraMap.symm
  have hπ' : Function.Surjective (algebraMap P A) := hπ
  let J := RingHom.ker (algebraMap P A)
  -- (b) a lift `h : P → B'` of `P → A → B`
  let h : P →ₐ[k] B' := MvPolynomial.aeval fun i => Function.surjInv hg (f (π (.X i)))
  have hgh : ∀ x, g (h x) = f (π x) := fun x => by
    have : g.comp h = f.comp π := MvPolynomial.algHom_ext fun i => by
      simp [h, Function.surjInv_eq hg]
    exact congr($this x)
  have hsq : ∀ a ∈ RingHom.ker g, ∀ b ∈ RingHom.ker g, a * b = 0 := fun a ha b hb => by
    have : a * b ∈ RingHom.ker g ^ 2 := pow_two (RingHom.ker g) ▸ Ideal.mul_mem_mul ha hb
    rwa [hI, Ideal.mem_bot] at this
  have hJ : ∀ j ∈ J, h j ∈ RingHom.ker g := fun j hj => by
    rw [RingHom.mem_ker, hgh]
    change f (algebraMap P A j) = 0
    rw [RingHom.mem_ker.mp hj, map_zero]
  -- the map `J/J² → I` induced by `h`, with `P` acting on `B'` through `h`
  let : Module P B' := Module.compHom B' h.toRingHom
  have hsmul : ∀ (x : P) (b : B'), x • b = h x * b := fun _ _ => rfl
  let L : J →ₗ[P] B' :=
    { toFun := fun x => h x.1
      map_add' := fun x y => map_add h x.1 y.1
      map_smul' := fun x y => by
        change h (x * y.1) = x • h y.1
        rw [map_mul, hsmul] }
  let hbar : J.Cotangent →ₗ[P] B' := Submodule.liftQ _ L (by
    refine Submodule.smul_le.mpr fun r hr m _ => ?_
    change h (r * m.1) = 0
    rw [map_mul]
    exact hsq _ (hJ r hr) _ (hJ m.1 m.2))
  have hbar_mk : ∀ j : J, hbar (J.toCotangent j) = h j.1 := fun _ => rfl
  have hbarI : ∀ c, hbar c ∈ RingHom.ker g := fun c => by
    obtain ⟨j, rfl⟩ := J.toCotangent_surjective c
    rw [hbar_mk]
    exact hJ j.1 j.2
  -- (c) a retraction `ρ` of `J/J² → A ⊗_P Ω_{P/k}`, from a section of `A ⊗_P Ω_{P/k} → Ω_{A/k}`
  let N := A ⊗[P] Ω[P⁄k]
  let ι := kerCotangentToTensor k P A
  let q := mapBaseChange k P A
  have hex : Function.Exact ι q := exact_kerCotangentToTensor_mapBaseChange k P A hπ'
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property q LinearMap.id
    (mapBaseChange_surjective k P A hπ')
  let e : N →ₗ[P] N := LinearMap.id - ((σ ∘ₗ q).restrictScalars P)
  have hqe : ∀ w, q (e w) = 0 := fun w => by
    have h1 : q (σ (q w)) = q w := congr($hσ (q w))
    change q (w - σ (q w)) = 0
    rw [map_sub, h1, sub_self]
  have he : ∀ w, e w ∈ LinearMap.range ι := fun w => (hex (e w)).mp (hqe w)
  let ρ : N →ₗ[P] J.Cotangent :=
    (LinearEquiv.ofInjective ι hinj).symm.toLinearMap ∘ₗ e.codRestrict _ he
  have hρ : ∀ c, ρ (ι c) = c := fun c => by
    have h0 : q (ι c) = 0 := hex.apply_apply_eq_zero c
    have h1 : e (ι c) = ι c := by
      change ι c - σ (q (ι c)) = ι c
      rw [h0, map_zero, sub_zero]
    refine (LinearEquiv.symm_apply_eq _).mpr (Subtype.ext ?_)
    exact h1.trans (LinearEquiv.ofInjective_apply _ c).symm
  -- the derivation `θ = ψ ∘ (1 ⊗ d) : P → I`, with `ψ = h̄ ∘ ρ`
  let ψ : N →ₗ[P] B' := hbar ∘ₗ ρ
  let θ : P →+ B' :=
    { toFun := fun x => ψ (1 ⊗ₜ D k P x)
      map_zero' := by rw [map_zero, TensorProduct.tmul_zero, map_zero]
      map_add' := fun x y => by rw [map_add, TensorProduct.tmul_add, map_add] }
  have hθI : ∀ x, θ x ∈ RingHom.ker g := fun x => hbarI _
  have hθ : ∀ x y, θ (x * y) = h x * θ y + h y * θ x := fun x y => by
    change ψ (1 ⊗ₜ D k P (x * y)) = h x * ψ (1 ⊗ₜ D k P y) + h y * ψ (1 ⊗ₜ D k P x)
    rw [Derivation.leibniz, TensorProduct.tmul_add, TensorProduct.tmul_smul,
      TensorProduct.tmul_smul, map_add, map_smul, map_smul, hsmul, hsmul]
  have hθk : ∀ r : k, θ (algebraMap k P r) = 0 := fun r => by
    change ψ (1 ⊗ₜ D k P (algebraMap k P r)) = 0
    rw [Derivation.map_algebraMap, TensorProduct.tmul_zero, map_zero]
  -- `h - θ` kills `J`
  let h' := subDerivation (RingHom.ker g) hI h θ hθI hθ hθk
  have hh' : ∀ x, h' x = h x - θ x := fun _ => rfl
  have hJ' : ∀ j ∈ RingHom.ker π, h' j = 0 := fun j hj => by
    have h1 : (1 : A) ⊗ₜ[P] D k P j = ι (J.toCotangent ⟨j, hj⟩) := rfl
    rw [hh', sub_eq_zero]
    change h j = ψ (1 ⊗ₜ D k P j)
    rw [h1]
    change h j = hbar (ρ (ι (J.toCotangent ⟨j, hj⟩)))
    rw [hρ, hbar_mk]
  let f' : A →ₐ[k] B' := (Ideal.Quotient.liftₐ (RingHom.ker π) h' hJ').comp
    (Ideal.quotientKerAlgEquivOfSurjective hπ).symm.toAlgHom
  refine ⟨f', AlgHom.ext fun a => ?_⟩
  obtain ⟨x, rfl⟩ := hπ a
  have h1 : (Ideal.quotientKerAlgEquivOfSurjective hπ).symm (π x) = Ideal.Quotient.mk _ x :=
    (AlgEquiv.symm_apply_eq _).mpr rfl
  change g (Ideal.Quotient.liftₐ (RingHom.ker π) h' hJ'
    ((Ideal.quotientKerAlgEquivOfSurjective hπ).symm (π x))) = f (π x)
  rw [h1]
  change g (h' x) = f (π x)
  rw [hh', map_sub, hgh, RingHom.mem_ker.mp (hθI x), sub_zero]

end Lifting

section StalkConormal

open CategoryTheory Limits Opposite AlgebraicGeometry Ringed ModuleSheafTensor Scheme
  LCICohenMacaulay ClosedConormal

variable {Z X Y : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (f : X ⟶ Y) (z : Z)

/-- If the stalk at `z` of the conormal map `i^* I ⟶ i^* Ω_{X/Y}` is injective, then so is the
algebraic map `K/K² → C ⊗_B Ω_{B/A}` for `A = 𝒪_{Y,f(i z)} → B = 𝒪_{X,i z} → C = 𝒪_{Z,z}` and
`K = ker(B → C)`. An element `a ∈ K` is the germ of a section `t` of `I`; the stalk map sends the
germ of `i^* t` to `(i^* d a)_z`, which is the image of `1 ⊗ d a`; and the morphism
`(i^* I)_z → C ⊗_B K` adjoint to `I_{i z} → C ⊗_B K`, `t ↦ 1 ⊗ t`, sends the germ of `i^* t` to
`1 ⊗ a`. Since `C ⊗_B K = K/K²`, the class of `a` vanishes once `1 ⊗ d a` does. -/
theorem injective_kerCotangentToTensor_stalk
    (hinj : Function.Injective
      ((moduleStalkFunctor (R := Z.sheaf) z).map (conormalToPullback i f))) :
    letI : Algebra (ringSheafStalk X.sheaf (i z)) (ringSheafStalk Z.sheaf z) :=
      (stalkHom i z).toAlgebra
    letI : Algebra (ringSheafStalk Y.sheaf (f (i z))) (ringSheafStalk X.sheaf (i z)) :=
      (stalkHom f (i z)).toAlgebra
    Function.Injective (KaehlerDifferential.kerCotangentToTensor
      (ringSheafStalk Y.sheaf (f (i z))) (ringSheafStalk X.sheaf (i z))
      (ringSheafStalk Z.sheaf z)) := by
  let Rz := ringSheafStalk Z.sheaf z
  let Rx := ringSheafStalk X.sheaf (i z)
  let Ry := ringSheafStalk Y.sheaf (f (i z))
  let : Algebra Rx Rz := (stalkHom i z).toAlgebra
  let : Algebra Ry Rx := (stalkHom f (i z)).toAlgebra
  let _ : Algebra Ry Rz := ((stalkHom i z).comp (stalkHom f (i z))).toAlgebra
  have _ : IsScalarTower Ry Rx Rz := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hsurj : Function.Surjective (algebraMap Rx Rz) := i.stalkMap_surjective z
  let K := RingHom.ker (algebraMap Rx Rz)
  -- the derivation `B → (i^*Ω_{X/Y})_z`, `b ↦ (i^* d b)_z` (as in Proposition 8.12)
  let T2 := (moduleStalkFunctor (R := Z.sheaf) z).obj
    ((Modules.pullback i).obj (relativeDifferentials f))
  let _ : Module Rx T2 := Module.compHom T2 (stalkHom i z)
  have _ : IsScalarTower Rx Rz T2 := ⟨fun a b c => mul_smul (stalkHom i z a) b c⟩
  let _ : Module Ry T2 := Module.compHom T2 (algebraMap Ry Rz)
  have _ : IsScalarTower Ry Rx T2 := ⟨fun a b c => by
    change (stalkHom i z (stalkHom f (i z) a * b)) • c =
      (stalkHom i z (stalkHom f (i z) a)) • (stalkHom i z b • c)
    rw [map_mul, mul_smul]⟩
  have hk2 : ∀ a : Ry, stalkUnitD i f z (algebraMap Ry Rx a) = 0 := fun a => by
    obtain ⟨V, hV, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq Y.sheaf.obj a
    erw [Scheme.Hom.germ_stalkMap_apply]
    exact stalkUnitD_app i f z V t hV
  let D2 : Derivation Ry Rx T2 := Derivation.mk'
    { toFun := stalkUnitD i f z
      map_add' := stalkUnitD_add i f z
      map_smul' := fun a r => by
        change stalkUnitD i f z (algebraMap Ry Rx a * r) = algebraMap Ry Rz a • _
        rw [stalkUnitD_mul, hk2, smul_zero, add_zero]
        rfl }
    (stalkUnitD_mul i f z)
  let φ2 : Rz ⊗[Rx] Ω[Rx⁄Ry] →ₗ[Rz] T2 := D2.liftKaehlerDifferential.liftBaseChange Rz
  let p := ((moduleStalkFunctor (R := Z.sheaf) z).map (conormalToPullback i f)).hom
  -- the morphism `Ψ : (i^* I)_z → C ⊗_B K` adjoint to `I_{i z} → C ⊗_B K`, `t ↦ 1 ⊗ t`
  let N : ModuleCat.{u} Rz := ModuleCat.of Rz (Rz ⊗[Rx] K)
  let ℓ : (moduleStalkFunctor (R := X.sheaf) (i z)).obj (closedImmersionIdealSheaf i) ⟶
      (ModuleCat.restrictScalars (i.stalkMap z).hom).obj N := ModuleCat.ofHom
    { toFun := fun s => (1 : Rz) ⊗ₜ[Rx]
        (⟨idealStalkMap i (i z) s, RingHom.mem_ker.mpr (stalkMap_idealStalkMap i z s)⟩ : K)
      map_add' := fun s s' => by
        rw [← TensorProduct.tmul_add]
        congr 1
        exact Subtype.ext (map_add _ s s')
      map_smul' := fun b s => by
        change (1 : Rz) ⊗ₜ[Rx] (⟨idealStalkMap i (i z) (b • s), _⟩ : K) =
          (algebraMap Rx Rz b) • ((1 : Rz) ⊗ₜ[Rx]
            (⟨idealStalkMap i (i z) s, RingHom.mem_ker.mpr (stalkMap_idealStalkMap i z s)⟩ : K))
        rw [TensorProduct.smul_tmul', algebraMap_smul, TensorProduct.smul_tmul]
        congr 1
        exact Subtype.ext (idealStalkMap_smul i (i z) b s) }
  let g1 := (moduleStalkSkyscraperAdjunction (R := X.sheaf) (i z)).homEquiv _ _ ℓ
  let g2 := g1 ≫ (pushforwardSkyscraperIso i z).inv.app N
  let g3 := ((Modules.pullbackPushforwardAdjunction i).homEquiv _ _).symm g2
  let Ψ := ofSkyscraper g3
  have hΨ : ∀ (V : X.Opens) (hz : i z ∈ V) (t : Γ(closedImmersionIdealSheaf i, V)),
      Ψ.hom (sectionGerm ((Modules.pullback i).obj (closedImmersionIdealSheaf i)).val z (i ⁻¹ᵁ V) hz
        (((Modules.pullbackPushforwardAdjunction i).unit.app
          (closedImmersionIdealSheaf i)).val.app (op V) t)) =
        ℓ.hom (sectionGerm (closedImmersionIdealSheaf i).val (i z) V hz t) := by
    intro V hz t
    erw [ofSkyscraper_germ]
    have h := congr(($(((Modules.pullbackPushforwardAdjunction i).homEquiv_unit _ _ g3).symm.trans
      (Equiv.apply_symm_apply _ g2))).val.app (op V) t)
    exact congrFun h ⟨hz⟩

  -- `C ⊗_B K → K/K²`, `1 ⊗ a ↦ [a]`
  let eq : Rz →ₗ[Rx] Rx ⧸ K :=
    { toFun := (RingHom.quotientKerEquivOfSurjective hsurj).symm
      map_add' := map_add _
      map_smul' := fun b c => by
        rw [Algebra.smul_def, map_mul, RingHom.id_apply, Algebra.smul_def]
        congr 1
        exact (RingEquiv.symm_apply_eq _).mpr rfl }
  let χ : Rz ⊗[Rx] K →ₗ[Rx] K.Cotangent :=
    (quotTensorEquivQuotSMul K K).toLinearMap ∘ₗ eq.rTensor K
  have hχ : ∀ a : K, χ ((1 : Rz) ⊗ₜ a) = K.toCotangent a := fun a => by
    have h1 : eq 1 = Ideal.Quotient.mk K 1 :=
      map_one (RingHom.quotientKerEquivOfSurjective hsurj).symm
    change quotTensorEquivQuotSMul K K (eq 1 ⊗ₜ a) = _
    rw [h1, quotTensorEquivQuotSMul_mk_tmul, one_smul]
    rfl
  rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨a, rfl⟩ := K.toCotangent_surjective c
  -- `(i^* d a)_z = 0`
  have hd : stalkUnitD i f z a.1 = 0 := by
    have h := congrArg φ2 hc
    rwa [KaehlerDifferential.kerCotangentToTensor_toCotangent, LinearMap.liftBaseChange_tmul,
      one_smul, Derivation.liftKaehlerDifferential_comp_D, map_zero] at h
  -- `a` is the germ of a section `t'` of `I` (as in Proposition 8.12)
  obtain ⟨V, hxV, s, hs⟩ := TopCat.Presheaf.exists_germ_eq X.sheaf.obj a.1
  have ha' : Z.presheaf.germ (i ⁻¹ᵁ V) z hxV (i.app V s) = 0 := by
    erw [← Scheme.Hom.germ_stalkMap_apply]
    erw [hs]
    exact RingHom.mem_ker.mp a.2
  obtain ⟨W', hzW', j₁, j₂, hW'⟩ := Z.presheaf.germ_eq z (U := i ⁻¹ᵁ V) (V := i ⁻¹ᵁ V)
    hxV hxV (i.app V s) 0 (ha'.trans (map_zero _).symm)
  obtain ⟨t, ht, htW⟩ := i.isClosedEmbedding.isInducing.isOpen_iff.mp W'.2
  let V' : X.Opens := V ⊓ ⟨t, ht⟩
  have hzt : z ∈ i ⁻¹' t := by rw [htW]; exact hzW'
  have hxV' : i z ∈ V' := ⟨hxV, hzt⟩
  have hle : i ⁻¹ᵁ V' ≤ W' := fun w hw => by
    have : w ∈ i ⁻¹' t := hw.2
    rw [htW] at this
    exact this
  let s' := X.presheaf.map (homOfLE inf_le_left : V' ⟶ V).op s
  have hs' : i.app V' s' = 0 := by
    have hnat : i.app V' s' = Z.presheaf.map ((TopologicalSpace.Opens.map i.base).map
        (homOfLE (inf_le_left : V' ≤ V)).op.unop).op (i.app V s) :=
      congr(ConcreteCategory.hom $(i.naturality (homOfLE inf_le_left : V' ⟶ V).op) s)
    rw [hnat]
    have hcomp : Z.presheaf.map ((TopologicalSpace.Opens.map i.base).map
        (homOfLE (inf_le_left : V' ≤ V)).op.unop).op =
        Z.presheaf.map (j₁.op ≫ (homOfLE hle).op) := rfl
    rw [hcomp, Functor.map_comp, ConcreteCategory.comp_apply, hW', map_zero, map_zero]
  let S : ShortComplex X.Modules := ShortComplex.mk (kernel.ι (structureSheafToPushforward i))
    (structureSheafToPushforward i) (kernel.condition (structureSheafToPushforward i))
  have : Mono S.f := by change Mono (closedImmersionIdealSheafι i); infer_instance
  obtain ⟨t', ht'⟩ := modules_sections_exact (S := S)
    (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)) (U := V') s' hs'
  have ht'' : (closedImmersionIdealSheafι i).val.app (op V') t' = s' := ht'
  have hgerm : X.presheaf.germ V' (i z) hxV' s' = a.1 := by
    rw [← hs]
    exact X.presheaf.germ_res_apply (homOfLE inf_le_left) (i z) hxV' s
  let m := sectionGerm ((Modules.pullback i).obj (closedImmersionIdealSheaf i)).val z
    (i ⁻¹ᵁ V') hxV' (((Modules.pullbackPushforwardAdjunction i).unit.app
      (closedImmersionIdealSheaf i)).val.app (op V') t')
  -- the conormal map sends `m` to `(i^* d a)_z = 0`
  have hpm : p m = stalkUnitD i f z a.1 := by
    erw [moduleStalkFunctor_map_germ]
    rw [← hgerm]
    erw [stalkUnitD_germ]
    have h1 := congr(($(homEquiv_conormalToPullback i f)).val.app (op V') t')
    rw [Adjunction.homEquiv_unit] at h1
    refine (congrArg (sectionGerm _ z _ hxV') h1).trans ?_
    exact congrArg (fun v => sectionGerm ((Modules.pullback i).obj (relativeDifferentials f)).val
      z (i ⁻¹ᵁ V') hxV' (((Modules.pullbackPushforwardAdjunction i).unit.app
        (relativeDifferentials f)).val.app (op V') ((relativeDifferentialsDerivation f).d v))) ht''
  -- `Ψ` sends `m` to `1 ⊗ a`
  have hΨm : Ψ.hom m = (1 : Rz) ⊗ₜ[Rx] a := by
    refine (hΨ V' hxV' t').trans ?_
    change (1 : Rz) ⊗ₜ[Rx] (⟨_, _⟩ : K) = _
    congr 1
    refine Subtype.ext ?_
    change idealStalkMap i (i z) ((closedImmersionIdealSheaf i).presheaf.germ V' (i z) hxV' t') = _
    refine (idealStalkMap_germ i (i z) V' hxV' t').trans ?_
    change X.presheaf.germ V' (i z) hxV' ((closedImmersionIdealSheafι i).val.app (op V') t') = _
    rw [ht'', hgerm]
  have hm : m = 0 := hinj (hpm.trans (hd.trans (map_zero p).symm))
  rw [← hχ, ← hΨm, hm]
  erw [LinearMap.map_zero]
  exact map_zero χ

/-- The stalk of `Ω_{Z/Y}` at `z` is `Ω_{C/A}` for `A = 𝒪_{Y,g z} → C = 𝒪_{Z,z}` (the comparison
map of Proposition 8.12 is bijective), so if the stalk is free, so is `Ω_{C/A}`. -/
theorem free_kaehler_of_free_stalk {Z Y : Scheme.{u}} (g : Z ⟶ Y) (z : Z)
    (hfree : Module.Free (ringSheafStalk Z.sheaf z)
      ((moduleStalkFunctor (R := Z.sheaf) z).obj (relativeDifferentials g))) :
    letI : Algebra (ringSheafStalk Y.sheaf (g z)) (ringSheafStalk Z.sheaf z) :=
      (stalkHom g z).toAlgebra
    Module.Free (ringSheafStalk Z.sheaf z)
      Ω[ringSheafStalk Z.sheaf z⁄ringSheafStalk Y.sheaf (g z)] := by
  let Rz := ringSheafStalk Z.sheaf z
  let Ry := ringSheafStalk Y.sheaf (g z)
  let : Algebra Ry Rz := (stalkHom g z).toAlgebra
  let T3 := (moduleStalkFunctor (R := Z.sheaf) z).obj (relativeDifferentials g)
  let _ : Module Ry T3 := Module.compHom T3 (algebraMap Ry Rz)
  have _ : IsScalarTower Ry Rz T3 := ⟨fun a b c => mul_smul (algebraMap Ry Rz a) b c⟩
  have hk3 : ∀ a : Ry, stalkD g z (algebraMap Ry Rz a) = 0 := fun a => by
    obtain ⟨V, hV, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq Y.sheaf.obj a
    erw [Scheme.Hom.germ_stalkMap_apply]
    exact stalkD_app g z V t hV
  let D3 : Derivation Ry Rz T3 := Derivation.mk'
    { toFun := stalkD g z
      map_add' := stalkD_add g z
      map_smul' := fun a r => by
        change stalkD g z (algebraMap Ry Rz a * r) = algebraMap Ry Rz a • _
        rw [stalkD_mul, hk3, smul_zero, add_zero] }
    (stalkD_mul g z)
  let φ3 : Ω[Rz⁄Ry] →ₗ[Rz] T3 := D3.liftKaehlerDifferential
  have hφ3s : Function.Surjective φ3 := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← span_germD g z, Submodule.span_le]
    rintro _ ⟨U, hU, s, rfl⟩
    refine ⟨KaehlerDifferential.D Ry Rz (TopCat.Presheaf.germ Z.sheaf.obj U z hU s), ?_⟩
    rw [Derivation.liftKaehlerDifferential_comp_D]
    exact stalkD_germ g z U hU s
  have hφ3i : Function.Injective φ3 := by
    obtain ⟨b, hb⟩ := exists_stalkD_inverse g z (A := Ry) fun V t hz => by
      erw [← Scheme.Hom.germ_stalkMap_apply]
      exact (KaehlerDifferential.D Ry Rz).map_algebraMap _
    refine Function.LeftInverse.injective (g := b) fun ω => ?_
    have hω : ω ∈ Submodule.span Rz (Set.range (KaehlerDifferential.D Ry Rz)) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    induction hω using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨r, rfl⟩ := h
      obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq Z.sheaf.obj r
      rw [Derivation.liftKaehlerDifferential_comp_D]
      exact (congrArg b (stalkD_germ g z U hU s)).trans (hb U hU s)
    | zero => rw [map_zero, map_zero]
    | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
    | smul r x _ h => rw [map_smul, map_smul, h]
  exact Module.Free.of_equiv (LinearEquiv.ofBijective φ3 ⟨hφ3i, hφ3s⟩).symm

end StalkConormal

section Local

open CategoryTheory Limits AlgebraicGeometry Ringed Scheme ClosedConormal

variable {k : Type u} [Field k] [IsAlgClosed k] {X Z : Scheme.{u}} (p : X ⟶ Spec (.of k))
  (i : Z ⟶ X) [IsClosedImmersion i]

omit [IsAlgClosed k] in
/-- A nonempty closed subscheme `Z` of an irreducible nonsingular scheme `X` of finite type over a
field has finite dimension and finite codimension in `X` (Exercise II.3.20). -/
theorem exists_codim_eq (hp : FiniteType p) [IrreducibleSpace X] (hX : X.IsRegular) (z : Z) :
    ∃ q r : ℕ, topologicalKrullDim Z = q ∧ codim (Set.range i.base) = r := by
  have : IsIntegral X := isIntegral_of_isRegular hX
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (i z)) isOpen_univ
  have : Nonempty U := ⟨⟨i z, hyU⟩⟩
  obtain ⟨n, -, hn⟩ := DimensionCodimension.exists_ringKrullDim_eq p hp U hU
  have hdc := dimension_codimension_formula p hp (Set.range i.base)
    i.isClosedEmbedding.isClosed_range (Set.range_nonempty_iff_nonempty.mpr ⟨z⟩)
  rw [← IsHomeomorph.topologicalKrullDim_eq _
    (i.isClosedEmbedding.toHomeomorph).isHomeomorph, hn] at hdc
  generalize topologicalKrullDim Z = e at hdc ⊢
  generalize codim (Set.range i.base) = c at hdc ⊢
  induction e using WithBot.recBotCoe with
  | bot => simp at hdc
  | coe e =>
    have h : e + c = n := by exact_mod_cast hdc
    induction e using ENat.recTopCoe with
    | top => simp at h
    | coe q =>
      induction c using ENat.recTopCoe with
      | top => simp at h
      | coe r => exact ⟨q, r, rfl, rfl⟩

/-- **Theorem 8.17 on stalks.** For an irreducible nonsingular closed subscheme `i : Z ⟶ X` of an
irreducible nonsingular `X` of finite type over `k`, at every `z ∈ Z` the map
`K/K² → C ⊗_B Ω_{B/A}` is injective, for `A = 𝒪_{Spec k}`, `B = 𝒪_{X,i z}`, `C = 𝒪_{Z,z}` and
`K = ker(B → C)`: the conormal sequence of Theorem 8.17 is exact on the left. -/
theorem injective_kerCotangentToTensor_of_isRegular (hp : FiniteType p) [IrreducibleSpace X]
    (hX : X.IsRegular) [IrreducibleSpace Z] (hZ : Z.IsRegular) (z : Z) :
    letI : Algebra (ringSheafStalk X.sheaf (i z)) (ringSheafStalk Z.sheaf z) :=
      (stalkHom i z).toAlgebra
    letI : Algebra (ringSheafStalk (Spec (.of k)).sheaf (p (i z))) (ringSheafStalk X.sheaf (i z)) :=
      (stalkHom p (i z)).toAlgebra
    Function.Injective (KaehlerDifferential.kerCotangentToTensor
      (ringSheafStalk (Spec (.of k)).sheaf (p (i z))) (ringSheafStalk X.sheaf (i z))
      (ringSheafStalk Z.sheaf z)) := by
  obtain ⟨-, r, -, hr⟩ := exists_codim_eq p i hp hX z
  obtain ⟨hS, -, -⟩ := NonsingularConormal.nonsingular_closedImmersion_conormal p i hp hX hZ r hr
  have := hS.mono_f
  exact injective_kerCotangentToTensor_stalk i p z
    (TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective (C := AddCommGrpCat.{u})
      (fun U => NonsingularConormal.modules_app_injective_of_mono
        (conormalToPullback i p) U) z)

/-- **Theorem 8.15 on stalks.** For a nonsingular irreducible `Z` of finite type over `k`, at every
`z ∈ Z` the module `Ω_{C/A}` is free, for `A = 𝒪_{Spec k}` and `C = 𝒪_{Z,z}`: `Ω_{Z/k}` is locally
free. -/
theorem free_kaehler_of_isRegular (hp : FiniteType p) [IrreducibleSpace X] (hX : X.IsRegular)
    [IrreducibleSpace Z] (hZ : Z.IsRegular) (z : Z) :
    letI : Algebra (ringSheafStalk (Spec (.of k)).sheaf ((i ≫ p) z)) (ringSheafStalk Z.sheaf z) :=
      (stalkHom (i ≫ p) z).toAlgebra
    Module.Free (ringSheafStalk Z.sheaf z)
      Ω[ringSheafStalk Z.sheaf z⁄ringSheafStalk (Spec (.of k)).sheaf ((i ≫ p) z)] := by
  obtain ⟨q, -, hq, -⟩ := exists_codim_eq p i hp hX z
  have := hp.1
  have := hp.2
  have hp' : FiniteType (i ≫ p) := ⟨inferInstance, inferInstance⟩
  have hΩ := (isRegular_iff_relativeDifferentials_isLocallyFreeOfRank (i ≫ p) hp' q hq).mp hZ
  obtain ⟨e⟩ := NonsingularConormal.nonempty_stalk_equiv_of_isLocallyFreeOfRank _ q hΩ z
  let e' : (moduleStalkFunctor (R := Z.sheaf) z).obj (relativeDifferentials (i ≫ p)) ≃ₗ[
      ringSheafStalk Z.sheaf z] (Fin q → ringSheafStalk Z.sheaf z) := e
  exact free_kaehler_of_free_stalk (i ≫ p) z (Module.Free.of_equiv e'.symm)

end Local

section Affine

open CategoryTheory AlgebraicGeometry Ringed Scheme StructureSheaf KaehlerDifferential
  ClosedConormal

/-- Along a tower `R → S → A → B`, if `K/K² → B ⊗_A Ω_{A/S}` is injective then so is
`K/K² → B ⊗_A Ω_{A/R}`, which it factors. -/
theorem injective_kerCotangentToTensor_of_tower (R S A B : Type*) [CommRing R] [CommRing S]
    [CommRing A] [CommRing B] [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]
    [Algebra A B] (h : Function.Injective (kerCotangentToTensor S A B)) :
    Function.Injective (kerCotangentToTensor R A B) := by
  have e : kerCotangentToTensor S A B =
      (map R S A A).lTensor B ∘ₗ kerCotangentToTensor R A B := by
    refine LinearMap.ext fun c => ?_
    obtain ⟨a, rfl⟩ := Ideal.toCotangent_surjective _ c
    simp only [LinearMap.comp_apply, kerCotangentToTensor_toCotangent, LinearMap.lTensor_tmul,
      map_D, Algebra.algebraMap_self, RingHom.id_apply]
  intro x y hxy
  apply h
  rw [e, LinearMap.comp_apply, LinearMap.comp_apply, hxy]

/-- If `R → S` is surjective, then `Ω_{B/R} → Ω_{B/S}` is bijective. -/
theorem bijective_map_of_surjective (R S B : Type*) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra S B] [Algebra R B] [IsScalarTower R S B]
    (h : Function.Surjective (algebraMap R S)) :
    Function.Bijective (map R S B B) := by
  refine ⟨?_, map_surjective R S B⟩
  have := subsingleton_of_surjective R S h
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := (exact_mapBaseChange_map R S B x).mp hx
  rw [Subsingleton.elim y 0, map_zero]

variable {k : Type u} [Field k]

/-- The stalk of `Spec k` at its point is `k`: the map `k → 𝒪_{Spec k}` is surjective. -/
theorem surjective_algebraMap_stalk (x : PrimeSpectrum k) :
    letI : Algebra k ((Spec (.of k)).presheaf.stalk x) := StructureSheaf.stalkAlgebra k x
    Function.Surjective (algebraMap k ((Spec (.of k)).presheaf.stalk x)) := by
  let : Algebra k ((Spec (.of k)).presheaf.stalk x) := StructureSheaf.stalkAlgebra k x
  have : IsLocalization.AtPrime ((Spec (.of k)).presheaf.stalk x) x.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk k x
  intro t
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj x.asIdeal.primeCompl t
  dsimp only at hs
  have hs0 : (s : k) ≠ 0 := fun h0 => s.2 (h0 ▸ x.asIdeal.zero_mem)
  have h1 : algebraMap k ((Spec (.of k)).presheaf.stalk x) (s : k) *
      algebraMap k ((Spec (.of k)).presheaf.stalk x) ((s : k)⁻¹) = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hs0, map_one]
  refine ⟨a * (s : k)⁻¹, ?_⟩
  rw [map_mul, ← hs, mul_assoc, h1, mul_one]

variable [IsAlgClosed k]

/-- **The local form of the conormal sequence for a nonsingular affine variety.** Let
`π : P = k[x_1, …, x_n] → A'` be a surjection onto a domain with `Spec A'` nonsingular, and let
`C = A'_𝔮` be a local ring of `A'`. Then `H¹(L_{C/k}) = 0` (that is, `K/K² → C ⊗ Ω_{P_𝔭/k}` is
injective for `K = ker(P_𝔭 → C)`) and `Ω_{C/k}` is free. This applies Theorem 8.17 to the closed
immersion `Spec A' → 𝔸^n_k`, and Theorem 8.15 to `Spec A'`, on stalks. -/
theorem subsingleton_h1Cotangent_and_free_stalk {n : ℕ} {A' : Type u} [CommRing A'] [Algebra k A']
    [IsDomain A'] (π : MvPolynomial (Fin n) k →ₐ[k] A') (hπ : Function.Surjective π)
    (hZ : (Spec (.of A')).IsRegular) (z : PrimeSpectrum A') :
    letI : Algebra A' ((Spec (.of A')).presheaf.stalk z) := StructureSheaf.stalkAlgebra A' z
    letI : Algebra k ((Spec (.of A')).presheaf.stalk z) :=
      ((algebraMap A' _).comp (algebraMap k A')).toAlgebra
    Subsingleton (Algebra.H1Cotangent k ((Spec (.of A')).presheaf.stalk z)) ∧
      Module.Free ((Spec (.of A')).presheaf.stalk z) Ω[(Spec (.of A')).presheaf.stalk z⁄k] := by
  let P := MvPolynomial (Fin n) k
  let φ : CommRingCat.of P ⟶ CommRingCat.of A' := CommRingCat.ofHom π.toRingHom
  let X := Spec (.of P)
  let Z := Spec (.of A')
  let i : Z ⟶ X := Spec.map φ
  let z' : Z := z
  have : IsClosedImmersion i := IsClosedImmersion.spec_of_surjective φ hπ
  let p : X ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k P))
  have hp : FiniteType p := ⟨HasRingHomProperty.Spec_iff.mpr
    (RingHom.finiteType_algebraMap.mpr inferInstance), inferInstance⟩
  have hX : X.IsRegular := by
    refine ⟨inferInstance, fun x => ?_⟩
    have := x.2
    let _ : Algebra P (X.presheaf.stalk x) := StructureSheaf.stalkAlgebra P x
    have : IsLocalization.AtPrime (X.presheaf.stalk x) x.asIdeal :=
      StructureSheaf.IsLocalization.to_stalk P x
    exact IsRegularLocalRing.of_ringEquiv
      (IsLocalization.algEquiv x.asIdeal.primeCompl (Localization.AtPrime x.asIdeal)
        (X.presheaf.stalk x)).toRingEquiv
  have := (i z').2
  have h1 := injective_kerCotangentToTensor_of_isRegular p i hp hX hZ z'
  have h2 := free_kaehler_of_isRegular p i hp hX hZ z'
  -- the rings `k`, `𝒪_{Spec k}`, `B = P_𝔭`, `C = A'_𝔮`
  let Rz := Z.presheaf.stalk z'
  let Rx := X.presheaf.stalk (i z')
  let Ry := (Spec (.of k)).presheaf.stalk (p (i z'))
  let : Algebra A' Rz := StructureSheaf.stalkAlgebra A' z
  let : Algebra k Rz := ((algebraMap A' Rz).comp (algebraMap k A')).toAlgebra
  let : Algebra P Rx := StructureSheaf.stalkAlgebra P (i z')
  have : IsLocalization.AtPrime Rx (i z').asIdeal := StructureSheaf.IsLocalization.to_stalk P (i z')
  let : Algebra k Rx := ((algebraMap P Rx).comp (algebraMap k P)).toAlgebra
  have : IsScalarTower k P Rx := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.FormallySmooth P Rx :=
    Algebra.FormallySmooth.of_isLocalization (i z').asIdeal.primeCompl
  have : Algebra.FormallySmooth k Rx := Algebra.FormallySmooth.comp k P Rx
  let : Algebra Rx Rz := (stalkHom i z').toAlgebra
  let : Algebra k Ry := StructureSheaf.stalkAlgebra k (p (i z'))
  let : Algebra Ry Rx := (stalkHom p (i z')).toAlgebra
  have hRyRx : ∀ r : k, algebraMap Ry Rx (algebraMap k Ry r) = algebraMap k Rx r := fun r =>
    stalkMap_toStalk_apply (CommRingCat.ofHom (algebraMap k P)) (i z') r
  have : IsScalarTower k Ry Rx := IsScalarTower.of_algebraMap_eq fun r => (hRyRx r).symm
  have hRxRz : ∀ x : P, algebraMap Rx Rz (algebraMap P Rx x) = algebraMap A' Rz (π x) := fun x =>
    stalkMap_toStalk_apply φ z' x
  have : IsScalarTower k Rx Rz := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap A' Rz (algebraMap k A' r) =
      algebraMap Rx Rz (algebraMap P Rx (algebraMap k P r))
    rw [hRxRz, AlgHom.commutes]
  -- `H¹(L_{C/k}) = 0`, as `B` is formally smooth over `k` and `K/K² → C ⊗_B Ω_{B/k}` is injective
  have hsurj : Function.Surjective (algebraMap Rx Rz) := i.stalkMap_surjective z'
  refine ⟨(Algebra.FormallySmooth.kerCotangentToTensor_injective_iff hsurj).mp
    (injective_kerCotangentToTensor_of_tower k Ry Rx Rz h1), ?_⟩
  -- `Ω_{C/k} ≅ Ω_{C/𝒪_{Spec k}}` is free
  let Ry' := ringSheafStalk (Spec (.of k)).sheaf ((i ≫ p) z')
  let : Algebra k Ry' := StructureSheaf.stalkAlgebra k ((i ≫ p) z')
  let : Algebra Ry' Rz := (stalkHom (i ≫ p) z').toAlgebra
  have : IsScalarTower k Ry' Rz := IsScalarTower.of_algebraMap_eq fun r => by
    have hc := congr($(Scheme.Hom.stalkMap_comp i p z') (toStalk k (p (i z')) r))
    refine Eq.trans ?_ hc.symm
    change algebraMap A' Rz (algebraMap k A' r) =
      algebraMap Rx Rz (algebraMap Ry Rx (algebraMap k Ry r))
    rw [hRyRx]
    change _ = algebraMap Rx Rz (algebraMap P Rx (algebraMap k P r))
    rw [hRxRz, AlgHom.commutes]
  have h2' : Module.Free Rz Ω[Rz⁄Ry'] := h2
  exact Module.Free.of_equiv (LinearEquiv.ofBijective (map k Ry' Rz Rz)
    (bijective_map_of_surjective k Ry' Rz (surjective_algebraMap_stalk ((i ≫ p) z')))).symm

end Affine

section Components

open AlgebraicGeometry

/-- If the localization `S = A_q` is a domain, every minimal prime `𝔭₀ ⊆ q` of `A` vanishes in
`A_q`: the kernel of `A → A_q` is a prime contained in `𝔭₀`, hence equal to it. -/
theorem exists_mul_eq_zero_of_mem_minimalPrimes {A : Type*} [CommRing A] {q 𝔭₀ : Ideal A}
    [q.IsPrime] (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.AtPrime S q] [IsDomain S]
    (h𝔭₀ : 𝔭₀ ∈ minimalPrimes A) (hle : 𝔭₀ ≤ q) {x : A} (hx : x ∈ 𝔭₀) :
    ∃ t ∉ q, t * x = 0 := by
  have h𝔭 : 𝔭₀.IsPrime := h𝔭₀.1.1
  have hker : RingHom.ker (algebraMap A S) ≤ 𝔭₀ := fun y hy => by
    obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl S y).mp hy
    refine (h𝔭.mem_or_mem (hc ▸ 𝔭₀.zero_mem : (c : A) * y ∈ 𝔭₀)).resolve_left fun h => ?_
    exact c.2 (hle h)
  have := h𝔭₀.2 ⟨RingHom.ker_isPrime (algebraMap A S), bot_le⟩ hker
  obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl S x).mp (this hx)
  exact ⟨c, c.2, hc⟩

/-- Let `𝔭₀` be an ideal of `A` which vanishes in `A_q` (`q = ` the preimage of a prime `z` of
`A/𝔭₀`). Then `(A/𝔭₀)_z` is also a localization of `A` at `q`. -/
theorem isLocalization_atPrime_of_quotient {A : Type*} [CommRing A] (𝔭₀ : Ideal A)
    (z : PrimeSpectrum (A ⧸ 𝔭₀))
    (hdie : ∀ x ∈ 𝔭₀, ∃ t ∉ z.asIdeal.comap (Ideal.Quotient.mk 𝔭₀), t * x = 0)
    (T : Type*) [CommRing T] [Algebra (A ⧸ 𝔭₀) T] [Algebra A T] [IsScalarTower A (A ⧸ 𝔭₀) T]
    [IsLocalization.AtPrime T z.asIdeal] :
    IsLocalization.AtPrime T (z.asIdeal.comap (Ideal.Quotient.mk 𝔭₀)) := by
  have hmap : ∀ y : A, algebraMap A T y = algebraMap (A ⧸ 𝔭₀) T (Ideal.Quotient.mk 𝔭₀ y) :=
    fun y => IsScalarTower.algebraMap_apply A (A ⧸ 𝔭₀) T y
  refine ⟨fun y => ?_, fun t => ?_, fun {x y} h => ?_⟩
  · rw [hmap]
    exact IsLocalization.map_units T (⟨_, y.2⟩ : z.asIdeal.primeCompl)
  · obtain ⟨⟨a', s'⟩, hs⟩ := IsLocalization.surj z.asIdeal.primeCompl t
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a'
    obtain ⟨s, hs'⟩ := Ideal.Quotient.mk_surjective (s' : A ⧸ 𝔭₀)
    refine ⟨(a, ⟨s, fun h => s'.2 (hs' ▸ h)⟩), ?_⟩
    simp only [hmap, hs']
    exact hs
  · rw [hmap, hmap] at h
    obtain ⟨c', hc'⟩ := IsLocalization.exists_of_eq (M := z.asIdeal.primeCompl) h
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (c' : A ⧸ 𝔭₀)
    have hmem : c * (x - y) ∈ 𝔭₀ := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_sub, hc, mul_sub, hc', sub_self]
    obtain ⟨t, ht, ht0⟩ := hdie _ hmem
    have hc0 : c ∉ z.asIdeal.comap (Ideal.Quotient.mk 𝔭₀) := fun h => c'.2 (hc ▸ h)
    refine ⟨⟨t * c, (Ideal.IsPrime.mul_notMem inferInstance ht hc0)⟩, ?_⟩
    change t * c * x = t * c * y
    linear_combination ht0

variable {k : Type u} [Field k] [IsAlgClosed k] {A : Type u} [CommRing A] [Algebra k A]
  [Algebra.FiniteType k A]

/-- **The local statements for a nonsingular affine scheme.** For `A` finitely generated over `k`
with `Spec A` nonsingular, and `q` a prime of `A`, we have `H¹(L_{A_q/k}) = 0` and `Ω_{A/k}` is free
at `q`. Choosing a minimal prime `𝔭₀ ⊆ q`, the integral closed subscheme `Spec A/𝔭₀` is a
nonsingular variety with the same local ring at `q`, and
`subsingleton_h1Cotangent_and_free_stalk` applies to it. -/
theorem subsingleton_h1Cotangent_and_mem_freeLocus {n : ℕ} (π : MvPolynomial (Fin n) k →ₐ[k] A)
    (hπ : Function.Surjective π) (hA : (Spec (.of A)).IsRegular) (q : PrimeSpectrum A) :
    Subsingleton (Algebra.H1Cotangent k (Localization.AtPrime q.asIdeal)) ∧
      q ∈ Module.freeLocus A Ω[A⁄k] := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  -- the local rings of `A` are regular domains, and minimal primes die in them
  have hdie : ∀ (q' : PrimeSpectrum A) (𝔭₀ : Ideal A), 𝔭₀ ∈ minimalPrimes A → 𝔭₀ ≤ q'.asIdeal →
      ∀ x ∈ 𝔭₀, ∃ t ∉ q'.asIdeal, t * x = 0 := fun q' 𝔭₀ h𝔭₀ hle x hx => by
    let _ : Algebra A ((Spec (.of A)).presheaf.stalk q') := StructureSheaf.stalkAlgebra A q'
    have : IsLocalization.AtPrime ((Spec (.of A)).presheaf.stalk q') q'.asIdeal :=
      StructureSheaf.IsLocalization.to_stalk A q'
    have : IsRegularLocalRing ((Spec (.of A)).presheaf.stalk q') := hA.2 q'
    have : IsDomain ((Spec (.of A)).presheaf.stalk q') := RegularLocal.isDomain _
    exact exists_mul_eq_zero_of_mem_minimalPrimes ((Spec (.of A)).presheaf.stalk q') h𝔭₀ hle hx
  -- a minimal prime `𝔭₀ ⊆ q` and the domain `A' = A/𝔭₀`
  obtain ⟨𝔭₀, h𝔭₀, hle⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ q.asIdeal)
  have : 𝔭₀.IsPrime := h𝔭₀.1.1
  let A' := A ⧸ 𝔭₀
  -- `A_{q'} ≅ A'_{q'}` for every prime `q' ⊇ 𝔭₀`
  have hloc : ∀ z : PrimeSpectrum A',
      letI : Algebra A' ((Spec (.of A')).presheaf.stalk z) := StructureSheaf.stalkAlgebra A' z
      letI : Algebra A ((Spec (.of A')).presheaf.stalk z) :=
        ((algebraMap A' _).comp (algebraMap A A')).toAlgebra
      IsLocalization.AtPrime ((Spec (.of A')).presheaf.stalk z)
        (z.asIdeal.comap (Ideal.Quotient.mk 𝔭₀)) := fun z => by
    let : Algebra A' ((Spec (.of A')).presheaf.stalk z) := StructureSheaf.stalkAlgebra A' z
    let : Algebra A ((Spec (.of A')).presheaf.stalk z) :=
      ((algebraMap A' _).comp (algebraMap A A')).toAlgebra
    have : IsScalarTower A A' ((Spec (.of A')).presheaf.stalk z) :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    have : IsLocalization.AtPrime ((Spec (.of A')).presheaf.stalk z) z.asIdeal :=
      StructureSheaf.IsLocalization.to_stalk A' z
    exact isLocalization_atPrime_of_quotient 𝔭₀ z
      (hdie (PrimeSpectrum.comap (Ideal.Quotient.mk 𝔭₀) z) 𝔭₀ h𝔭₀ fun x hx => by
        change Ideal.Quotient.mk 𝔭₀ x ∈ z.asIdeal
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
        exact z.asIdeal.zero_mem) _
  -- `Spec A'` is nonsingular
  have hZ : (Spec (.of A')).IsRegular := by
    refine ⟨inferInstance, fun z => ?_⟩
    let q' := PrimeSpectrum.comap (Ideal.Quotient.mk 𝔭₀) z
    let : Algebra A' ((Spec (.of A')).presheaf.stalk z) := StructureSheaf.stalkAlgebra A' z
    let : Algebra A ((Spec (.of A')).presheaf.stalk z) :=
      ((algebraMap A' _).comp (algebraMap A A')).toAlgebra
    have : IsLocalization.AtPrime ((Spec (.of A')).presheaf.stalk z) q'.asIdeal := hloc z
    let _ : Algebra A ((Spec (.of A)).presheaf.stalk q') := StructureSheaf.stalkAlgebra A q'
    have : IsLocalization.AtPrime ((Spec (.of A)).presheaf.stalk q') q'.asIdeal :=
      StructureSheaf.IsLocalization.to_stalk A q'
    have : IsRegularLocalRing ((Spec (.of A)).presheaf.stalk q') := hA.2 q'
    exact IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv q'.asIdeal.primeCompl
      ((Spec (.of A)).presheaf.stalk q') ((Spec (.of A')).presheaf.stalk z)).toRingEquiv
  -- the point `z` of `Spec A'` over `q`
  obtain ⟨z, rfl⟩ : q ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk 𝔭₀)) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
      Ideal.mk_ker]
    exact hle
  let π' : MvPolynomial (Fin n) k →ₐ[k] A' := (Ideal.Quotient.mkₐ k 𝔭₀).comp π
  have hπ' : Function.Surjective π' := Ideal.Quotient.mk_surjective.comp hπ
  obtain ⟨hH1, hfree⟩ := subsingleton_h1Cotangent_and_free_stalk π' hπ' hZ z
  let T := (Spec (.of A')).presheaf.stalk z
  let : Algebra A' T := StructureSheaf.stalkAlgebra A' z
  let : Algebra A T := ((algebraMap A' T).comp (algebraMap A A')).toAlgebra
  let : Algebra k T := ((algebraMap A' T).comp (algebraMap k A')).toAlgebra
  have : IsScalarTower k A T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsLocalization.AtPrime T (z.asIdeal.comap (Ideal.Quotient.mk 𝔭₀)) := hloc z
  refine ⟨?_, ?_⟩
  · let e : Localization.AtPrime (z.asIdeal.comap (Ideal.Quotient.mk 𝔭₀)) ≃ₐ[k] T :=
      (IsLocalization.algEquiv (z.asIdeal.comap (Ideal.Quotient.mk 𝔭₀)).primeCompl
        (Localization.AtPrime (z.asIdeal.comap (Ideal.Quotient.mk 𝔭₀))) T).restrictScalars k
    have : Subsingleton (Algebra.H1Cotangent k T) := hH1
    exact (Algebra.H1Cotangent.mapEquiv k _ _ e).toEquiv.subsingleton
  · have hfree' : Module.Free T Ω[T⁄k] := hfree
    have : IsLocalization.AtPrime T (PrimeSpectrum.comap (Ideal.Quotient.mk 𝔭₀) z).asIdeal := hloc z
    exact (Module.mem_freeLocus_of_isLocalization (PrimeSpectrum.comap (Ideal.Quotient.mk 𝔭₀) z)
      T Ω[T⁄k] (KaehlerDifferential.map k k A T)).mpr hfree'

end Components

section Main

open AlgebraicGeometry

variable {k A : Type u} [Field k] [IsAlgClosed k] [CommRing A] [Algebra k A]
  [Algebra.FiniteType k A]

/-- **Hartshorne II, Exercise 8.6** (the infinitesimal lifting property). Let `k` be an
algebraically closed field and `A` a finitely generated `k`-algebra such that `Spec A` is
nonsingular. Let `g : B' → B` be a surjection of `k`-algebras whose kernel `I` satisfies
`I² = 0`, and let `f : A → B` be a `k`-algebra homomorphism. Then there is a `k`-algebra
homomorphism `f' : A → B'` with `g ∘ f' = f`.

This generalizes Hartshorne's statement, which asks for `Spec A` to be a nonsingular variety:
here `Spec A` is only assumed regular at every point, not irreducible. -/
theorem exists_lift_of_isRegular (hA : (Spec (CommRingCat.of A)).IsRegular)
    {B' B : Type v} [CommRing B'] [CommRing B] [Algebra k B'] [Algebra k B]
    (g : B' →ₐ[k] B) (hg : Function.Surjective g) (hI : RingHom.ker g ^ 2 = ⊥)
    (f : A →ₐ[k] B) :
    ∃ f' : A →ₐ[k] B', g.comp f' = f := by
  -- (b) a presentation `A = P/J` with `P = k[x_1, …, x_n]`
  obtain ⟨n, π, hπ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹_›
  -- Theorems 8.17 and 8.15 at every prime of `A`
  have hloc := subsingleton_h1Cotangent_and_mem_freeLocus (k := k) π hπ hA
  -- `J/J² → A ⊗_P Ω_{P/k}` is injective, as `H¹(L_{A/k})` vanishes locally
  have hH1 : Subsingleton (Algebra.H1Cotangent k A) :=
    Module.subsingleton_of_localization_maximal
      (fun P _ => Algebra.H1Cotangent k (Localization.AtPrime P))
      (fun P _ => Algebra.H1Cotangent.map k k A (Localization.AtPrime P))
      fun P hP => (hloc ⟨P, hP.isPrime⟩).1
  let : Algebra (MvPolynomial (Fin n) k) A := π.toRingHom.toAlgebra
  have : IsScalarTower k (MvPolynomial (Fin n) k) A :=
    IsScalarTower.of_algebraMap_eq' π.comp_algebraMap.symm
  have hinj := (Algebra.FormallySmooth.kerCotangentToTensor_injective_iff hπ).mpr hH1
  -- `Ω_{A/k}` is projective, as it is locally free
  have hproj : Module.Projective A Ω[A⁄k] := by
    have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
    have : Module.FinitePresentation A Ω[A⁄k] := Module.finitePresentation_of_finite A _
    exact Module.freeLocus_eq_univ_iff.mp (Set.eq_univ_of_forall fun q => (hloc q).2)
  -- (c)
  exact exists_lift_of_presentation g π hπ hinj hproj hg hI f

/-- **Hartshorne II, Exercise 8.6** (p.188), in the book's setting. Let `k` be an algebraically
closed field and `A` a finitely generated `k`-algebra such that `Spec A` is a nonsingular variety
over `k`: `A` is a domain and every local ring of `Spec A` is regular. Let `g : B' → B` be a
surjection of `k`-algebras whose kernel `I` satisfies `I² = 0`, and let `f : A → B` be a
`k`-algebra homomorphism. Then there is a `k`-algebra homomorphism `f' : A → B'` with
`g ∘ f' = f`.

The domain hypothesis is the book's (`Spec A` is a variety) and is not used by the proof; see
`exists_lift_of_isRegular`. -/
@[nolint unusedArguments]
theorem exists_lift_of_isDomain_of_isRegular [IsDomain A]
    (hA : (Spec (CommRingCat.of A)).IsRegular)
    {B' B : Type v} [CommRing B'] [CommRing B] [Algebra k B'] [Algebra k B]
    (g : B' →ₐ[k] B) (hg : Function.Surjective g) (hI : RingHom.ker g ^ 2 = ⊥)
    (f : A →ₐ[k] B) :
    ∃ f' : A →ₐ[k] B', g.comp f' = f :=
  exists_lift_of_isRegular hA g hg hI f

end Main

end AffineNonsingularLifting

end Hartshorne

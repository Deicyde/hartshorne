/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.SmoothMorphisms.CotangentRelativeDifferentials
import Hartshorne.Cohomology.Semicontinuity.CoherentFiberDimension
import Hartshorne.Scheme.Differentials.RelativeDifferentialsAffineFibre
import Hartshorne.Scheme.Differentials.ClosedImmersionConormalSequence
import Hartshorne.Cohomology.FlatFamilies.NormalFamilyFlat
import Hartshorne.Cohomology.SmoothMorphisms.HartshorneSmoothnessCriterion
import Hartshorne.Cohomology.SmoothMorphisms.RegularCotangentFlat
import Hartshorne.Cohomology.SmoothMorphisms.SmoothOverAlgClosedRegular
import Hartshorne.Scheme.Differentials.DifferentialsCharacterizeNonsingular
import Hartshorne.Scheme.Differentials.RelativeDifferentialsFibreRank
import Hartshorne.Scheme.Differentials.RegularLocalDifferentialCriterion
import Hartshorne.Scheme.DimensionAtClosedPoint
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Flat.Localization

/-!
# Smoothness by tangent-map surjectivity: scheme-level glue

Hartshorne, *Algebraic Geometry*, III, Proposition 10.4 (pp. 270–271).

## Main results

* `Hartshorne.SmoothTangent.smoothOfRelativeDimension_tfae_of_isRegularAt`: Proposition 10.4,
  the equivalence of smoothness of relative dimension `n`, local freeness of rank `n` of
  `Ω_{X/Y}`, and surjectivity of the tangent maps at closed points.
* `Hartshorne.SmoothTangent.moduleFiberDim_relativeDifferentials_eq_finrank_cotangentSpace`:
  II.8.7 at a closed point of a scheme over an algebraically closed field, `Ω_{Z/k} ⊗ k(z)` and
  `𝔪_z/𝔪_z²` have the same dimension.
* `Hartshorne.SmoothTangent.finrank_cotangentSpace_eq_of_isRegularAt`: a nonsingular variety of
  dimension `d` is smooth over `k`, so its cotangent spaces at closed points have dimension `d`.
* `Hartshorne.SmoothTangent.injective_localCotangentBaseChange_iff_of_isClosed`: at a closed
  point, injectivity of the cotangent map is the dimension count with the fibre of `Ω_{X/Y}`.
* `Hartshorne.SmoothTangent.le_finrank_kaehler_genericPoint`: by II.8.6A,
  `dim Ω_{K(X)/K(Y)} ≥ tr.deg K(X)/K(Y) = dim X - dim Y` for a morphism preserving generic points.
* `Hartshorne.SmoothTangent.finrank_fibre_relativeDifferentials_eq_stalk`: the fibre of `Ω_{X/Y}`
  at `x` has the dimension of `κ(x) ⊗ Ω_{𝒪_{X,x}/𝒪_{Y,f x}}`.
* `Hartshorne.SmoothTangent.moduleFiberDim_relativeDifferentials_eq_of_specializes`: if `z ⤳ x`,
  the fibre of `Ω_{X/Y}` at `z` is computed from `Ω_{𝒪_{X,x}/𝒪_{Y,f x}}`.
* `Hartshorne.SmoothTangent.stalk_kaehler_transitivity_exact`: the stalk at `x` of the exact
  sequence `f^*Ω_{Y/S} → Ω_{X/S} → Ω_{X/Y} → 0` of II.8.11 is the sequence
  `𝒪_{X,x} ⊗ Ω_{𝒪_{Y,f x}/𝒪_{S,s}} → Ω_{𝒪_{X,x}/𝒪_{S,s}} → Ω_{𝒪_{X,x}/𝒪_{Y,f x}}`, which is
  therefore exact.
* `Hartshorne.SmoothTangent.stalk_exact_of_isColimit`: on a ringed space, the stalk functor carries
  a cokernel presentation of modules to an exact sequence.

## Proof

We follow Hartshorne's proof.

* (1) ⇒ (2) is Example 10.0.2.
* (2) ⇒ (3): `X` and `Y` are smooth over `k` (Example 10.0.3), so `Ω_{X/k}` and `Ω_{Y/k}` are
  locally free of ranks `dim X` and `dim Y` (Example 10.0.2), and by II.8.7 the cotangent spaces
  at closed points have these dimensions. At a closed point `x` the fibre of the exact sequence
  `f^*Ω_{Y/k} → Ω_{X/k} → Ω_{X/Y} → 0` of II.8.11 is, after the identifications of II.8.7, the
  exact sequence `k(x) ⊗ 𝔪_y/𝔪_y² → 𝔪_x/𝔪_x² → Ω_{X/Y} ⊗ k(x) → 0`. Concretely: the stalk
  functor preserves cokernels, so the stalk at `x` of the sequence of II.8.11
  (`AlgebraicGeometry.Scheme.relativeDifferentialsTransitivityIsColimit`) is exact; it is
  identified with the sequence of Kähler modules of the local rings
  (`stalk_kaehler_transitivity_exact`); tensoring with `k(x)` (right exactness) and the
  identifications of II.8.7 give the cotangent sequence
  (`Hartshorne.CotangentKaehler.injective_localCotangentBaseChange_iff`). Counting dimensions,
  the cotangent map is injective, so the tangent map is surjective.
* (3) ⇒ (1): reversing the count, `Ω_{X/Y} ⊗ k(x)` has dimension `n` at every closed point.
  At each closed point a regular system of parameters of `𝒪_{Y,y}` maps to part of one of
  `𝒪_{X,x}`, and Lemma 10.3A applied along it shows that `f` is flat
  (`Hartshorne.RegularCotangentFlat.flat_stalkMap_of_surjective_zariskiTangentMap`). So `f` sends
  the generic point of `X` to that of `Y`, and by II.8.6A the generic fibre `Ω_{K(X)/K(Y)}` has
  dimension at least `tr.deg K(X)/K(Y) = n`; here it is at most `n` by upper semicontinuity of
  the fibre dimension (the value at a closed point). By II.8.9, `Ω_{𝒪_{X,x}/𝒪_{Y,y}}`
  is free of rank `n` at every closed point, so every fibre of `Ω_{X/Y}`
  has dimension `n`, and `f` is smooth of relative dimension `n`.
-/

namespace Hartshorne

-- A definitionally equal duplicate of `schemeModulesStalkModule`, the instance used by
-- `moduleFiberDim`; erased so that the fibre-dimension lemmas below apply syntactically.
attribute [-instance] moduleSheafStalkModule

noncomputable section

open IsLocalRing Module KaehlerDifferential CategoryTheory AlgebraicGeometry
open scoped TensorProduct

universe u

namespace SmoothTangent

section Algebra

variable {R T A B : Type u} [CommRing R] [CommRing T] [CommRing A] [CommRing B] [IsLocalRing B]
  [Algebra R T] [Algebra T B] [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R T B]
  [IsScalarTower R A B]

omit [IsLocalRing B] [Algebra R T] [Algebra T B] [IsScalarTower R T B] in
/-- If `Ω_{A/R} = 0`, then `Ω_{B/R} → Ω_{B/A}` is injective. -/
theorem map_injective_of_subsingleton [Subsingleton Ω[A⁄R]] :
    Function.Injective (KaehlerDifferential.map R A B B) := by
  rw [injective_iff_map_eq_zero]
  intro ω hω
  have ht : ∀ t : B ⊗[A] Ω[A⁄R], t = 0 := fun t ↦ by
    induction t using TensorProduct.induction_on with
    | zero => rfl
    | tmul b η => rw [Subsingleton.elim η 0, TensorProduct.tmul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  obtain ⟨t, rfl⟩ := (KaehlerDifferential.exact_mapBaseChange_map R A B ω).mp hω
  rw [ht t, map_zero]

omit [IsLocalRing B] in
/-- Let `B` be a localization of an `R`-algebra `T`, and let `B` be an algebra over an `R`-algebra
`A` with `Ω_{A/R} = 0`. Then `B ⊗_T Ω_{T/R} ≅ Ω_{B/A}`, so the two have the same dimension. -/
theorem finrank_tensor_kaehler_eq_finrank_of_isLocalization (M : Submonoid T)
    [IsLocalization M B] [Subsingleton Ω[A⁄R]] :
    finrank B (B ⊗[T] Ω[T⁄R]) = finrank B Ω[B⁄A] := by
  have hbc : IsBaseChange B (KaehlerDifferential.map R R T B) :=
    (isLocalizedModule_iff_isBaseChange M B _).mp inferInstance
  exact (hbc.equiv.trans (LinearEquiv.ofBijective (KaehlerDifferential.map R A B B)
    ⟨map_injective_of_subsingleton, KaehlerDifferential.map_surjective R A B⟩)).finrank_eq

/-- Let `B = T_q` be a localization of an `R`-algebra `T` at a prime `q`, and let `B` be an algebra
over an `R`-algebra `A` with `Ω_{A/R} = 0` (for instance a localization of `R`). Then
`dim κ(q) ⊗_T Ω_{T/R} = dim κ_B ⊗_B Ω_{B/A}`. -/
theorem finrank_tensor_kaehler_eq_of_isLocalization (q : Ideal T) [q.IsPrime]
    [IsLocalization.AtPrime B q] [Subsingleton Ω[A⁄R]] :
    finrank q.ResidueField (q.ResidueField ⊗[T] Ω[T⁄R]) =
      finrank (ResidueField B) (ResidueField B ⊗[B] Ω[B⁄A]) := by
  -- `Ω_{B/R} ≅ Ω_{B/A}`
  let e₁ : Ω[B⁄R] ≃ₗ[B] Ω[B⁄A] := LinearEquiv.ofBijective (KaehlerDifferential.map R A B B)
    ⟨map_injective_of_subsingleton, KaehlerDifferential.map_surjective R A B⟩
  -- `B ⊗_T Ω_{T/R} ≅ Ω_{B/R}`
  have : IsLocalization q.primeCompl B := ‹IsLocalization.AtPrime B q›
  have hbc : IsBaseChange B (KaehlerDifferential.map R R T B) :=
    (isLocalizedModule_iff_isBaseChange q.primeCompl B _).mp inferInstance
  let e₂ : ResidueField B ⊗[B] Ω[B⁄A] ≃ₗ[ResidueField B] ResidueField B ⊗[T] Ω[T⁄R] :=
    (TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl (ResidueField B) (ResidueField B)) (hbc.equiv.trans e₁).symm).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange T B (ResidueField B) (ResidueField B)
        Ω[T⁄R])
  -- the residue field of `T_q` maps to that of `B`
  let e := IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) B
  let φ : Localization.AtPrime q →+* B := e.toRingEquiv.toRingHom
  have : IsLocalHom φ := ⟨fun a ha ↦ by
    have := ha.map (e.symm.toRingEquiv.toRingHom)
    simpa [φ] using this⟩
  let ψ : q.ResidueField →+* ResidueField B := ResidueField.map φ
  let : Algebra q.ResidueField (ResidueField B) := ψ.toAlgebra
  have : IsScalarTower T q.ResidueField (ResidueField B) := IsScalarTower.of_algebraMap_eq
    fun t ↦ by
      change residue B (algebraMap T B t) = ψ (residue _ (algebraMap T (Localization.AtPrime q) t))
      rw [ResidueField.map_residue]
      exact congrArg (residue B) (e.commutes t).symm
  let e₃ : ResidueField B ⊗[q.ResidueField] (q.ResidueField ⊗[T] Ω[T⁄R]) ≃ₗ[ResidueField B]
      ResidueField B ⊗[T] Ω[T⁄R] :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange T q.ResidueField (ResidueField B)
      (ResidueField B) Ω[T⁄R]
  have hbase : finrank (ResidueField B)
      (ResidueField B ⊗[q.ResidueField] (q.ResidueField ⊗[T] Ω[T⁄R])) =
      finrank q.ResidueField (q.ResidueField ⊗[T] Ω[T⁄R]) := Module.finrank_baseChange
  rw [e₂.finrank_eq, ← e₃.finrank_eq, hbase]

omit [IsLocalRing B] in
/-- Let `R → T` with `Ω_{T/R} = 0`, and let `T → A → B`. If `B ⊗_A Ω_{A/T} → Ω_{B/T} → Ω_{B/A}` is
exact, then so is `B ⊗_A Ω_{A/R} → Ω_{B/R} → Ω_{B/A}`. -/
theorem exact_mapBaseChange_map_of_subsingleton [Algebra T A] [IsScalarTower R T A]
    [IsScalarTower T A B] [Subsingleton Ω[T⁄R]]
    (h : Function.Exact (mapBaseChange T A B) (map T A B B)) :
    Function.Exact (mapBaseChange R A B) (map R A B B) := by
  -- `Ω_{B/R} → Ω_{B/T}` is injective, and compatible with the maps to `Ω_{B/A}`
  have hinj : Function.Injective (map R T B B) := map_injective_of_subsingleton
  have hmap : ∀ ω, map T A B B (map R T B B ω) = map R A B B ω := fun ω ↦ by
    have hω : ω ∈ Submodule.span B (Set.range (D R B)) := by
      rw [span_range_derivation]; trivial
    induction hω using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨b, rfl⟩ := h
      simp only [map_D, Algebra.algebraMap_self, RingHom.id_apply]
    | zero => simp only [map_zero]
    | add x y _ _ hx hy => rw [map_add, map_add, map_add, hx, hy]
    | smul c x _ hx => rw [map_smul, map_smul, map_smul, hx]
  -- and with the maps from `B ⊗_A Ω_{A/R}` and `B ⊗_A Ω_{A/T}`
  have hbc : ∀ u, map R T B B (mapBaseChange R A B u) =
      mapBaseChange T A B ((map R T A A).lTensor B u) := fun u ↦ by
    induction u using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul b α =>
      have hα : α ∈ Submodule.span A (Set.range (D R A)) := by
        rw [span_range_derivation]; trivial
      induction hα using Submodule.span_induction generalizing b with
      | mem _ h =>
        obtain ⟨a, rfl⟩ := h
        rw [LinearMap.lTensor_tmul, mapBaseChange_tmul, mapBaseChange_tmul, map_smul]
        simp only [map_D, Algebra.algebraMap_self, RingHom.id_apply]
      | zero => simp only [TensorProduct.tmul_zero, map_zero]
      | add x y _ _ hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
      | smul a x _ h => rw [← TensorProduct.smul_tmul, h]
    | add u v hu hv => rw [map_add, map_add, map_add, map_add, hu, hv]
  intro ω
  constructor
  · intro hω
    obtain ⟨u', hu'⟩ := (h (map R T B B ω)).mp (by rw [hmap, hω])
    obtain ⟨u, rfl⟩ := LinearMap.lTensor_surjective B (map_surjective R T A) u'
    exact ⟨u, hinj (by rw [hbc, hu'])⟩
  · rintro ⟨u, rfl⟩
    rw [← hmap, hbc]
    exact (h _).mpr ⟨_, rfl⟩

end Algebra

section StalkTransitivity

open Ringed ModuleSheafTensor ClosedConormal CategoryTheory.Limits Scheme

/-- On a ringed space, the stalk functor at a point carries a cokernel presentation
`M ⟶ N ⟶ P ⟶ 0` of `𝒪_X`-modules to an exact sequence of `𝒪_{X,x}`-modules: the stalk functor is
a left adjoint, so it preserves cokernels. -/
theorem stalk_exact_of_isColimit {T : TopCat.{u}}
    {R : Sheaf (Opens.grothendieckTopology T) CommRingCat.{u}} (x : T)
    {M N P : SheafOfModules.{u} (ringCatSheafOf R)} {φ : M ⟶ N} {ψ : N ⟶ P} (w : φ ≫ ψ = 0)
    (hc : IsColimit (CokernelCofork.ofπ ψ w)) :
    Function.Exact ((moduleStalkFunctor x).map φ) ((moduleStalkFunctor x).map ψ) ∧
      Function.Surjective ((moduleStalkFunctor x).map ψ) := by
  have := (moduleStalkSkyscraperAdjunction (R := R) x).isLeftAdjoint
  have := (moduleStalkSkyscraperAdjunction (R := R) x).leftAdjoint_preservesColimits
  let S := ShortComplex.mk ((moduleStalkFunctor x).map φ) ((moduleStalkFunctor x).map ψ)
    (by rw [← Functor.map_comp, w, Functor.map_zero])
  obtain ⟨hS, hepi⟩ := S.exact_and_epi_g_iff_g_is_cokernel.mpr
    ⟨CokernelCofork.mapIsColimit _ hc (moduleStalkFunctor x)⟩
  exact ⟨(ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS,
    (ModuleCat.epi_iff_surjective _).mp hepi⟩

/-- On stalks, the map `Ω_{X/S} ⟶ Ω_{X/Y}` of II.8.11 sends `(d s)_x` to `(d s)_x`. -/
theorem map_stalkD_relativeDifferentialsCompToLeft {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    (x : X) (r : ringSheafStalk X.sheaf x) :
    (moduleStalkFunctor (R := X.sheaf) x).map (relativeDifferentialsCompToLeft f g)
      (stalkD (f ≫ g) x r) = stalkD f x r := by
  obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.sheaf.obj r
  erw [stalkD_germ, stalkD_germ]
  unfold germD
  erw [moduleStalkFunctor_map_germ, relativeDifferentialsCompToLeft_d]

/-- **The stalk of the exact sequence of Hartshorne II, Proposition 8.11.** For morphisms
`f : X ⟶ Y` and `g : Y ⟶ S` and a point `x ∈ X`, put `A = 𝒪_{S,g(f x)}`, `B = 𝒪_{Y,f x}` and
`C = 𝒪_{X,x}`. Then `C ⊗_B Ω_{B/A} → Ω_{C/A} → Ω_{C/B}` is exact.

This is deduced from the sheaf-level sequence `f^*Ω_{Y/S} ⟶ Ω_{X/S} ⟶ Ω_{X/Y} ⟶ 0`
(`relativeDifferentialsTransitivityIsColimit`): its stalk at `x` is exact, and it is compared with
the algebraic sequence by `1 ⊗ db ↦ (f^* d b)_x`, which is surjective, and `dc ↦ (d c)_x`, which
is injective for both `Ω_{C/A}` and `Ω_{C/B}`. -/
theorem stalk_kaehler_transitivity_exact {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (x : X) :
    letI := (f.stalkMap x).hom.toAlgebra
    letI := (g.stalkMap (f x)).hom.toAlgebra
    letI : Algebra (S.presheaf.stalk (g (f x))) (X.presheaf.stalk x) :=
      ((f.stalkMap x).hom.comp (g.stalkMap (f x)).hom).toAlgebra
    haveI : IsScalarTower (S.presheaf.stalk (g (f x))) (Y.presheaf.stalk (f x))
        (X.presheaf.stalk x) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    Function.Exact
      (mapBaseChange (S.presheaf.stalk (g (f x))) (Y.presheaf.stalk (f x)) (X.presheaf.stalk x))
      (map (S.presheaf.stalk (g (f x))) (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
        (X.presheaf.stalk x)) := by
  let A := ringSheafStalk S.sheaf (g (f x))
  let B := ringSheafStalk Y.sheaf (f x)
  let C := ringSheafStalk X.sheaf x
  let _ : Algebra B C := (stalkHom f x).toAlgebra
  let _ : Algebra A B := (stalkHom g (f x)).toAlgebra
  let _ : Algebra A C := ((stalkHom f x).comp (stalkHom g (f x))).toAlgebra
  have _ : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  -- the stalk at `x` of the exact sequence `f^*Ω_{Y/S} ⟶ Ω_{X/S} ⟶ Ω_{X/Y} ⟶ 0` of II.8.11
  have hex := (stalk_exact_of_isColimit (R := X.sheaf) x _
    (relativeDifferentialsTransitivityIsColimit f g)).1
  let T1 := (moduleStalkFunctor (R := X.sheaf) x).obj
    ((Modules.pullback f).obj (relativeDifferentials g))
  let T2 := (moduleStalkFunctor (R := X.sheaf) x).obj (relativeDifferentials (f ≫ g))
  let T3 := (moduleStalkFunctor (R := X.sheaf) x).obj (relativeDifferentials f)
  let _ : Module B T1 := Module.compHom T1 (stalkHom f x)
  have _ : IsScalarTower B C T1 := ⟨fun a b c ↦ mul_smul (stalkHom f x a) b c⟩
  let _ : Module A T1 := Module.compHom T1 (algebraMap A C)
  have _ : IsScalarTower A B T1 := ⟨fun a b c ↦ by
    change (stalkHom f x (stalkHom g (f x) a * b)) • c =
      (stalkHom f x (stalkHom g (f x) a)) • (stalkHom f x b • c)
    rw [map_mul, mul_smul]⟩
  let _ : Module A T2 := Module.compHom T2 (algebraMap A C)
  have _ : IsScalarTower A C T2 := ⟨fun a b c ↦ mul_smul (algebraMap A C a) b c⟩
  let _ : Module B T3 := Module.compHom T3 (algebraMap B C)
  have _ : IsScalarTower B C T3 := ⟨fun a b c ↦ mul_smul (algebraMap B C a) b c⟩
  -- the sections `d (g^♯ t)` and `d (f^♯ t)` vanish
  have hk1 : ∀ a : A, stalkUnitD f g x (algebraMap A B a) = 0 := fun a ↦ by
    obtain ⟨V, hV, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq S.sheaf.obj a
    erw [Scheme.Hom.germ_stalkMap_apply]
    exact stalkUnitD_app f g x V t hV
  have hk2 : ∀ a : A, stalkD (f ≫ g) x (algebraMap A C a) = 0 := fun a ↦ by
    obtain ⟨V, hV, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq S.sheaf.obj a
    erw [stalkHom_stalkHom_germ f g x V t hV]
    exact stalkD_app (f ≫ g) x V t hV
  have hk3 : ∀ b : B, stalkD f x (algebraMap B C b) = 0 := fun b ↦ by
    obtain ⟨V, hV, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq Y.sheaf.obj b
    erw [Scheme.Hom.germ_stalkMap_apply]
    exact stalkD_app f x V t hV
  -- the derivations `B → (f^*Ω_{Y/S})_x`, `C → (Ω_{X/S})_x` and `C → (Ω_{X/Y})_x`
  let D1 : Derivation A B T1 := Derivation.mk'
    { toFun := stalkUnitD f g x
      map_add' := stalkUnitD_add f g x
      map_smul' := fun a r ↦ by
        change stalkUnitD f g x (algebraMap A B a * r) = algebraMap A C a • _
        rw [stalkUnitD_mul, hk1, smul_zero, add_zero]
        rfl }
    (stalkUnitD_mul f g x)
  let D2 : Derivation A C T2 := Derivation.mk'
    { toFun := stalkD (f ≫ g) x
      map_add' := stalkD_add (f ≫ g) x
      map_smul' := fun a r ↦ by
        change stalkD (f ≫ g) x (algebraMap A C a * r) = algebraMap A C a • _
        rw [stalkD_mul, hk2, smul_zero, add_zero] }
    (stalkD_mul (f ≫ g) x)
  let D3 : Derivation B C T3 := Derivation.mk'
    { toFun := stalkD f x
      map_add' := stalkD_add f x
      map_smul' := fun b r ↦ by
        change stalkD f x (algebraMap B C b * r) = algebraMap B C b • _
        rw [stalkD_mul, hk3, smul_zero, add_zero] }
    (stalkD_mul f x)
  let φ1 : C ⊗[B] Ω[B⁄A] →ₗ[C] T1 := D1.liftKaehlerDifferential.liftBaseChange C
  let φ2 : Ω[C⁄A] →ₗ[C] T2 := D2.liftKaehlerDifferential
  let φ3 : Ω[C⁄B] →ₗ[C] T3 := D3.liftKaehlerDifferential
  let p := ((moduleStalkFunctor (R := X.sheaf) x).map
    (pullbackRelativeDifferentialsToComp f g)).hom
  let q := ((moduleStalkFunctor (R := X.sheaf) x).map (relativeDifferentialsCompToLeft f g)).hom
  -- the comparison squares commute
  have hcomm1 : ∀ w, p (φ1 w) = φ2 (mapBaseChange A B C w) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero, map_zero]
    | tmul c ω =>
      have hω : ω ∈ Submodule.span B (Set.range (D A B)) := by
        rw [span_range_derivation]; trivial
      induction hω using Submodule.span_induction generalizing c with
      | mem _ h =>
        obtain ⟨r, rfl⟩ := h
        rw [LinearMap.liftBaseChange_tmul, mapBaseChange_tmul, map_smul, map_smul, map_D,
          Derivation.liftKaehlerDifferential_comp_D, Derivation.liftKaehlerDifferential_comp_D]
        exact congrArg (c • ·) (map_stalkUnitD f g x r)
      | zero => rw [TensorProduct.tmul_zero, map_zero, map_zero, map_zero, map_zero]
      | add x y _ _ hx hy => rw [TensorProduct.tmul_add, map_add, map_add, hx, hy, map_add, map_add]
      | smul r ω _ h => rw [← TensorProduct.smul_tmul, h]
    | add w w' hw hw' => rw [map_add, map_add, hw, hw', map_add, map_add]
  have hcomm2 : ∀ ω, q (φ2 ω) = φ3 (map A B C C ω) := by
    intro ω
    have hω : ω ∈ Submodule.span C (Set.range (D A C)) := by
      rw [span_range_derivation]; trivial
    induction hω using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨r, rfl⟩ := h
      rw [map_D, Derivation.liftKaehlerDifferential_comp_D,
        Derivation.liftKaehlerDifferential_comp_D]
      exact map_stalkD_relativeDifferentialsCompToLeft f g x r
    | zero => rw [map_zero, map_zero, map_zero, map_zero]
    | add x y _ _ hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
    | smul r ω _ h => rw [map_smul, map_smul, map_smul, map_smul, h]
  -- `C ⊗_B Ω_{B/A} ⟶ (f^*Ω_{Y/S})_x` is surjective
  have hφ1 : Function.Surjective φ1 := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← span_germUnitD f g x, Submodule.span_le]
    rintro _ ⟨U, hU, s, rfl⟩
    refine ⟨1 ⊗ₜ D A B (TopCat.Presheaf.germ Y.sheaf.obj U (f x) hU s), ?_⟩
    rw [LinearMap.liftBaseChange_tmul, one_smul, Derivation.liftKaehlerDifferential_comp_D]
    exact stalkUnitD_germ f g x U hU s
  -- `Ω_{C/A} ⟶ (Ω_{X/S})_x` and `Ω_{C/B} ⟶ (Ω_{X/Y})_x` are injective
  have hφ2 : Function.Injective φ2 := by
    obtain ⟨b, hb⟩ := exists_stalkD_inverse (f ≫ g) x (A := A) fun V t hz ↦ by
      erw [← stalkHom_stalkHom_germ f g x V t hz]
      exact (D A C).map_algebraMap _
    refine Function.LeftInverse.injective (g := b) fun ω ↦ ?_
    have hω : ω ∈ Submodule.span C (Set.range (D A C)) := by
      rw [span_range_derivation]; trivial
    induction hω using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨r, rfl⟩ := h
      obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.sheaf.obj r
      rw [Derivation.liftKaehlerDifferential_comp_D]
      exact (congrArg b (stalkD_germ (f ≫ g) x U hU s)).trans (hb U hU s)
    | zero => rw [map_zero, map_zero]
    | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
    | smul r x _ h => rw [map_smul, map_smul, h]
  have hφ3 : Function.Injective φ3 := by
    obtain ⟨b, hb⟩ := exists_stalkD_inverse f x (A := B) fun V t hz ↦ by
      erw [← Scheme.Hom.germ_stalkMap_apply f V x hz t]
      exact (D B C).map_algebraMap _
    refine Function.LeftInverse.injective (g := b) fun ω ↦ ?_
    have hω : ω ∈ Submodule.span C (Set.range (D B C)) := by
      rw [span_range_derivation]; trivial
    induction hω using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨r, rfl⟩ := h
      obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.sheaf.obj r
      rw [Derivation.liftKaehlerDifferential_comp_D]
      exact (congrArg b (stalkD_germ f x U hU s)).trans (hb U hU s)
    | zero => rw [map_zero, map_zero]
    | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
    | smul r x _ h => rw [map_smul, map_smul, h]
  change Function.Exact (mapBaseChange A B C) (map A B C C)
  intro ω
  constructor
  · intro hω
    obtain ⟨t, ht⟩ := (hex (φ2 ω)).mp (by change q (φ2 ω) = 0; rw [hcomm2, hω, map_zero])
    obtain ⟨w, rfl⟩ := hφ1 t
    exact ⟨w, hφ2 (by rw [← hcomm1]; exact ht)⟩
  · rintro ⟨w, rfl⟩
    apply hφ3
    rw [← hcomm2, ← hcomm1, map_zero]
    exact (hex _).mpr ⟨_, rfl⟩

end StalkTransitivity

section Scheme

/-- In an irreducible space, every irreducible component is the whole space. -/
theorem eq_univ_of_mem_irreducibleComponents {S : Type*} [TopologicalSpace S] [IrreducibleSpace S]
    {C : Set S} (hC : C ∈ irreducibleComponents S) : C = Set.univ :=
  Set.eq_univ_of_univ_subset (hC.2 (IrreducibleSpace.isIrreducible_univ S) (Set.subset_univ C))

/-- The fibre of `Ω_{X/Y}` at `x` has the dimension of `κ(x) ⊗ Ω_{𝒪_{X,x}/𝒪_{Y,f x}}`. -/
theorem finrank_fibre_relativeDifferentials_eq_stalk {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    letI := (f.stalkMap x).hom.toAlgebra
    finrank (ResidueField (X.presheaf.stalk x))
        (ResidueField (X.presheaf.stalk x) ⊗[X.presheaf.stalk x]
          (Scheme.relativeDifferentials f).presheaf.stalk x) =
      finrank (ResidueField (X.presheaf.stalk x))
        (ResidueField (X.presheaf.stalk x) ⊗[X.presheaf.stalk x]
          Ω[X.presheaf.stalk x⁄Y.presheaf.stalk (f x)]) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ (f ⁻¹ᵁ V : Set X) from hxV) (f ⁻¹ᵁ V).2
  obtain ⟨y, rfl⟩ : ∃ y, hU.fromSpec y = x := ⟨_, hU.fromSpec_primeIdealOf ⟨x, hxU⟩⟩
  have : y.asIdeal.IsPrime := y.2
  let _ := (f.stalkMap (hU.fromSpec y)).hom.toAlgebra
  let : Algebra Γ(Y, V) (Y.presheaf.stalk (f (hU.fromSpec y))) :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨f (hU.fromSpec y), hxV⟩
  have : IsLocalization.AtPrime (Y.presheaf.stalk (f (hU.fromSpec y)))
      (hV.primeIdealOf ⟨f (hU.fromSpec y), hxV⟩).asIdeal :=
    hV.isLocalization_stalk ⟨f (hU.fromSpec y), hxV⟩
  have : Algebra.FormallyUnramified Γ(Y, V) (Y.presheaf.stalk (f (hU.fromSpec y))) :=
    Algebra.FormallyUnramified.of_isLocalization
      (hV.primeIdealOf ⟨f (hU.fromSpec y), hxV⟩).asIdeal.primeCompl
  let : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  let : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec y, hxU⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec y)) y.asIdeal :=
    hU.isLocalization_stalk' y hxU
  let : Algebra Γ(Y, V) (X.presheaf.stalk (hU.fromSpec y)) :=
    ((algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y))).comp
      (algebraMap Γ(Y, V) Γ(X, U))).toAlgebra
  have : IsScalarTower Γ(Y, V) Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower Γ(Y, V) (Y.presheaf.stalk (f (hU.fromSpec y)))
      (X.presheaf.stalk (hU.fromSpec y)) := IsScalarTower.of_algebraMap_eq fun r ↦ by
    simp only [RingHom.algebraMap_toAlgebra, Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appLE,
      homOfLE_leOfHom, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
      X.presheaf.germ_res_apply]
  refine (finrank_fibre_relativeDifferentials_affine f ⟨U, hU⟩ ⟨V, hV⟩ hUV y).trans ?_
  exact finrank_tensor_kaehler_eq_of_isLocalization (R := Γ(Y, V)) (T := Γ(X, U))
    (A := Y.presheaf.stalk (f (hU.fromSpec y))) y.asIdeal

/-- If `z ⤳ x`, the fibre of `Ω_{X/Y}` at `z` is computed from the stalk at `x`: it has the
dimension of `κ(𝔮) ⊗ Ω_{𝒪_{X,x}/𝒪_{Y,f x}}`, where `𝔮` is the prime of `𝒪_{X,x}` corresponding
to `z`. -/
theorem moduleFiberDim_relativeDifferentials_eq_of_specializes {X Y : Scheme.{u}} (f : X ⟶ Y)
    {z x : X} (h : z ⤳ x) :
    letI := (f.stalkMap x).hom.toAlgebra
    moduleFiberDim (Scheme.relativeDifferentials f) z =
      finrank ((maximalIdeal (X.presheaf.stalk z)).comap
          (X.presheaf.stalkSpecializes h).hom).ResidueField
        (((maximalIdeal (X.presheaf.stalk z)).comap
          (X.presheaf.stalkSpecializes h).hom).ResidueField ⊗[X.presheaf.stalk x]
            Ω[X.presheaf.stalk x⁄Y.presheaf.stalk (f x)]) := by
  have hY : f z ⤳ f x := f.base.hom.map_specializes h
  let _ : Algebra (X.presheaf.stalk x) (X.presheaf.stalk z) :=
    (X.presheaf.stalkSpecializes h).hom.toAlgebra
  let _ : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  let _ : Algebra (Y.presheaf.stalk (f x)) (Y.presheaf.stalk (f z)) :=
    (Y.presheaf.stalkSpecializes hY).hom.toAlgebra
  let _ : Algebra (Y.presheaf.stalk (f z)) (X.presheaf.stalk z) := (f.stalkMap z).hom.toAlgebra
  let _ : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk z) :=
    ((algebraMap (X.presheaf.stalk x) (X.presheaf.stalk z)).comp
      (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x))).toAlgebra
  have : IsScalarTower (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) (X.presheaf.stalk z) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower (Y.presheaf.stalk (f x)) (Y.presheaf.stalk (f z)) (X.presheaf.stalk z) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (f.stalkSpecializes_stalkMap_apply z x h a).symm
  have : IsLocalization.AtPrime (X.presheaf.stalk z)
      ((maximalIdeal (X.presheaf.stalk z)).comap (X.presheaf.stalkSpecializes h).hom) :=
    NormalFamily.isLocalization_stalkSpecializes h
  have : IsLocalization.AtPrime (Y.presheaf.stalk (f z))
      ((maximalIdeal (Y.presheaf.stalk (f z))).comap (Y.presheaf.stalkSpecializes hY).hom) :=
    NormalFamily.isLocalization_stalkSpecializes hY
  have : Algebra.FormallyUnramified (Y.presheaf.stalk (f x)) (Y.presheaf.stalk (f z)) :=
    Algebra.FormallyUnramified.of_isLocalization
      ((maximalIdeal (Y.presheaf.stalk (f z))).comap
        (Y.presheaf.stalkSpecializes hY).hom).primeCompl
  rw [moduleFiberDim, finrank_fibre_relativeDifferentials_eq_stalk]
  exact (finrank_tensor_kaehler_eq_of_isLocalization (R := Y.presheaf.stalk (f x))
    (T := X.presheaf.stalk x) (A := Y.presheaf.stalk (f z)) (B := X.presheaf.stalk z) _).symm

/-- Flatness of stalk maps passes to generalizations: if `x ⤳ x₀` and `𝒪_{Y, f x₀} → 𝒪_{X, x₀}`
is flat, then so is `𝒪_{Y, f x} → 𝒪_{X, x}`. -/
theorem flat_stalkMap_of_specializes {X Y : Scheme.{u}} (f : X ⟶ Y) {x x₀ : X} (h : x ⤳ x₀)
    (h₀ : (f.stalkMap x₀).hom.Flat) : (f.stalkMap x).hom.Flat := by
  have hY : f x ⤳ f x₀ := f.base.hom.map_specializes h
  let _ : Algebra (Y.presheaf.stalk (f x₀)) (X.presheaf.stalk x₀) := (f.stalkMap x₀).hom.toAlgebra
  let _ : Algebra (X.presheaf.stalk x₀) (X.presheaf.stalk x) :=
    (X.presheaf.stalkSpecializes h).hom.toAlgebra
  let _ : Algebra (Y.presheaf.stalk (f x₀)) (Y.presheaf.stalk (f x)) :=
    (Y.presheaf.stalkSpecializes hY).hom.toAlgebra
  let _ : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  let _ : Algebra (Y.presheaf.stalk (f x₀)) (X.presheaf.stalk x) :=
    ((algebraMap (X.presheaf.stalk x₀) (X.presheaf.stalk x)).comp
      (algebraMap (Y.presheaf.stalk (f x₀)) (X.presheaf.stalk x₀))).toAlgebra
  have : IsScalarTower (Y.presheaf.stalk (f x₀)) (X.presheaf.stalk x₀) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower (Y.presheaf.stalk (f x₀)) (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (f.stalkSpecializes_stalkMap_apply x x₀ h a).symm
  have : Module.Flat (Y.presheaf.stalk (f x₀)) (X.presheaf.stalk x₀) := h₀
  have hB : IsLocalization.AtPrime (X.presheaf.stalk x)
      ((maximalIdeal (X.presheaf.stalk x)).comap (X.presheaf.stalkSpecializes h).hom) :=
    NormalFamily.isLocalization_stalkSpecializes h
  have : Module.Flat (X.presheaf.stalk x₀) (X.presheaf.stalk x) :=
    IsLocalization.flat _
      ((maximalIdeal (X.presheaf.stalk x)).comap (X.presheaf.stalkSpecializes h).hom).primeCompl
  have : Module.Flat (Y.presheaf.stalk (f x₀)) (X.presheaf.stalk x) :=
    Module.Flat.trans _ (X.presheaf.stalk x₀) _
  have hA : IsLocalization.AtPrime (Y.presheaf.stalk (f x))
      ((maximalIdeal (Y.presheaf.stalk (f x))).comap (Y.presheaf.stalkSpecializes hY).hom) :=
    NormalFamily.isLocalization_stalkSpecializes hY
  exact (Module.flat_iff_of_isLocalization (Y.presheaf.stalk (f x))
    ((maximalIdeal (Y.presheaf.stalk (f x))).comap (Y.presheaf.stalkSpecializes hY).hom).primeCompl
    (X.presheaf.stalk x)).mpr this

/-- On a Jacobson scheme, a morphism whose stalk maps at closed points are flat is flat. -/
theorem flat_of_forall_isClosed {X Y : Scheme.{u}} [JacobsonSpace X] (f : X ⟶ Y)
    (h : ∀ x : X, IsClosed ({x} : Set X) → (f.stalkMap x).hom.Flat) : Flat f := by
  refine Flat.of_stalkMap f fun x ↦ ?_
  obtain ⟨x₀, hx₀, hc⟩ := nonempty_inter_closedPoints (Z := closure {x})
    ⟨x, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
  exact flat_stalkMap_of_specializes f (specializes_iff_mem_closure.mpr hx₀) (h x₀ hc)

end Scheme

section ClosedPoint

/-- At a closed point `z` of a scheme locally of finite type over an algebraically closed field `k`,
the composite `k → 𝒪_{Z,z} → κ(z)` is bijective. -/
theorem bijective_residue_germ_appTop {k : Type u} [Field k] [IsAlgClosed k] {Z : Scheme.{u}}
    (g : Z ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g] (z : Z)
    (hz : IsClosed ({z} : Set Z)) :
    Function.Bijective fun c : Γ(Spec (.of k), ⊤) ↦
      residue (Z.presheaf.stalk z) (Z.presheaf.germ ⊤ z trivial (g.appTop c)) := by
  -- the base ring `Γ(Spec k, ⊤) ≅ k` is an algebraically closed field
  let eA := (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  let : Field Γ(Spec (.of k), ⊤) := (eA.toMulEquiv.isField (Field.toIsField k)).toField
  have : IsAlgClosed Γ(Spec (.of k), ⊤) := IsAlgClosed.of_ringEquiv k _ eA.symm
  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  let : Algebra Γ(Spec (.of k), ⊤) Γ(Z, U) := (g.appLE ⊤ U le_top).hom.toAlgebra
  have : Algebra.FiniteType Γ(Spec (.of k), ⊤) Γ(Z, U) :=
    g.finiteType_appLE (isAffineOpen_top _) hU le_top
  let m := hU.primeIdealOf ⟨z, hzU⟩
  have : m.asIdeal.IsMaximal := hU.primeIdealOf_isMaximal_of_isClosed ⟨z, hzU⟩ hz
  have hb := DifferentialsNonsingular.bijective_algebraMap_residueField
    (k := Γ(Spec (.of k), ⊤)) m.asIdeal
  let : Algebra Γ(Z, U) (Z.presheaf.stalk z) :=
    TopCat.Presheaf.algebra_section_stalk Z.presheaf ⟨z, hzU⟩
  have : IsLocalization.AtPrime (Z.presheaf.stalk z) m.asIdeal :=
    hU.isLocalization_stalk ⟨z, hzU⟩
  let e := IsLocalization.algEquiv m.asIdeal.primeCompl (Localization.AtPrime m.asIdeal)
    (Z.presheaf.stalk z)
  let ψ := ResidueField.mapEquiv e.toRingEquiv
  convert ψ.bijective.comp hb using 1
  ext c
  change residue _ (Z.presheaf.germ ⊤ z trivial (g.appTop c)) =
    ResidueField.map (e.toRingEquiv : Localization.AtPrime m.asIdeal →+* _)
      (residue _ (algebraMap Γ(Z, U) (Localization.AtPrime m.asIdeal)
        (algebraMap Γ(Spec (.of k), ⊤) Γ(Z, U) c)))
  rw [ResidueField.map_residue]
  congr 1
  change _ = e (algebraMap Γ(Z, U) (Localization.AtPrime m.asIdeal) _)
  rw [AlgEquiv.commutes]
  change _ = Z.presheaf.germ U z hzU (g.appLE ⊤ U le_top c)
  simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    Z.presheaf.germ_res_apply]
  rfl

/-- **Hartshorne II.8, Proposition 8.7, at a closed point.** For a scheme `Z` locally of finite type
over an algebraically closed field `k` and a closed point `z ∈ Z`, the fibre `Ω_{Z/k} ⊗ k(z)` has
the dimension of the cotangent space `𝔪_z/𝔪_z²`. -/
theorem moduleFiberDim_relativeDifferentials_eq_finrank_cotangentSpace {k : Type u} [Field k]
    [IsAlgClosed k] {Z : Scheme.{u}} (g : Z ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g]
    (z : Z) (hz : IsClosed ({z} : Set Z)) :
    moduleFiberDim (Scheme.relativeDifferentials g) z =
      finrank (ResidueField (Z.presheaf.stalk z)) (CotangentSpace (Z.presheaf.stalk z)) := by
  let eA := (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  let : Field Γ(Spec (.of k), ⊤) := (eA.toMulEquiv.isField (Field.toIsField k)).toField
  let _ : Algebra ((Spec (.of k)).presheaf.stalk (g z)) (Z.presheaf.stalk z) :=
    (g.stalkMap z).hom.toAlgebra
  let p : (⊤ : (Spec (.of k)).Opens) := ⟨g z, trivial⟩
  let : Algebra Γ(Spec (.of k), ⊤) ((Spec (.of k)).presheaf.stalk (g z)) :=
    TopCat.Presheaf.algebra_section_stalk (Spec (.of k)).presheaf p
  have : IsLocalization.AtPrime ((Spec (.of k)).presheaf.stalk (g z))
      ((isAffineOpen_top (Spec (.of k))).primeIdealOf p).asIdeal :=
    (isAffineOpen_top (Spec (.of k))).isLocalization_stalk p
  have : Algebra.FormallyUnramified Γ(Spec (.of k), ⊤) ((Spec (.of k)).presheaf.stalk (g z)) :=
    Algebra.FormallyUnramified.of_isLocalization
      ((isAffineOpen_top (Spec (.of k))).primeIdealOf p).asIdeal.primeCompl
  let : Algebra Γ(Spec (.of k), ⊤) (Z.presheaf.stalk z) :=
    (g.appTop ≫ Z.presheaf.germ ⊤ z trivial).hom.toAlgebra
  have : IsScalarTower Γ(Spec (.of k), ⊤) ((Spec (.of k)).presheaf.stalk (g z))
      (Z.presheaf.stalk z) := IsScalarTower.of_algebraMap_eq fun c ↦ by
    change Z.presheaf.germ ⊤ z trivial (g.appTop c) =
      g.stalkMap z ((Spec (.of k)).presheaf.germ ⊤ (g z) trivial c)
    exact (Scheme.Hom.germ_stalkMap_apply g ⊤ z trivial c).symm
  have hk : Function.Bijective
      (algebraMap Γ(Spec (.of k), ⊤) (ResidueField (Z.presheaf.stalk z))) :=
    bijective_residue_germ_appTop g z hz
  -- `Ω_{𝒪_{Z,z}/k} ≅ Ω_{𝒪_{Z,z}/𝒪_{Spec k, g z}}`
  let e₁ : Ω[Z.presheaf.stalk z⁄Γ(Spec (.of k), ⊤)] ≃ₗ[Z.presheaf.stalk z]
      Ω[Z.presheaf.stalk z⁄(Spec (.of k)).presheaf.stalk (g z)] :=
    LinearEquiv.ofBijective (KaehlerDifferential.map _ _ _ _)
      ⟨map_injective_of_subsingleton, KaehlerDifferential.map_surjective _ _ _⟩
  -- II.8.7: `𝔪_z/𝔪_z² ≅ Ω_{𝒪_{Z,z}/k} ⊗ κ(z)`
  let e₂ : CotangentSpace (Z.presheaf.stalk z) ≃ₗ[ResidueField (Z.presheaf.stalk z)]
      ResidueField (Z.presheaf.stalk z) ⊗[Z.presheaf.stalk z]
        Ω[Z.presheaf.stalk z⁄Γ(Spec (.of k), ⊤)] :=
    LinearEquiv.ofBijective (CotangentKaehler.cotangentToFiber _ _)
      ⟨CotangentKaehler.cotangentToFiber_injective _ hk,
        CotangentKaehler.cotangentToFiber_surjective _ _ _ hk.2⟩
  rw [moduleFiberDim, finrank_fibre_relativeDifferentials_eq_stalk, e₂.finrank_eq]
  exact ((TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl (ResidueField (Z.presheaf.stalk z)) (ResidueField (Z.presheaf.stalk z)))
      e₁).finrank_eq).symm

/-- **Hartshorne III, proof of Proposition 10.4**: "`X` and `Y` are both smooth over `k`". A
nonsingular variety `Z` of dimension `d` over an algebraically closed field `k` is smooth over `k`
of relative dimension `d` (Example 10.0.3), so `Ω_{Z/k}` is locally free of rank `d`
(Example 10.0.2), and by II.8.7 the cotangent space at every closed point has dimension `d`. -/
theorem finrank_cotangentSpace_eq_of_isRegularAt {k : Type u} [Field k] [IsAlgClosed k]
    {Z : Scheme.{u}} (g : Z ⟶ Spec (CommRingCat.of k)) (hg : FiniteType g) [IsIntegral Z]
    (hZ : ∀ z : Z, Z.IsRegularAt z) {d : ℕ} (hd : topologicalKrullDim Z = d) (z : Z)
    (hz : IsClosed ({z} : Set Z)) :
    finrank (ResidueField (Z.presheaf.stalk z)) (CotangentSpace (Z.presheaf.stalk z)) = d := by
  have : LocallyOfFiniteType g := hg.1
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian g
  -- `Z` is smooth over `k` of relative dimension `d`
  have : SmoothOfRelativeDimension d g :=
    (smoothOfRelativeDimension_iff_forall_isRegularAt g hg d).mpr ⟨hZ, fun C hC ↦ by
      rw [eq_univ_of_mem_irreducibleComponents hC,
        (Homeomorph.Set.univ Z).isHomeomorph.topologicalKrullDim_eq, hd]⟩
  -- so `Ω_{Z/k}` is locally free of rank `d`
  have hfree := (Scheme.relativeDifferentials_isLocallyFreeOfRank_iff g d).mp
    (Scheme.relativeDifferentials_isLocallyFreeOfRank_of_smoothOfRelativeDimension g d) z
  rw [← moduleFiberDim_relativeDifferentials_eq_finrank_cotangentSpace g z hz]
  exact hfree

/-- At a closed point `x` of a scheme of finite type over an algebraically closed field `k`, for a
`k`-morphism `f : X ⟶ Y`, the scalar-extended cotangent map
`κ(x) ⊗ 𝔪_{f x}/𝔪_{f x}² → 𝔪_x/𝔪_x²` is injective if and only if
`dim κ(x) ⊗ (Ω_{X/Y})_x + dim 𝔪_{f x}/𝔪_{f x}² = dim 𝔪_x/𝔪_x²`. This is the dimension count in the
fibre at `x` of the exact sequence `f^*Ω_{Y/k} → Ω_{X/k} → Ω_{X/Y} → 0` of II.8.11, taken on stalks
(`stalk_kaehler_transitivity_exact`) and identified with the cotangent sequence by II.8.7. -/
theorem injective_localCotangentBaseChange_iff_of_isClosed {k : Type u} [Field k]
    [IsAlgClosed k] {X Y : Over (Spec (CommRingCat.of k))} (hX : LocallyOfFiniteType X.hom)
    (f : X ⟶ Y) (x : X.left) (hx : IsClosed ({x} : Set X.left))
    [IsNoetherianRing (Y.left.presheaf.stalk (f.left x))]
    [IsNoetherianRing (X.left.presheaf.stalk x)] :
    letI := (f.left.stalkMap x).hom.toAlgebra
    haveI := isLocalHom_stalkMap_algebraMap f.left x
    Function.Injective (localCotangentBaseChange (Y.left.presheaf.stalk (f.left x))
        (X.left.presheaf.stalk x)) ↔
      finrank (ResidueField (X.left.presheaf.stalk x))
          (ResidueField (X.left.presheaf.stalk x) ⊗[X.left.presheaf.stalk x]
            (Scheme.relativeDifferentials f.left).presheaf.stalk x) +
        finrank (ResidueField (Y.left.presheaf.stalk (f.left x)))
          (CotangentSpace (Y.left.presheaf.stalk (f.left x))) =
      finrank (ResidueField (X.left.presheaf.stalk x))
        (CotangentSpace (X.left.presheaf.stalk x)) := by
  let _ := (f.left.stalkMap x).hom.toAlgebra
  have := isLocalHom_stalkMap_algebraMap f.left x
  -- the base ring `Γ(Spec k, ⊤) ≅ k` is an algebraically closed field
  let eA := (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  let : Field Γ(Spec (.of k), ⊤) := (eA.toMulEquiv.isField (Field.toIsField k)).toField
  have : IsAlgClosed Γ(Spec (.of k), ⊤) := IsAlgClosed.of_ringEquiv k _ eA.symm
  let : Algebra Γ(Spec (.of k), ⊤) (Y.left.presheaf.stalk (f.left x)) :=
    (Y.hom.appTop ≫ Y.left.presheaf.germ ⊤ (f.left x) trivial).hom.toAlgebra
  let : Algebra Γ(Spec (.of k), ⊤) (X.left.presheaf.stalk x) :=
    (X.hom.appTop ≫ X.left.presheaf.germ ⊤ x trivial).hom.toAlgebra
  have : IsScalarTower Γ(Spec (.of k), ⊤) (Y.left.presheaf.stalk (f.left x))
      (X.left.presheaf.stalk x) := IsScalarTower.of_algebraMap_eq fun c ↦ by
    change X.left.presheaf.germ ⊤ x trivial (X.hom.appTop c) =
      f.left.stalkMap x (Y.left.presheaf.germ ⊤ (f.left x) trivial (Y.hom.appTop c))
    rw [← Over.w f]
    exact (Scheme.Hom.germ_stalkMap_apply f.left ⊤ x trivial (Y.hom.appTop c)).symm
  -- `k → κ(x)` is bijective at the closed point `x`
  have : LocallyOfFiniteType X.hom := hX
  have hk : Function.Bijective
      (algebraMap Γ(Spec (.of k), ⊤) (ResidueField (X.left.presheaf.stalk x))) :=
    bijective_residue_germ_appTop X.hom x hx
  -- the stalk at `x` of the exact sequence of II.8.11 for `X ⟶ Y ⟶ Spec k`, over the stalk `S₀`
  -- of `Spec k`, and then over `k` itself
  have hex : Function.Exact
      (mapBaseChange Γ(Spec (.of k), ⊤) (Y.left.presheaf.stalk (f.left x))
        (X.left.presheaf.stalk x))
      (map Γ(Spec (.of k), ⊤) (Y.left.presheaf.stalk (f.left x)) (X.left.presheaf.stalk x)
        (X.left.presheaf.stalk x)) := by
    let S₀ := (Spec (.of k)).presheaf.stalk (Y.hom (f.left x))
    let _ : Algebra S₀ (Y.left.presheaf.stalk (f.left x)) :=
      (Y.hom.stalkMap (f.left x)).hom.toAlgebra
    let _ : Algebra S₀ (X.left.presheaf.stalk x) :=
      ((f.left.stalkMap x).hom.comp (Y.hom.stalkMap (f.left x)).hom).toAlgebra
    have : IsScalarTower S₀ (Y.left.presheaf.stalk (f.left x)) (X.left.presheaf.stalk x) :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    let p : (⊤ : (Spec (.of k)).Opens) := ⟨Y.hom (f.left x), trivial⟩
    let : Algebra Γ(Spec (.of k), ⊤) S₀ :=
      TopCat.Presheaf.algebra_section_stalk (Spec (.of k)).presheaf p
    have : IsLocalization.AtPrime S₀ ((isAffineOpen_top (Spec (.of k))).primeIdealOf p).asIdeal :=
      (isAffineOpen_top (Spec (.of k))).isLocalization_stalk p
    have : Algebra.FormallyUnramified Γ(Spec (.of k), ⊤) S₀ :=
      Algebra.FormallyUnramified.of_isLocalization
        ((isAffineOpen_top (Spec (.of k))).primeIdealOf p).asIdeal.primeCompl
    have hY : ∀ c : Γ(Spec (.of k), ⊤), Y.hom.stalkMap (f.left x)
        ((Spec (.of k)).presheaf.germ ⊤ (Y.hom (f.left x)) trivial c) =
          Y.left.presheaf.germ ⊤ (f.left x) trivial (Y.hom.appTop c) := fun c ↦
      Scheme.Hom.germ_stalkMap_apply Y.hom ⊤ (f.left x) trivial c
    have : IsScalarTower Γ(Spec (.of k), ⊤) S₀ (Y.left.presheaf.stalk (f.left x)) :=
      IsScalarTower.of_algebraMap_eq fun c ↦ (hY c).symm
    have : IsScalarTower Γ(Spec (.of k), ⊤) S₀ (X.left.presheaf.stalk x) :=
      IsScalarTower.of_algebraMap_eq fun c ↦ by
        change X.left.presheaf.germ ⊤ x trivial (X.hom.appTop c) =
          f.left.stalkMap x (Y.hom.stalkMap (f.left x)
            ((Spec (.of k)).presheaf.germ ⊤ (Y.hom (f.left x)) trivial c))
        rw [hY, ← Over.w f]
        exact (Scheme.Hom.germ_stalkMap_apply f.left ⊤ x trivial (Y.hom.appTop c)).symm
    exact exact_mapBaseChange_map_of_subsingleton (T := S₀)
      (stalk_kaehler_transitivity_exact f.left Y.hom x)
  rw [CotangentKaehler.injective_localCotangentBaseChange_iff Γ(Spec (.of k), ⊤) _ _ hk hex,
    finrank_fibre_relativeDifferentials_eq_stalk]

end ClosedPoint

section Main

/-- The tangent map at `x` is surjective if and only if the scalar-extended cotangent map is
injective. -/
theorem surjective_zariskiTangentMap_iff {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    [Module.Finite (ResidueField (Y.presheaf.stalk (f x)))
      (CotangentSpace (Y.presheaf.stalk (f x)))] :
    letI := (f.stalkMap x).hom.toAlgebra
    haveI := isLocalHom_stalkMap_algebraMap f x
    Function.Surjective (zariskiTangentMap f x) ↔
      Function.Injective
        (localCotangentBaseChange (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) := by
  let _ := (f.stalkMap x).hom.toAlgebra
  have := isLocalHom_stalkMap_algebraMap f x
  rw [← LinearMap.dualMap_surjective_iff]
  change Function.Surjective (localTangentMap _ _) ↔ _
  simp only [localTangentMap, LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.comp_surjective]

/-- The transcendence degree over `k` of the local ring at a point `y` equal to the generic point
of `Y` is that of the function field. -/
theorem trdeg_stalk_eq_of_eq_genericPoint {k : Type u} [Field k] {Y : Scheme.{u}} [IsIntegral Y]
    (p : Y ⟶ Spec (.of k)) (y : Y) (hy : genericPoint Y = y) :
    (letI : Algebra k (Y.presheaf.stalk y) :=
      ((Y.presheaf.germ (p ⁻¹ᵁ ⊤) y trivial).hom.comp
        ((p.app ⊤).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)).toAlgebra;
      Algebra.trdeg k (Y.presheaf.stalk y)) =
      (letI := functionFieldAlgebra p; Algebra.trdeg k Y.functionField) := by
  subst hy
  rfl

/-- **Hartshorne III, proof of Proposition 10.4, via II.8.6A.** Let `f : X ⟶ Y` be a `k`-morphism
of integral schemes of finite type over a field `k` that sends the generic point `η` of `X` to the
generic point of `Y`, with `dim X = dim Y + n`. Then
`dim_{K(X)} Ω_{K(X)/K(Y)} ≥ tr.deg K(X)/K(Y) = n`. -/
theorem le_finrank_kaehler_genericPoint {k : Type u} [Field k] {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k)) (hX : FiniteType pX) (hY : FiniteType pY)
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) (hf : f ≫ pY = pX)
    (hgen : f (genericPoint X) = genericPoint Y) {n : ℕ}
    (hdim : topologicalKrullDim X = topologicalKrullDim Y + n) :
    letI := (f.stalkMap (genericPoint X)).hom.toAlgebra
    n ≤ finrank (X.presheaf.stalk (genericPoint X))
      Ω[X.presheaf.stalk (genericPoint X)⁄Y.presheaf.stalk (f (genericPoint X))] := by
  subst hf
  have : LocallyOfFiniteType (f ≫ pY) := hX.1
  have : LocallyOfFiniteType pY := hY.1
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f pY
  set η := genericPoint X
  have hfield : IsField (Y.presheaf.stalk (f η)) := hgen ▸ Field.toIsField Y.functionField
  let : Field (Y.presheaf.stalk (f η)) := hfield.toField
  let : Algebra (Y.presheaf.stalk (f η)) (X.presheaf.stalk η) := (f.stalkMap η).hom.toAlgebra
  have : Algebra.EssFiniteType (Y.presheaf.stalk (f η)) (X.presheaf.stalk η) :=
    LocallyOfFiniteType.stalkMap f η
  -- II.8.6A: `tr.deg K(X)/K(Y) ≤ dim Ω_{K(X)/K(Y)}`
  have h86 := (trdeg_le_rank_kaehlerDifferential (k := Y.presheaf.stalk (f η))
    (K := X.presheaf.stalk η) (IntermediateField.fg_top_iff.mpr inferInstance)).1
  rw [← Module.finrank_eq_rank] at h86
  obtain ⟨t, ht⟩ : ∃ t : ℕ, Algebra.trdeg (Y.presheaf.stalk (f η)) (X.presheaf.stalk η) = t :=
    Cardinal.lt_aleph0.mp (h86.trans_lt Cardinal.natCast_lt_aleph0)
  -- `tr.deg K(X)/K(Y) = dim X - dim Y = n`, from `dim = tr.deg` and the tower `k ⊆ K(Y) ⊆ K(X)`
  let φ : Algebra k (Y.presheaf.stalk (f η)) :=
    ((Y.presheaf.germ (pY ⁻¹ᵁ ⊤) (f η) trivial).hom.comp
      ((pY.app ⊤).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)).toAlgebra
  obtain ⟨rX, hXdim, hXtr⟩ := exists_topologicalKrullDim_eq_trdeg (f ≫ pY) hX
  obtain ⟨rY, hYdim, hYtr⟩ := exists_topologicalKrullDim_eq_trdeg pY hY
  rw [← trdeg_stalk_eq_of_eq_genericPoint pY (f η) hgen.symm] at hYtr
  let := functionFieldAlgebra (f ≫ pY)
  have : IsScalarTower k (Y.presheaf.stalk (f η)) (X.presheaf.stalk η) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      change _ = f.stalkMap η (Y.presheaf.germ (pY ⁻¹ᵁ ⊤) (f η) trivial
        (pY.app ⊤ ((Scheme.ΓSpecIso (.of k)).inv a)))
      exact (Scheme.Hom.germ_stalkMap_apply f (pY ⁻¹ᵁ ⊤) η trivial _).symm
  have htr : rY + t = rX := by
    have h := trdeg_add_eq k (Y.presheaf.stalk (f η)) (A := X.presheaf.stalk η)
    rw [hYtr, ht, hXtr] at h
    exact_mod_cast h
  have hrn : rX = rY + n := by
    rw [hXdim, hYdim] at hdim
    exact_mod_cast hdim
  have htn : t = n := by omega
  rw [ht, htn] at h86
  exact_mod_cast h86

/-- **Hartshorne III, Proposition 10.4.** Let `f : X → Y` be a morphism of nonsingular varieties
over an algebraically closed field `k`, with `dim X = dim Y + n`. The following are equivalent:
1. `f` is smooth of relative dimension `n`;
2. `Ω_{X/Y}` is locally free of rank `n`;
3. for every closed point `x ∈ X`, the Zariski tangent map `T_x X → k(x) ⊗ T_{f x} Y` is
   surjective.

Varieties are integral schemes of finite type over `k` (separatedness is not used); nonsingular
means every local ring is regular. -/
theorem smoothOfRelativeDimension_tfae_of_isRegularAt {k : Type u} [Field k] [IsAlgClosed k]
    {X Y : Over (Spec (CommRingCat.of k))}
    (hX : LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom)
    (hY : LocallyOfFiniteType Y.hom ∧ QuasiCompact Y.hom)
    [IsIntegral X.left] [IsIntegral Y.left]
    (hXr : ∀ x : X.left, X.left.IsRegularAt x) (hYr : ∀ y : Y.left, Y.left.IsRegularAt y)
    (f : X ⟶ Y) (n : ℕ)
    (hdim : topologicalKrullDim X.left = topologicalKrullDim Y.left + n) :
    haveI : LocallyOfFiniteType Y.hom := hY.1
    haveI := LocallyOfFiniteType.isLocallyNoetherian Y.hom
    [SmoothOfRelativeDimension n f.left,
      (Scheme.relativeDifferentials f.left).IsLocallyFreeOfRank n,
      ∀ x : X.left, IsClosed ({x} : Set X.left) →
        Function.Surjective (zariskiTangentMap f.left x)].TFAE := by
  have : LocallyOfFiniteType X.hom := hX.1
  have : LocallyOfFiniteType Y.hom := hY.1
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [Over.w f]; infer_instance
  have : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left Y.hom
  -- `X` and `Y` are both smooth over `k`, of relative dimensions `dim X` and `dim Y`, so their
  -- cotangent spaces at closed points have dimensions `dim X` and `dim Y`
  -- (Examples 10.0.3 and 10.0.2 and II.8.7)
  obtain ⟨dX, hdX, -⟩ := exists_topologicalKrullDim_eq_trdeg X.hom hX
  obtain ⟨dY, hdY, -⟩ := exists_topologicalKrullDim_eq_trdeg Y.hom hY
  have hd : dX = dY + n := by
    rw [hdX, hdY] at hdim
    exact_mod_cast hdim
  have hcotX : ∀ x : X.left, IsClosed ({x} : Set X.left) →
      finrank (ResidueField (X.left.presheaf.stalk x)) (CotangentSpace (X.left.presheaf.stalk x)) =
        dX := finrank_cotangentSpace_eq_of_isRegularAt X.hom hX hXr hdX
  have hcotY : ∀ y : Y.left, IsClosed ({y} : Set Y.left) →
      finrank (ResidueField (Y.left.presheaf.stalk y)) (CotangentSpace (Y.left.presheaf.stalk y)) =
        dY := finrank_cotangentSpace_eq_of_isRegularAt Y.hom hY hYr hdY
  -- the fibre at a closed point of the exact sequence `f^*Ω_Y → Ω_X → Ω_{X/Y} → 0` of II.8.11,
  -- with `Ω_X ⊗ k(x) ≅ 𝔪_x/𝔪_x²` and `Ω_Y ⊗ k(y) ≅ 𝔪_y/𝔪_y²` (II.8.7)
  have key : ∀ x : X.left, IsClosed ({x} : Set X.left) →
      (Function.Surjective (zariskiTangentMap f.left x) ↔
        moduleFiberDim (Scheme.relativeDifferentials f.left) x + dY = dX) := fun x hx ↦ by
    rw [surjective_zariskiTangentMap_iff,
      injective_localCotangentBaseChange_iff_of_isClosed hX.1 f x hx,
      hcotY _ (f.left.closePoints_subset_preimage_closedPoints hx), hcotX x hx]
    rfl
  tfae_have 1 → 2 := fun h ↦
    haveI := h
    Scheme.relativeDifferentials_isLocallyFreeOfRank_of_smoothOfRelativeDimension f.left n
  tfae_have 2 → 3 := by
    intro h x hx
    rw [key x hx]
    have := (Scheme.relativeDifferentials_isLocallyFreeOfRank_iff f.left n).mp h x
    change moduleFiberDim _ x = n at this
    omega
  tfae_have 3 → 1 := by
    intro h
    -- the fibre of `Ω_{X/Y}` at every closed point has dimension `n`
    have hfib : ∀ x : X.left, IsClosed ({x} : Set X.left) →
        moduleFiberDim (Scheme.relativeDifferentials f.left) x = n := fun x hx ↦ by
      have := (key x hx).mp (h x hx)
      omega
    -- `f` is flat: regular parameters and Lemma 10.3A at each closed point
    have hflat : Flat f.left := flat_of_forall_isClosed f.left fun x hx ↦
      RegularCotangentFlat.flat_stalkMap_of_surjective_zariskiTangentMap f.left x (hXr x)
        (hYr _) (h x hx)
    -- hence `f` sends the generic point `η` of `X` to the generic point of `Y`
    set η := genericPoint X.left
    have hηspec : IsGenericPoint η ⊤ := genericPoint_spec X.left
    have hgen : f.left η = genericPoint Y.left := by
      obtain ⟨η', h', he⟩ := Flat.generalizingMap f.left
        ((genericPoint_spec Y.left).specializes (trivial : f.left η ∈ ⊤))
      rw [← he, (h'.antisymm (hηspec.specializes trivial)).eq]
    -- the fibre of `Ω_{X/Y}` at `η` is `Ω_{K(X)/K(Y)}`
    let _ : Algebra (Y.left.presheaf.stalk (f.left η)) (X.left.presheaf.stalk η) :=
      (f.left.stalkMap η).hom.toAlgebra
    have hη : moduleFiberDim (Scheme.relativeDifferentials f.left) η =
        finrank (X.left.presheaf.stalk η)
          Ω[X.left.presheaf.stalk η⁄Y.left.presheaf.stalk (f.left η)] := by
      rw [moduleFiberDim, finrank_fibre_relativeDifferentials_eq_stalk, Module.finrank_baseChange]
    -- its dimension is at least `tr.deg K(X)/K(Y) = n` (II.8.6A) ...
    have hge : n ≤ finrank (X.left.presheaf.stalk η)
        Ω[X.left.presheaf.stalk η⁄Y.left.presheaf.stalk (f.left η)] :=
      le_finrank_kaehler_genericPoint X.hom Y.hom hX hY f.left (Over.w f) hgen hdim
    -- ... and at most `n`, the value at a closed point (upper semicontinuity)
    obtain ⟨x₀, -, hx₀⟩ := nonempty_inter_closedPoints (X := X.left) Set.univ_nonempty
      isClosed_univ.isLocallyClosed
    have hle : moduleFiberDim (Scheme.relativeDifferentials f.left) η ≤ n := by
      by_contra hlt
      have hmem := (hηspec.specializes (trivial : x₀ ∈ ⊤)).mem_closed
        (isClosed_setOf_le_moduleFiberDim_of_isCoherent (Scheme.relativeDifferentials f.left)
          (Scheme.relativeDifferentials_isCoherent_of_locallyOfFiniteType f.left) ((n + 1 : ℕ) : ℤ))
        (show ((n + 1 : ℕ) : ℤ) ≤ _ by push_cast; omega)
      have := hfib x₀ hx₀
      simp only [Set.mem_ofPred_eq, this] at hmem
      omega
    have hKn : finrank (X.left.presheaf.stalk η)
        Ω[X.left.presheaf.stalk η⁄Y.left.presheaf.stalk (f.left η)] = n := by
      rw [← hη] at hge ⊢
      exact le_antisymm hle hge
    -- II.8.9: at each closed point `x`, `Ω_{𝒪_{X,x}/𝒪_{Y,f x}}` is free of rank `n`, since its
    -- fibres at the closed point and at the generic point both have dimension `n`
    have hfree : ∀ x : X.left, IsClosed ({x} : Set X.left) →
        letI := (f.left.stalkMap x).hom.toAlgebra
        Module.Free (X.left.presheaf.stalk x)
            Ω[X.left.presheaf.stalk x⁄Y.left.presheaf.stalk (f.left x)] ∧
          finrank (X.left.presheaf.stalk x)
            Ω[X.left.presheaf.stalk x⁄Y.left.presheaf.stalk (f.left x)] = n := by
      intro x hx
      let _ : Algebra (Y.left.presheaf.stalk (f.left x)) (X.left.presheaf.stalk x) :=
        (f.left.stalkMap x).hom.toAlgebra
      have : Algebra.EssFiniteType (Y.left.presheaf.stalk (f.left x)) (X.left.presheaf.stalk x) :=
        LocallyOfFiniteType.stalkMap f.left x
      have hk : finrank (ResidueField (X.left.presheaf.stalk x))
          (ResidueField (X.left.presheaf.stalk x) ⊗[X.left.presheaf.stalk x]
            Ω[X.left.presheaf.stalk x⁄Y.left.presheaf.stalk (f.left x)]) = n :=
        (finrank_fibre_relativeDifferentials_eq_stalk f.left x).symm.trans (hfib x hx)
      -- `K(X) ⊗ Ω_{𝒪_{X,x}/𝒪_{Y,f x}} ≅ Ω_{K(X)/K(Y)}`
      have hηx : η ⤳ x := hηspec.specializes trivial
      have hY : f.left η ⤳ f.left x := f.left.base.hom.map_specializes hηx
      let _ : Algebra (Y.left.presheaf.stalk (f.left x)) (Y.left.presheaf.stalk (f.left η)) :=
        (Y.left.presheaf.stalkSpecializes hY).hom.toAlgebra
      let _ : Algebra (Y.left.presheaf.stalk (f.left x)) X.left.functionField :=
        ((algebraMap (X.left.presheaf.stalk x) X.left.functionField).comp
          (algebraMap (Y.left.presheaf.stalk (f.left x)) (X.left.presheaf.stalk x))).toAlgebra
      have : IsScalarTower (Y.left.presheaf.stalk (f.left x)) (X.left.presheaf.stalk x)
          X.left.functionField := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
      have : IsScalarTower (Y.left.presheaf.stalk (f.left x)) (Y.left.presheaf.stalk (f.left η))
          X.left.functionField := IsScalarTower.of_algebraMap_eq fun a ↦
        (f.left.stalkSpecializes_stalkMap_apply η x hηx a).symm
      have : IsLocalization.AtPrime (Y.left.presheaf.stalk (f.left η))
          ((maximalIdeal (Y.left.presheaf.stalk (f.left η))).comap
            (Y.left.presheaf.stalkSpecializes hY).hom) :=
        NormalFamily.isLocalization_stalkSpecializes hY
      have : Algebra.FormallyUnramified (Y.left.presheaf.stalk (f.left x))
          (Y.left.presheaf.stalk (f.left η)) :=
        Algebra.FormallyUnramified.of_isLocalization
          ((maximalIdeal (Y.left.presheaf.stalk (f.left η))).comap
            (Y.left.presheaf.stalkSpecializes hY).hom).primeCompl
      have hK : finrank X.left.functionField (X.left.functionField ⊗[X.left.presheaf.stalk x]
          Ω[X.left.presheaf.stalk x⁄Y.left.presheaf.stalk (f.left x)]) = n :=
        (finrank_tensor_kaehler_eq_finrank_of_isLocalization (R := Y.left.presheaf.stalk (f.left x))
          (A := Y.left.presheaf.stalk (f.left η)) (B := X.left.functionField)
          (nonZeroDivisors (X.left.presheaf.stalk x))).trans hKn
      exact free_of_finrank_residueField_eq_finrank_fractionField X.left.functionField hk hK
    -- hence every fibre of `Ω_{X/Y}` has dimension `n`: each point specializes to a closed point
    have hall : ∀ z : X.left, moduleFiberDim (Scheme.relativeDifferentials f.left) z = n := by
      intro z
      obtain ⟨x, hx, hxc⟩ := nonempty_inter_closedPoints (Z := closure {z})
        ⟨z, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
      have hzx : z ⤳ x := specializes_iff_mem_closure.mpr hx
      obtain ⟨hfr, hrk⟩ := hfree x hxc
      rw [moduleFiberDim_relativeDifferentials_eq_of_specializes f.left hzx,
        Module.finrank_baseChange, hrk]
    rw [smoothOfRelativeDimension_iff_flat_and_component_dim_and_finrank hX hY f n]
    refine ⟨hflat, ?_, hall⟩
    intro X' hX' Y' hY' _
    rw [eq_univ_of_mem_irreducibleComponents hX', eq_univ_of_mem_irreducibleComponents hY',
      (Homeomorph.Set.univ X.left).isHomeomorph.topologicalKrullDim_eq,
      (Homeomorph.Set.univ Y.left).isHomeomorph.topologicalKrullDim_eq]
    exact hdim
  tfae_finish

end Main

end SmoothTangent

end

end Hartshorne

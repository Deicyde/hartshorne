/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.QuasiCoherentAlgebraOfModule
import Hartshorne.RingedSpace.PolynomialSheafSections

/-!
# Sections of `Sym(E)` over affine opens on which `E` is free

Supplements Hartshorne II, Exercise 5.18 (p. 128). Let `E` be an `𝒪_Y`-module and let
`e = (e_k)` be a frame of `E` over an open `U` of `Y` (`Hartshorne.Ringed.IsLocalFrame`), that is,
`E|_U ≅ 𝒪_U^{⊕ κ}` with basis `e`. The `Γ(U, 𝒪_Y)`-algebra homomorphism
`Γ(U, 𝒪_Y)[x_k] → Γ(U, Sym(E))`, `x_k ↦ e_k` (`chartRingHom`), is bijective when `U` is affine
(`chartRingHom_bijective`): local bases identify `Sym(E)` with a polynomial algebra. These maps are
compatible with restriction (`chartRingHom_naturality`), and two frames over the same open give
maps differing by a linear change of variables (`chartRingHom_transition`): `x_k ↦ ∑_l a_{kl} x_l`
where `e'_k = ∑_l a_{kl} e_l`.
-/

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

open Hartshorne Hartshorne.SheafAlgebraOperations Hartshorne.ModuleSheafAlgebra

noncomputable section

variable {Y : Scheme.{u}} (E : Y.Modules)

/-- The multiplication of `Sym(E)` is commutative. -/
theorem symmetricAlgebraStructure_isCommutative :
    ModuleSheafAlgebra.IsCommutative E.symmetricAlgebraStructure :=
  moduleSheafSymmetricAlgebra_mul_comm (R := Y.sheaf) E

/-- `E` as a sheaf of modules on the ringed space `(Y, 𝒪_Y)`. -/
private abbrev ringed : SheafOfModules.{u} (ringCatSheafOf Y.sheaf) := E

/-- The commutative ring `Γ(U, Sym(E))`. -/
abbrev symSections (U : Y.Opens) : CommRingCat.{u} :=
  sectionsRing E.symmetricAlgebraStructure_isCommutative U

/-- The canonical ring homomorphism `S(Γ(U, E)) → Γ(U, Sym(E))` from the symmetric algebra of the
module of sections. -/
def symUnitRingHom (U : Y.Opens) : SymmetricAlgebra Γ(Y, U) Γ(E, U) →+* E.symSections U where
  toFun a := toSectionsRing _
    ((sheafifyUnit (moduleSheafSymmetricAlgebraPresheaf (R := Y.sheaf) E)).app (op U) a)
  map_one' := (moduleSheafSymmetricAlgebra_one (R := Y.sheaf) E (op U)).symm
  map_mul' a b := (moduleSheafSymmetricAlgebra_mul_unit (R := Y.sheaf) E (op U) a b).symm
  map_zero' := map_zero _
  map_add' := map_add _

/-- The degree-one sections: `Γ(U, E) → Γ(U, Sym(E))`. -/
def symDegreeOne (U : Y.Opens) (s : Γ(E, U)) : E.symSections U :=
  E.symUnitRingHom U (SymmetricAlgebra.ι _ _ s)

lemma symUnitRingHom_algebraMap (U : Y.Opens) (r : Γ(Y, U)) :
    E.symUnitRingHom U (algebraMap _ _ r) = unitRingHom _ U r := by
  exact congrArg (toSectionsRing _)
    ((congrArg ((sheafifyUnit (moduleSheafSymmetricAlgebraPresheaf (R := Y.sheaf) E)).app (op U))
      (Algebra.algebraMap_eq_smul_one (A := SymmetricAlgebra Γ(Y, U) Γ(E, U)) r)).trans
      (((sheafifyUnit (moduleSheafSymmetricAlgebraPresheaf (R := Y.sheaf) E)).app
        (op U)).hom.map_smul r (1 : SymmetricAlgebra Γ(Y, U) Γ(E, U))))

lemma symDegreeOne_smul (U : Y.Opens) (r : Γ(Y, U)) (s : Γ(E, U)) :
    E.symDegreeOne U (r • s) = unitRingHom _ U r * E.symDegreeOne U s := by
  rw [symDegreeOne, symDegreeOne, ← symUnitRingHom_algebraMap, ← map_mul, ← Algebra.smul_def]
  congr 1
  exact (SymmetricAlgebra.ι _ _).map_smul r s

lemma symDegreeOne_add (U : Y.Opens) (s t : Γ(E, U)) :
    E.symDegreeOne U (s + t) = E.symDegreeOne U s + E.symDegreeOne U t := by
  rw [symDegreeOne, symDegreeOne, symDegreeOne, map_add, map_add]

lemma symDegreeOne_sum {κ : Type*} (U : Y.Opens) (T : Finset κ) (s : κ → Γ(E, U)) :
    E.symDegreeOne U (∑ k ∈ T, s k) = ∑ k ∈ T, E.symDegreeOne U (s k) := by
  rw [symDegreeOne, map_sum, map_sum]
  rfl

lemma symDegreeOne_naturality {U V : Y.Opens} (i : V ⟶ U) (s : Γ(E, U)) :
    sectionsRestrict _ i (E.symDegreeOne U s) = E.symDegreeOne V (E.presheaf.map i.op s) := by
  exact congrArg (toSectionsRing _)
    ((PresheafOfModules.naturality_apply
      (sheafifyUnit (moduleSheafSymmetricAlgebraPresheaf (R := Y.sheaf) E)) i.op
        (SymmetricAlgebra.ι Γ(Y, U) Γ(E, U) s)).symm.trans
      (congrArg ((sheafifyUnit (moduleSheafSymmetricAlgebraPresheaf (R := Y.sheaf) E)).app (op V))
        (SheafTensorOperations.symmetricAlgebraRingHom_ι _ (E.ringed.val.restrictₛₗ i.op)
          (show E.ringed.val.obj (op U) from s))))

variable {κ : Type u}

/-- **The chart ring map** `Γ(U, 𝒪_Y)[x_k] → Γ(U, Sym(E))`, `x_k ↦ e_k`, of a family `e` of
sections of `E` over `U`: the `Γ(U, 𝒪_Y)`-algebra homomorphism sending each variable to the
corresponding section in degree one. -/
def chartRingHom (U : Y.Opens) (e : κ → Γ(E, U)) :
    MvPolynomial κ Γ(Y, U) →+* E.symSections U :=
  MvPolynomial.eval₂Hom (unitRingHom _ U).hom fun k => E.symDegreeOne U (e k)

lemma chartRingHom_C (U : Y.Opens) (e : κ → Γ(E, U)) (r : Γ(Y, U)) :
    E.chartRingHom U e (MvPolynomial.C r) = unitRingHom _ U r :=
  MvPolynomial.eval₂Hom_C _ _ _

lemma chartRingHom_X (U : Y.Opens) (e : κ → Γ(E, U)) (k : κ) :
    E.chartRingHom U e (MvPolynomial.X k) = E.symDegreeOne U (e k) :=
  MvPolynomial.eval₂Hom_X' _ _ _

variable [Fintype κ] [DecidableEq κ] in
/-- **Local bases identify `Sym(E)` with a polynomial algebra**: over an affine open `U` on which
`E` has a frame `e`, the chart ring map `Γ(U, 𝒪_Y)[x_k] → Γ(U, Sym(E))` is bijective. -/
theorem chartRingHom_bijective {U : Y.Opens} (hU : IsAffineOpen U) {e : κ → Γ(E, U)}
    (he : Ringed.IsLocalFrame (R := Y.sheaf) E U e) :
    Function.Bijective (E.chartRingHom U e) := by
  have h : E.chartRingHom U e =
      (E.symUnitRingHom U).comp (frameSymmetricAlgebraEquiv he le_rfl).toRingEquiv.toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun k => ?_)
    · refine (E.chartRingHom_C U e r).trans ((E.symUnitRingHom_algebraMap U r).symm.trans ?_)
      exact congrArg (E.symUnitRingHom U)
        ((frameSymmetricAlgebraEquiv he le_rfl).commutes r).symm
    · refine (E.chartRingHom_X U e k).trans ?_
      refine congrArg (E.symUnitRingHom U) ((congrArg (SymmetricAlgebra.ι _ _) ?_).trans
        (frameSymmetricAlgebraEquiv_X he le_rfl k).symm)
      change e k = E.val.map (𝟙 _) (e k)
      simp
      rfl
  rw [h]
  exact (moduleSheafSymmetricAlgebra_sheafifyUnit_bijective he hU.isCompact).comp
    (frameSymmetricAlgebraEquiv he le_rfl).bijective

/-- **The chart ring maps are compatible with restriction**: for `V ⊆ U`, restricting
`Γ(U, Sym(E)) → Γ(V, Sym(E))` after the chart of `e` is the chart of the restricted family `e|_V`
after restricting coefficients. -/
theorem chartRingHom_naturality {U V : Y.Opens} (h : V ≤ U) (e : κ → Γ(E, U))
    (p : MvPolynomial κ Γ(Y, U)) :
    sectionsRestrict _ (homOfLE h) (E.chartRingHom U e p) =
      E.chartRingHom V (fun k => E.presheaf.map (homOfLE h).op (e k))
        (MvPolynomial.map (Y.presheaf.map (homOfLE h).op).hom p) := by
  have := MvPolynomial.ringHom_ext (f := (sectionsRestrict _ (homOfLE h)).hom.comp
      (E.chartRingHom U e))
    (g := (E.chartRingHom V (fun k => E.presheaf.map (homOfLE h).op (e k))).comp
      (MvPolynomial.map (Y.presheaf.map (homOfLE h).op).hom))
    (fun r => by
      simp only [RingHom.comp_apply, MvPolynomial.map_C]
      rw [chartRingHom_C, chartRingHom_C]
      exact unitRingHom_naturality _ _ r)
    (fun k => by
      simp only [RingHom.comp_apply, MvPolynomial.map_X]
      rw [chartRingHom_X, chartRingHom_X]
      exact E.symDegreeOne_naturality _ _)
  exact RingHom.congr_fun this p

variable [Fintype κ] [DecidableEq κ] in
/-- **Changes of basis are linear**: for two frames `e`, `e'` of `E` over `V`, the chart of `e'` is
the chart of `e` after the linear substitution `x_k ↦ ∑_l a_{kl} x_l`, where
`e'_k = ∑_l a_{kl} e_l`. -/
theorem chartRingHom_transition {V : Y.Opens} {e : κ → Γ(E, V)}
    (he : Ringed.IsLocalFrame (R := Y.sheaf) E V e) (e' : κ → Γ(E, V)) :
    ∃ a : Matrix κ κ Γ(Y, V), ∀ k, E.chartRingHom V e' (MvPolynomial.X k) =
      E.chartRingHom V e (∑ l, MvPolynomial.C (a k l) * MvPolynomial.X l) := by
  let b := ExteriorPerfectPairing.frameBasis E he le_rfl
  have hb : ∀ l, b l = e l := fun l => by
    refine (ExteriorPerfectPairing.frameBasis_apply E he le_rfl l).trans ?_
    change E.val.map (𝟙 _) (e l) = e l
    simp
    rfl
  refine ⟨fun k l => b.repr (e' k) l, fun k => ?_⟩
  have hsum : e' k = ∑ l, (show Γ(Y, V) from b.repr (e' k) l) • e l :=
    (b.sum_repr (e' k)).symm.trans (Finset.sum_congr rfl fun l _ => by rw [hb l]; rfl)
  refine (E.chartRingHom_X V e' k).trans ((congrArg (E.symDegreeOne V) hsum).trans
    ((E.symDegreeOne_sum V Finset.univ _).trans ?_))
  rw [map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul]
  exact (E.symDegreeOne_smul V _ _).trans (congrArg₂ (· * ·) (E.chartRingHom_C V e _).symm
    (E.chartRingHom_X V e l).symm)

end

end AlgebraicGeometry.Scheme.Modules

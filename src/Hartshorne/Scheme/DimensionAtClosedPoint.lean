/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Dimension.DimFormula
import Hartshorne.Scheme.FiniteType
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Dimension at a closed point

Hartshorne, *Algebraic Geometry*, Exercise II.3.20(a) (p. 94).

For an integral scheme of finite type over a field, the dimension of the
scheme equals the Krull dimension of the local ring at any closed point.
-/

namespace Hartshorne

open CategoryTheory TopologicalSpace Topology
open AlgebraicGeometry

universe u

noncomputable section

/-- **Exercise II.3.20(a).** The dimension of an integral scheme of finite
type over a field equals the dimension of its local ring at every closed
point. -/
theorem dimension_at_closed_point
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsIntegral X]
    (hf : FiniteType f) (P : X) (hP : IsClosed ({P} : Set X)) :
    topologicalKrullDim X = ringKrullDim (X.presheaf.stalk P) := by
  let _ : LocallyOfFiniteType f := hf.1
  have htopK : genericPoint X ∈ f ⁻¹ᵁ (⊤ : (Spec (.of k)).Opens) := trivial
  let φK : k →+* X.functionField :=
    (X.presheaf.germ (f ⁻¹ᵁ (⊤ : (Spec (.of k)).Opens))
      (genericPoint X) htopK).hom.comp
        ((f.app ⊤).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
  letI : Algebra k X.functionField := φK.toAlgebra
  have affine_data (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
      ∃ d : ℕ, topologicalKrullDim U = d ∧
        Algebra.trdeg k X.functionField = d ∧
        ∀ (x : U), IsClosed ({(x : X)} : Set X) →
          ringKrullDim (X.presheaf.stalk (x : X)) = d := by
    have hUle : U ≤ f ⁻¹ᵁ (⊤ : (Spec (.of k)).Opens) := by simp
    let φU : k →+* Γ(X, U) :=
      (f.appLE ⊤ U hUle).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
    letI : Algebra k Γ(X, U) := φU.toAlgebra
    have hinv : Function.Surjective (Scheme.ΓSpecIso (.of k)).inv := by
      intro z
      exact ⟨(Scheme.ΓSpecIso (.of k)).hom z, by simp⟩
    have hφU : φU.FiniteType :=
      (f.finiteType_appLE (isAffineOpen_top _) hU hUle).comp
        (RingHom.FiniteType.of_surjective _ hinv)
    letI : Algebra.FiniteType k Γ(X, U) := hφU
    letI : IsScalarTower k Γ(X, U) X.functionField :=
      IsScalarTower.of_algebraMap_eq fun a => by
        change φK a = X.germToFunctionField U (φU a)
        simp only [φK, φU, RingHom.coe_comp, Function.comp_apply]
        convert
          (X.presheaf.germ_res_apply (homOfLE hUle) (genericPoint X)
            (((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
              (by simpa using (inferInstance : Nonempty U)))
            (f.app ⊤ ((Scheme.ΓSpecIso (.of k)).inv a))).symm using 1 <;>
          simp [Scheme.Hom.appLE, Scheme.germToFunctionField, Scheme.functionField,
            ConcreteCategory.comp_apply] <;> rfl
    letI : IsFractionRing Γ(X, U) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X U hU
    obtain ⟨d, hRing, htr⟩ :=
      exists_ringKrullDim_eq_trdeg k Γ(X, U) X.functionField
    have htop : topologicalKrullDim U = d := by
      rw [IsHomeomorph.topologicalKrullDim_eq _ hU.isoSpec.hom.homeomorph.isHomeomorph]
      change topologicalKrullDim (PrimeSpectrum Γ(X, U)) = (d : WithBot ℕ∞)
      rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, hRing]
    refine ⟨d, htop, htr, ?_⟩
    intro x hx
    let p := (hU.primeIdealOf x).asIdeal
    letI : p.IsMaximal := hU.primeIdealOf_isMaximal_of_isClosed x hx
    letI : IsLocalization.AtPrime (X.presheaf.stalk (x : X)) p :=
      hU.isLocalization_stalk x
    have hpheight : ((p.height : ℕ∞) : WithBot ℕ∞) = ringKrullDim Γ(X, U) :=
      height_eq_ringKrullDim_of_isMaximal k Γ(X, U) p
    have hlocal : ringKrullDim (X.presheaf.stalk (x : X)) =
        ((p.height : ℕ∞) : WithBot ℕ∞) := by
      exact IsLocalization.AtPrime.ringKrullDim_eq_height p _
    exact hlocal.trans (hpheight.trans hRing)
  obtain ⟨_, ⟨U, hU, rfl⟩, hPU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show P ∈ (⊤ : X.Opens) from trivial) isOpen_univ
  letI : Nonempty U := ⟨⟨P, hPU⟩⟩
  obtain ⟨r, hUdim, hXtr, hUclosed⟩ := affine_data U hU
  have hXdim : topologicalKrullDim X = (r : WithBot ℕ∞) := by
    apply le_antisymm
    · rw [topologicalKrullDim, Order.krullDim]
      refine iSup_le fun l => ?_
      obtain ⟨p, hp⟩ := (l 0).isIrreducible.nonempty
      obtain ⟨_, ⟨W, hW, rfl⟩, hpW, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open
          (show p ∈ (⊤ : X.Opens) from trivial) isOpen_univ
      letI : Nonempty W := ⟨⟨p, hpW⟩⟩
      obtain ⟨d, hWdim, hWtr, -⟩ := affine_data W hW
      have hdr : d = r := by
        have hcard : (d : Cardinal) = r := hWtr.symm.trans hXtr
        exact_mod_cast hcard
      have hmeet : ∀ m,
          ((fun z : W => (z : X)) ⁻¹' (l m : Set X)).Nonempty := by
        intro m
        refine ⟨⟨p, hpW⟩, ?_⟩
        exact l.monotone (Fin.zero_le m) hp
      have hchain : (l.length : WithBot ℕ∞) ≤ topologicalKrullDim W := by
        let e := TopologicalSpace.IrreducibleCloseds.orderIsoOfIsOpenEmbedding
          (fun z : ↥(↑W : Set X) => (z : X)) W.isOpen.isOpenEmbedding_subtypeVal
        change (l.length : WithBot ℕ∞) ≤
          Order.krullDim (IrreducibleCloseds ↥(↑W : Set X))
        rw [Order.krullDim_eq_of_orderIso e]
        exact Order.LTSeries.length_le_krullDim
          ⟨l.length, fun m => ⟨l m, hmeet m⟩, fun m => l.step m⟩
      rw [hWdim, hdr] at hchain
      exact hchain
    · rw [← hUdim]
      exact IsInducing.subtypeVal.topologicalKrullDim_le
  exact hXdim.trans (hUclosed ⟨P, hPU⟩ hP).symm

end

end Hartshorne

/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.ExternalProduct
import Hartshorne.RingedSpace.FiniteLocallyFreeProjectionFormula
import Hartshorne.RingedSpace.PicardGroup
import Hartshorne.Scheme.DimensionCodimension
import Hartshorne.Scheme.Differentials.DifferentialsCharacterizeNonsingular
import Hartshorne.Scheme.Differentials.DifferentialsOfProduct
import Hartshorne.Scheme.LocallyFreeRinged

/-!
# Products of nonsingular varieties

Let `k` be an algebraically closed field. If `X` and `Y` are nonsingular varieties over `k`, then
`X ×_k Y` is a nonsingular variety of dimension `dim X + dim Y`. This is used implicitly in
Hartshorne, *Algebraic Geometry*, II, Exercise 8.3(b) (pp. 187–188).

## Proof

* *Charts.* For nonempty affine opens `Spec A ⊆ X` and `Spec B ⊆ Y`, the open
  `fst⁻¹ (Spec A) ∩ snd⁻¹ (Spec B)` of `X ×_k Y` is `Spec (A ⊗_k B)`, and `A ⊗_k B` is a domain of
  dimension `dim A + dim B` (`k` is algebraically closed).
* *Integral.* The charts cover `X ×_k Y`, so its local rings are localizations of domains and it
  is reduced; the product of the closures of the generic points of `X` and `Y` is the closure of a
  point, so `X ×_k Y` is irreducible.
* *Dimension.* For an integral scheme of finite type over `k`, every nonempty affine open has the
  dimension of the scheme; apply this to one chart and to its two factors.
* *Nonsingular.* By Theorem II.8.15, `Ω_{X/k}` and `Ω_{Y/k}` are locally free of ranks `dim X` and
  `dim Y`. Then `Ω_{X×Y/k} ≅ p_X^* Ω_{X/k} ⊕ p_Y^* Ω_{Y/k}` (Exercise II.8.3(a)) is locally free of
  rank `dim X + dim Y = dim (X ×_k Y)`, and Theorem II.8.15 applies to `X ×_k Y`.

## Main results

* `Hartshorne.product_nonsingular_variety`: the product of nonsingular varieties over an
  algebraically closed field is a nonsingular variety of dimension `dim X + dim Y`.
-/

open CategoryTheory Limits Topology
open scoped TensorProduct

namespace Hartshorne

open AlgebraicGeometry

universe u

noncomputable section

namespace ProductNonsingular

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

/-- The pullback of a module sheaf that is locally free of rank `r` is locally free of rank `r`. -/
theorem isLocallyFreeOfRank_pullback {X Y : Scheme.{u}} (f : X ⟶ Y) {F : Y.Modules} {r : ℕ}
    (hF : F.IsLocallyFreeOfRank r) :
    ((Scheme.Modules.pullback f).obj F).IsLocallyFreeOfRank r := by
  classical
  rw [Scheme.Modules.isLocallyFreeOfRank_iff_ringed] at hF ⊢
  refine Ringed.isLocallyFreeOfRank_of_isLocalFrame fun x => ?_
  obtain ⟨U, e, hx, he⟩ := Ringed.exists_isLocalFrame_of_isLocallyFreeOfRank hF (f.base x)
  exact ⟨f ⁻¹ᵁ U, _, hx, Ringed.IsLocalFrame.pullback (φ := f.toRingCatSheafHom) he⟩

/-- A module sheaf that is free of rank `r` on an open `U` is free of rank `r` on every smaller
open `V`. -/
def restrictFreeOfLE {X : Scheme.{u}} {U V : X.Opens} (h : V ≤ U) (M : X.Modules) {r : ℕ}
    (e : (Scheme.Modules.restrictFunctor U.ι).obj M ≅ SheafOfModules.free (ULift.{u} (Fin r))) :
    (Scheme.Modules.restrictFunctor V.ι).obj M ≅ SheafOfModules.free (ULift.{u} (Fin r)) :=
  ((Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h).symm).app M :
      (Scheme.Modules.restrictFunctor V.ι).obj M ≅
        (Scheme.Modules.restrictFunctor (X.homOfLE h ≫ U.ι)).obj M) ≪≫
    ((Scheme.Modules.restrictFunctorComp (X.homOfLE h) U.ι).app M :
      (Scheme.Modules.restrictFunctor (X.homOfLE h ≫ U.ι)).obj M ≅
        (Scheme.Modules.restrictFunctor (X.homOfLE h)).obj
          ((Scheme.Modules.restrictFunctor U.ι).obj M)) ≪≫
    (Scheme.Modules.restrictFunctor (X.homOfLE h)).mapIso e ≪≫
    Scheme.Modules.restrictFreeIso (X.homOfLE h) _

/-- The direct sum of module sheaves locally free of ranks `m` and `n` is locally free of rank
`m + n`. -/
theorem isLocallyFreeOfRank_biprod {X : Scheme.{u}} {F G : X.Modules} {m n : ℕ}
    (hF : F.IsLocallyFreeOfRank m) (hG : G.IsLocallyFreeOfRank n) :
    (F ⊞ G).IsLocallyFreeOfRank (m + n) := by
  intro x
  obtain ⟨U₁, hx₁, ⟨α⟩⟩ := hF x
  obtain ⟨U₂, hx₂, ⟨β⟩⟩ := hG x
  refine ⟨U₁ ⊓ U₂, ⟨hx₁, hx₂⟩, ⟨?_⟩⟩
  let e : ULift.{u} (Fin m) ⊕ ULift.{u} (Fin n) ≃ ULift.{u} (Fin (m + n)) :=
    (Equiv.sumCongr Equiv.ulift Equiv.ulift).trans (finSumFinEquiv.trans Equiv.ulift.symm)
  exact (Scheme.Modules.restrictFunctor (U₁ ⊓ U₂).ι).mapIso (biprod.isoCoprod F G) ≪≫
    (PreservesColimitPair.iso (Scheme.Modules.restrictFunctor (U₁ ⊓ U₂).ι) F G).symm ≪≫
    coprod.mapIso (restrictFreeOfLE inf_le_left F α) (restrictFreeOfLE inf_le_right G β) ≪≫
    SheafOfModules.freeSumIso _ _ ≪≫ SheafOfModules.freeFunctor.mapIso e.toIso

/-- Every point of a scheme lies in an affine open. -/
theorem exists_isAffineOpen_mem {Z : Scheme.{u}} (z : Z) : ∃ U : Z.Opens, IsAffineOpen U ∧ z ∈ U := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open (show z ∈ (⊤ : Z.Opens) from trivial)
      isOpen_univ
  exact ⟨U, hU, hzU⟩

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (pX : X ⟶ Spec (.of k))
  (pY : Y ⟶ Spec (.of k))

/-- **The product chart.** For nonempty affine opens `Spec A = U ⊆ X` and `Spec B = V ⊆ Y` of
integral schemes locally of finite type over an algebraically closed field `k`, there is an open
immersion `Spec (A ⊗_k B) ⟶ X ×_k Y` whose image contains `fst⁻¹ U ∩ snd⁻¹ V`; the ring
`A ⊗_k B` is a domain of dimension `dim A + dim B`. -/
theorem exists_chart [IsAlgClosed k] [IsIntegral X] [IsIntegral Y] [LocallyOfFiniteType pX]
    [LocallyOfFiniteType pY] {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] {V : Y.Opens}
    (hV : IsAffineOpen V) [Nonempty V] :
    ∃ (R : CommRingCat.{u}) (ψ : Spec R ⟶ pullback pX pY), IsOpenImmersion ψ ∧ IsDomain R ∧
      (∀ z : ↑(pullback pX pY), pullback.fst pX pY z ∈ U → pullback.snd pX pY z ∈ V →
        z ∈ Set.range ψ) ∧
      ringKrullDim R = ringKrullDim Γ(X, U) + ringKrullDim Γ(Y, V) := by
  let a : CommRingCat.of k ⟶ Γ(X, U) := Spec.preimage (hU.fromSpec ≫ pX)
  let _ : Algebra k Γ(X, U) := a.hom.toAlgebra
  have hφA : Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U))) = hU.fromSpec ≫ pX := by
    change Spec.map (CommRingCat.ofHom a.hom) = _
    simp [a]
  have : Algebra.FiniteType k Γ(X, U) := by
    have : LocallyOfFiniteType (Spec.map a) := by rw [Spec.map_preimage]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this
  let b : CommRingCat.of k ⟶ Γ(Y, V) := Spec.preimage (hV.fromSpec ≫ pY)
  let _ : Algebra k Γ(Y, V) := b.hom.toAlgebra
  have hφB : Spec.map (CommRingCat.ofHom (algebraMap k Γ(Y, V))) = hV.fromSpec ≫ pY := by
    change Spec.map (CommRingCat.ofHom b.hom) = _
    simp [b]
  have : Algebra.FiniteType k Γ(Y, V) := by
    have : LocallyOfFiniteType (Spec.map b) := by rw [Spec.map_preimage]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this
  have : IsDomain (Γ(X, U) ⊗[k] Γ(Y, V)) := ExternalProduct.isDomain_tensorProduct k _ _
  let E : Spec (.of (Γ(X, U) ⊗[k] Γ(Y, V))) ≅ pullback (hU.fromSpec ≫ pX) (hV.fromSpec ≫ pY) :=
    (pullbackSpecIso k Γ(X, U) Γ(Y, V)).symm ≪≫ pullback.congrHom hφA hφB
  let m : pullback (hU.fromSpec ≫ pX) (hV.fromSpec ≫ pY) ⟶ pullback pX pY :=
    pullback.map _ _ pX pY hU.fromSpec hV.fromSpec (𝟙 _) (by simp) (by simp)
  refine ⟨.of (Γ(X, U) ⊗[k] Γ(Y, V)), E.hom ≫ m, inferInstance, ‹_›, fun z hzU hzV => ?_,
    ringKrullDim_tensorProduct k _ _⟩
  obtain ⟨w, hw⟩ : z ∈ Set.range m := by
    rw [Scheme.Pullback.range_map, hU.range_fromSpec, hV.range_fromSpec]
    exact ⟨hzU, hzV⟩
  refine ⟨E.inv w, ?_⟩
  rw [← hw, ← Scheme.Hom.comp_apply]
  simp

/-- Over an algebraically closed field, the product of integral schemes locally of finite type is
reduced: its local rings are localizations of the domains `A ⊗_k B`. -/
theorem isReduced_pullback [IsAlgClosed k] [IsIntegral X] [IsIntegral Y] [LocallyOfFiniteType pX]
    [LocallyOfFiniteType pY] : IsReduced (pullback pX pY) := by
  have (z : ↑(pullback pX pY)) : _root_.IsReduced ((pullback pX pY).presheaf.stalk z) := by
    obtain ⟨U, hU, hzU⟩ := exists_isAffineOpen_mem (pullback.fst pX pY z)
    obtain ⟨V, hV, hzV⟩ := exists_isAffineOpen_mem (pullback.snd pX pY z)
    have : Nonempty U := ⟨⟨_, hzU⟩⟩
    have : Nonempty V := ⟨⟨_, hzV⟩⟩
    obtain ⟨R, ψ, hψ, hR, hcov, -⟩ := exists_chart pX pY hU hV
    obtain ⟨w, rfl⟩ := hcov z hzU hzV
    exact isReduced_of_injective (ψ.stalkMap w).hom
      (ConcreteCategory.bijective_of_isIso (ψ.stalkMap w)).1
  exact isReduced_of_isReduced_stalk _

/-- Over an algebraically closed field, the product of integral schemes locally of finite type is
irreducible: it is the closure of the generic point of the product of the closures of the generic
points of the factors. -/
theorem irreducibleSpace_pullback [IsAlgClosed k] [IsIntegral X] [IsIntegral Y]
    [LocallyOfFiniteType pX] [LocallyOfFiniteType pY] : IrreducibleSpace ↑(pullback pX pY) := by
  obtain ⟨ξ, hξ, -⟩ :=
    ExternalProduct.exists_closure_eq_preimage_inter pX pY (genericPoint X) (genericPoint Y)
  rw [genericPoint_closure, genericPoint_closure, Set.preimage_univ,
    Set.preimage_univ, Set.inter_self] at hξ
  refine (irreducibleSpace_def _).2 ?_
  rw [Set.top_eq_univ, ← hξ]
  exact isIrreducible_singleton.closure

/-- Over an algebraically closed field, the product of integral schemes locally of finite type is
integral. -/
theorem isIntegral_pullback [IsAlgClosed k] [IsIntegral X] [IsIntegral Y] [LocallyOfFiniteType pX]
    [LocallyOfFiniteType pY] : IsIntegral (pullback pX pY) := by
  have := isReduced_pullback pX pY
  have := irreducibleSpace_pullback pX pY
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- The product of schemes of finite type over `k` is of finite type over `k`. -/
theorem finiteType_pullback (hX : FiniteType pX) (hY : FiniteType pY) :
    FiniteType (pullback.fst pX pY ≫ pX) := by
  have := hX.1; have := hX.2; have := hY.1; have := hY.2
  exact ⟨inferInstance, inferInstance⟩

/-- An integral scheme of finite type over `k` has finite dimension. -/
theorem exists_topologicalKrullDim_eq [IsIntegral X] (hX : FiniteType pX) :
    ∃ N : ℕ, topologicalKrullDim X = N := by
  obtain ⟨U, hU, hxU⟩ := exists_isAffineOpen_mem (Nonempty.some (inferInstance : Nonempty X))
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  obtain ⟨N, -, hN⟩ := DimensionCodimension.exists_ringKrullDim_eq pX hX U hU
  exact ⟨N, hN⟩

/-- Over an algebraically closed field, `dim (X ×_k Y) = dim X + dim Y` for integral schemes `X`,
`Y` of finite type over `k`. -/
theorem topologicalKrullDim_pullback [IsAlgClosed k] [IsIntegral X] [IsIntegral Y]
    (hX : FiniteType pX) (hY : FiniteType pY) :
    topologicalKrullDim ↑(pullback pX pY) = topologicalKrullDim X + topologicalKrullDim Y := by
  have := hX.1; have := hY.1
  obtain ⟨U, hU, hxU⟩ := exists_isAffineOpen_mem (Nonempty.some (inferInstance : Nonempty X))
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  obtain ⟨V, hV, hyV⟩ := exists_isAffineOpen_mem (Nonempty.some (inferInstance : Nonempty Y))
  have : Nonempty V := ⟨⟨_, hyV⟩⟩
  obtain ⟨R, ψ, hψ, hR, -, hdim⟩ := exists_chart pX pY hU hV
  have := isIntegral_pullback pX pY
  have hW : IsAffineOpen (ψ ''ᵁ ⊤) := (isAffineOpen_top (Spec R)).image_of_isOpenImmersion ψ
  have : Nonempty (Spec R) := inferInstance
  have : Nonempty (ψ ''ᵁ ⊤) :=
    ⟨⟨ψ (Nonempty.some this), ⟨Nonempty.some this, trivial, rfl⟩⟩⟩
  obtain ⟨N, hN, hNP⟩ :=
    DimensionCodimension.exists_ringKrullDim_eq _ (finiteType_pullback pX pY hX hY) _ hW
  obtain ⟨a, ha, haX⟩ := DimensionCodimension.exists_ringKrullDim_eq pX hX U hU
  obtain ⟨b, hb, hbY⟩ := DimensionCodimension.exists_ringKrullDim_eq pY hY V hV
  have he : ringKrullDim Γ(pullback pX pY, ψ ''ᵁ ⊤) = ringKrullDim R :=
    (ringKrullDim_eq_of_ringEquiv (ψ.appIso ⊤).commRingCatIsoToRingEquiv).trans
      (ringKrullDim_eq_of_ringEquiv (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv)
  rw [hNP, haX, hbY, ← hN, he, hdim, ha, hb]

/-- Over an algebraically closed field, the product of nonsingular integral schemes of finite type
is nonsingular. -/
theorem isRegular_pullback [IsAlgClosed k] [IsIntegral X] [IsIntegral Y] (hX : FiniteType pX)
    (hY : FiniteType pY) (hXr : X.IsRegular) (hYr : Y.IsRegular) :
    (pullback pX pY).IsRegular := by
  have := hX.1; have := hY.1
  obtain ⟨m, hm⟩ := exists_topologicalKrullDim_eq pX hX
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_eq pY hY
  have hΩX := (isRegular_iff_relativeDifferentials_isLocallyFreeOfRank pX hX m hm).1 hXr
  have hΩY := (isRegular_iff_relativeDifferentials_isLocallyFreeOfRank pY hY n hn).1 hYr
  have := irreducibleSpace_pullback pX pY
  have hdim : topologicalKrullDim ↑(pullback pX pY) = ((m + n : ℕ) : WithBot ℕ∞) := by
    rw [topologicalKrullDim_pullback pX pY hX hY, hm, hn]
    rfl
  refine (isRegular_iff_relativeDifferentials_isLocallyFreeOfRank (pullback.fst pX pY ≫ pX)
    (finiteType_pullback pX pY hX hY) (m + n) hdim).2 ?_
  have h := isLocallyFreeOfRank_biprod (isLocallyFreeOfRank_pullback (pullback.fst pX pY) hΩX)
    (isLocallyFreeOfRank_pullback (pullback.snd pX pY) hΩY)
  intro z
  obtain ⟨W, hz, ⟨e⟩⟩ := h z
  exact ⟨W, hz, ⟨(Scheme.Modules.restrictFunctor W.ι).mapIso
    (Scheme.relativeDifferentialsProductIso pX pY) ≪≫ e⟩⟩

end ProductNonsingular

open ProductNonsingular

/-- **Products of nonsingular varieties.** Let `k` be an algebraically closed field. If `X` and
`Y` are nonsingular varieties over `k` (integral, separated, of finite type, with regular local
rings), then `X ×_k Y` is a nonsingular variety over `k` of dimension `dim X + dim Y`. This fact
is used implicitly in Hartshorne II, Exercise 8.3(b). -/
theorem product_nonsingular_variety {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k)) [IsIntegral X] [IsIntegral Y]
    (hX : FiniteType pX) (hY : FiniteType pY) [IsSeparated pX] [IsSeparated pY]
    (hXr : X.IsRegular) (hYr : Y.IsRegular) :
    IsIntegral (pullback pX pY) ∧ IsSeparated (pullback.fst pX pY ≫ pX) ∧
      FiniteType (pullback.fst pX pY ≫ pX) ∧ (pullback pX pY).IsRegular ∧
      topologicalKrullDim ↑(pullback pX pY) = topologicalKrullDim X + topologicalKrullDim Y := by
  have := hX.1; have := hY.1
  exact ⟨isIntegral_pullback pX pY, inferInstance, finiteType_pullback pX pY hX hY,
    isRegular_pullback pX pY hX hY hXr hYr, topologicalKrullDim_pullback pX pY hX hY⟩

end

end Hartshorne

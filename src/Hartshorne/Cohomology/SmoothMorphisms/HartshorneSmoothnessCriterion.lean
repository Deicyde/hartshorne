/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.SmoothMorphisms.SmoothnessCriterion
import Hartshorne.Cohomology.SmoothMorphisms.DifferentialCriterionSchemeOverField

/-!
# Hartshorne's smoothness criterion

Hartshorne, *Algebraic Geometry*, III.10, definition on p. 268.

For a morphism `f : X → Y` of schemes of finite type over a field, Mathlib's smoothness of relative
dimension `n` is equivalent to Hartshorne's three conditions: `f` is flat; every irreducible
component of every scheme-theoretic fibre has dimension `n`; and
`dim_{k(x)} ((Ω_{X/Y})_x ⊗ k(x)) = n` for every `x ∈ X`.

The forward direction is `Hartshorne.flat_and_fiber_dim_and_finrank_of_smoothOfRelativeDimension`.
For the converse, each fibre `X_y → Spec k(y)` is smooth by the differential criterion for a scheme
over a field (`Hartshorne.smooth_of_forall_topologicalKrullDim_eq_of_finrank_fibre_le`): its
components have dimension `n`, and the fibres of `Ω_{X_y/k(y)}` have the same dimensions as fibres
of `Ω_{X/Y}`. The latter is checked on affine charts `Spec (κ(p) ⊗_A B)` of `X_y`, where
`Ω_{κ(p) ⊗_A B / κ(p)} ≅ (κ(p) ⊗_A B) ⊗_B Ω_{B/A}`. Flatness and smooth fibres then give
smoothness (`Scheme.smoothOfRelativeDimension_of_flat_of_smooth_fiber`).
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct IsLocalRing Module

namespace Hartshorne

universe u

section Algebra

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The fibre of `Ω_{κ(p) ⊗_R S / κ(p)}` at a prime `Q` has the same dimension as the fibre of
`Ω_{S/R}` at the contraction of `Q` to `S`. -/
theorem finrank_tensor_kaehler_fiber {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] (Q : Ideal (p.Fiber S)) [Q.IsPrime] :
    finrank Q.ResidueField (Q.ResidueField ⊗[p.Fiber S] Ω[p.Fiber S⁄p.ResidueField]) =
      finrank (Q.comap (algebraMap S (p.Fiber S))).ResidueField
        ((Q.comap (algebraMap S (p.Fiber S))).ResidueField ⊗[S] Ω[S⁄R]) := by
  set T := p.Fiber S
  set q := Q.comap (algebraMap S T)
  let φ : q.ResidueField →+* Q.ResidueField := Ideal.ResidueField.map q Q (algebraMap S T) rfl
  let : Algebra q.ResidueField Q.ResidueField := φ.toAlgebra
  have : IsScalarTower S q.ResidueField Q.ResidueField := IsScalarTower.of_algebraMap_eq
    fun s => by
      rw [IsScalarTower.algebraMap_apply S T Q.ResidueField]
      exact (Ideal.ResidueField.map_algebraMap q Q (algebraMap S T) rfl s).symm
  let e₁ : Q.ResidueField ⊗[T] Ω[T⁄p.ResidueField] ≃ₗ[Q.ResidueField]
      Q.ResidueField ⊗[S] Ω[S⁄R] :=
    (AlgebraTensorModule.congr (LinearEquiv.refl Q.ResidueField Q.ResidueField)
      (KaehlerDifferential.tensorKaehlerEquiv R p.ResidueField S T).symm).trans
      (AlgebraTensorModule.cancelBaseChange S T Q.ResidueField Q.ResidueField Ω[S⁄R])
  let e₂ : Q.ResidueField ⊗[q.ResidueField] (q.ResidueField ⊗[S] Ω[S⁄R]) ≃ₗ[Q.ResidueField]
      Q.ResidueField ⊗[S] Ω[S⁄R] :=
    AlgebraTensorModule.cancelBaseChange S q.ResidueField Q.ResidueField Q.ResidueField Ω[S⁄R]
  rw [e₁.finrank_eq, ← e₂.finrank_eq, Module.finrank_baseChange]

end Algebra

section Fibre

set_option maxHeartbeats 400000 in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- Every fibre of `Ω_{X_y/k(y)}` on the scheme-theoretic fibre `X_y = X ×_Y Spec k(y)` of
`f : X → Y` has the same dimension as some fibre of `Ω_{X/Y}` (pullback form). -/
theorem exists_finrank_fibre_pullback_snd_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y)
    (z : ↥(pullback f (Y.fromSpecResidueField y))) :
    ∃ x : X, finrank (ResidueField ((pullback f (Y.fromSpecResidueField y)).presheaf.stalk z))
        (ResidueField ((pullback f (Y.fromSpecResidueField y)).presheaf.stalk z) ⊗[
          (pullback f (Y.fromSpecResidueField y)).presheaf.stalk z]
          (Scheme.relativeDifferentials (pullback.snd f (Y.fromSpecResidueField y))).presheaf.stalk
            z) =
      finrank (ResidueField (X.presheaf.stalk x))
        (ResidueField (X.presheaf.stalk x) ⊗[X.presheaf.stalk x]
          (Scheme.relativeDifferentials f).presheaf.stalk x) := by
  classical
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hzy : f (pullback.fst f (Y.fromSpecResidueField y) z) = y := by
    have : f.fiberι y z ∈ f ⁻¹' {y} := f.range_fiberι y ▸ ⟨z, rfl⟩
    exact this
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show pullback.fst f (Y.fromSpecResidueField y) z ∈ (f ⁻¹ᵁ V : Set X) from by
      simpa [hzy] using hyV) (f ⁻¹ᵁ V).2
  let iV : Spec (.of Γ(Y, V)) ⟶ Y := hV.fromSpec
  let iU : Spec (.of Γ(X, U)) ⟶ X := hU.fromSpec
  obtain ⟨p, rfl⟩ : y ∈ Set.range iV := by
    show y ∈ Set.range hV.fromSpec
    rw [hV.range_fromSpec]; exact hyV
  have : p.asIdeal.IsPrime := p.2
  let : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  let g : Spec (.of Γ(X, U)) ⟶ Spec (.of Γ(Y, V)) :=
    Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, V) Γ(X, U)))
  have : IsOpenImmersion iU := hU.isOpenImmersion_fromSpec
  have : IsOpenImmersion iV := hV.isOpenImmersion_fromSpec
  have hcomm : iU ≫ f = g ≫ iV := (IsAffineOpen.SpecMap_appLE_fromSpec f hV hU hUV).symm
  let y' := iV p
  -- the open immersion of the fibre of `U → Y` into the fibre of `X → Y`
  let J : pullback (iU ≫ f) (Y.fromSpecResidueField y') ⟶ pullback f (Y.fromSpecResidueField y') :=
    (pullbackRightPullbackFstIso f (Y.fromSpecResidueField y') iU).inv ≫ pullback.snd _ _
  have : IsOpenImmersion J := by dsimp only [J]; infer_instance
  have hJ : J ≫ pullback.snd f (Y.fromSpecResidueField y') =
      pullback.snd (iU ≫ f) (Y.fromSpecResidueField y') := by
    simp [J]
  let K : pullback (g ≫ iV) (Y.fromSpecResidueField y') ⟶
      pullback (iU ≫ f) (Y.fromSpecResidueField y') :=
    pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp [hcomm]) (by simp)
  have : IsIso K := by dsimp only [K]; infer_instance
  have hK : K ≫ pullback.snd (iU ≫ f) (Y.fromSpecResidueField y') =
      pullback.snd (g ≫ iV) (Y.fromSpecResidueField y') :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have h0 : IsPullback (𝟙 _) g (g ≫ iV) iV := by
    simpa using (IsPullback.id_horiz g).paste_vert (IsKernelPair.id_of_mono iV)
  obtain ⟨Tm, hT⟩ : ∃ Tm : pullback g ((Spec (.of Γ(Y, V))).fromSpecResidueField p) ⟶
      pullback (g ≫ iV) (Y.fromSpecResidueField y'),
      IsPullback Tm (pullback.snd g ((Spec (.of Γ(Y, V))).fromSpecResidueField p))
        (pullback.snd (g ≫ iV) (Y.fromSpecResidueField y'))
        (Spec.map (iV.residueFieldMap p)) :=
    ⟨_, isPullback_fiberToSpecResidueField_of_isPullback h0 p⟩
  have : IsIso (Spec.map (iV.residueFieldMap p)) :=
    (Scheme.Spec.mapIso (asIso (iV.residueFieldMap p)).op).isIso_hom
  have : IsIso Tm := hT.isIso_fst_of_isIso
  let e₁ := Spec.fiberToSpecResidueFieldIso Γ(Y, V) Γ(X, U) p
  let L : Spec (.of (p.asIdeal.Fiber Γ(X, U))) ⟶
      pullback g ((Spec (.of Γ(Y, V))).fromSpecResidueField p) := e₁.inv.left
  let M : Spec (.of p.asIdeal.ResidueField) ⟶ Spec ((Spec (.of Γ(Y, V))).residueField p) :=
    e₁.inv.right
  have : IsIso L := inferInstanceAs (IsIso e₁.inv.left)
  have : IsIso M := inferInstanceAs (IsIso e₁.inv.right)
  have hL : L ≫ pullback.snd g ((Spec (.of Γ(Y, V))).fromSpecResidueField p) =
      Spec.map (CommRingCat.ofHom (algebraMap p.asIdeal.ResidueField
        (p.asIdeal.Fiber Γ(X, U)))) ≫ M := Arrow.w e₁.inv
  let P := L ≫ Tm ≫ K
  have : IsIso P := by dsimp only [P]; infer_instance
  let E := P ≫ J
  let B := M ≫ Spec.map (iV.residueFieldMap p)
  have : IsOpenImmersion E := by dsimp only [E]; infer_instance
  have : IsOpenImmersion B := by dsimp only [B]; infer_instance
  have hw : E ≫ pullback.snd f (Y.fromSpecResidueField y') =
      Spec.map (CommRingCat.ofHom (algebraMap p.asIdeal.ResidueField
        (p.asIdeal.Fiber Γ(X, U)))) ≫ B := by
    simp only [E, P, B, Category.assoc, hJ, hK, hT.w]
    rw [← Category.assoc, hL, Category.assoc]
  have key : ∀ w, finrank (ResidueField ((pullback f (Y.fromSpecResidueField y')).presheaf.stalk
        (E w)))
      (ResidueField ((pullback f (Y.fromSpecResidueField y')).presheaf.stalk (E w)) ⊗[
        (pullback f (Y.fromSpecResidueField y')).presheaf.stalk (E w)]
        (Scheme.relativeDifferentials (pullback.snd f (Y.fromSpecResidueField y'))).presheaf.stalk
          (E w)) =
      finrank (ResidueField (X.presheaf.stalk
          (iU (PrimeSpectrum.comap (algebraMap Γ(X, U) (p.asIdeal.Fiber Γ(X, U))) w))))
        (ResidueField (X.presheaf.stalk
          (iU (PrimeSpectrum.comap (algebraMap Γ(X, U) (p.asIdeal.Fiber Γ(X, U))) w))) ⊗[
          X.presheaf.stalk
          (iU (PrimeSpectrum.comap (algebraMap Γ(X, U) (p.asIdeal.Fiber Γ(X, U))) w))]
          (Scheme.relativeDifferentials f).presheaf.stalk
          (iU (PrimeSpectrum.comap (algebraMap Γ(X, U) (p.asIdeal.Fiber Γ(X, U))) w))) := by
    intro w
    have : w.asIdeal.IsPrime := w.2
    have h1 := finrank_fibre_restrict E
      (Scheme.relativeDifferentials (pullback.snd f (Y.fromSpecResidueField y'))) w
    have h2 := finrank_fibre_eq_of_iso_tilde (R := .of (p.asIdeal.Fiber Γ(X, U))) _ _
      ((RelDiffLocal.restrictIso _ E _ B hw).symm ≪≫
        Scheme.relativeDifferentialsSpecIso p.asIdeal.ResidueField (p.asIdeal.Fiber Γ(X, U))) w
    have h3 := finrank_tensor_kaehler_fiber (S := Γ(X, U)) p.asIdeal w.asIdeal
    have h4 := finrank_fibre_relativeDifferentials_affine f ⟨U, hU⟩ ⟨V, hV⟩ hUV
      (PrimeSpectrum.comap (algebraMap Γ(X, U) (p.asIdeal.Fiber Γ(X, U))) w)
    exact h1.trans (h2.trans (h3.trans h4.symm))
  -- `z` lies in the image of `E`
  have hz : z ∈ Set.range (pullback.snd iU (pullback.fst f (Y.fromSpecResidueField y'))) := by
    rw [Scheme.Pullback.range_snd]
    show pullback.fst f (Y.fromSpecResidueField y') z ∈ Set.range hU.fromSpec
    rw [hU.range_fromSpec]
    exact hxU
  obtain ⟨w₀, rfl⟩ := hz
  let w₁ := (pullbackRightPullbackFstIso f (Y.fromSpecResidueField y') iU).hom w₀
  have hEw : E (inv P w₁) = pullback.snd iU (pullback.fst f (Y.fromSpecResidueField y')) w₀ :=
    calc E (inv P w₁) = (inv P ≫ P ≫ J) w₁ := (Scheme.Hom.comp_apply _ _ _).symm
      _ = J w₁ := by rw [IsIso.inv_hom_id_assoc]
      _ = ((pullbackRightPullbackFstIso f (Y.fromSpecResidueField y') iU).hom ≫ J) w₀ :=
        (Scheme.Hom.comp_apply _ _ _).symm
      _ = _ := by simp only [J, Iso.hom_inv_id_assoc]
  have := key (inv P w₁)
  rw [hEw] at this
  exact ⟨_, this⟩

/-- The converse of Hartshorne's smoothness criterion, for a flat morphism `f : X → Y` locally of
finite type and quasi-compact over a locally Noetherian base: if every irreducible component of
every fibre has dimension `n` and every fibre of `Ω_{X/Y}` has dimension `n`, then `f` is smooth of
relative dimension `n`. -/
theorem smoothOfRelativeDimension_of_flat_of_fiber_dim_of_finrank {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] [IsLocallyNoetherian Y] [Flat f] (n : ℕ)
    (hdim : ∀ y : Y, ∀ Z ∈ irreducibleComponents (f.fiber y), topologicalKrullDim Z = n)
    (hΩ : ∀ x : X, finrank (ResidueField (X.presheaf.stalk x))
      (ResidueField (X.presheaf.stalk x) ⊗[X.presheaf.stalk x]
        (Scheme.relativeDifferentials f).presheaf.stalk x) = n) :
    SmoothOfRelativeDimension n f := by
  refine Scheme.smoothOfRelativeDimension_of_flat_of_smooth_fiber f n (fun y => ?_) hΩ
  have hft : FiniteType (f.fiberToSpecResidueField y) :=
    ⟨inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _)),
      inferInstanceAs (QuasiCompact (pullback.snd _ _))⟩
  exact smooth_of_forall_topologicalKrullDim_eq_of_finrank_fibre_le (K := Y.residueField y)
    (f.fiberToSpecResidueField y) hft n (hdim y) fun z => by
      obtain ⟨x, hx⟩ := exists_finrank_fibre_pullback_snd_eq f y z
      exact (hx.trans (hΩ x)).le

/-- **Hartshorne III.10, definition of smoothness (p. 268).** Let `f : X → Y` be a morphism of
schemes of finite type over a field `k`. Then `f` is smooth of relative dimension `n` (Mathlib's
`SmoothOfRelativeDimension`) if and only if `f` is flat, every irreducible component of every
scheme-theoretic fibre `X_y` has dimension `n`, and `dim_{k(x)} ((Ω_{X/Y})_x ⊗ k(x)) = n` for
every `x ∈ X`. Hartshorne states the dimension condition with components of `X` and `Y`; the fibre
form is equivalent by III.9.6. -/
theorem smoothOfRelativeDimension_iff_flat_and_fiber_dim_and_finrank {k : Type u} [Field k]
    {X Y : Over (Spec (CommRingCat.of k))}
    (hX : LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom)
    (hY : LocallyOfFiniteType Y.hom ∧ QuasiCompact Y.hom) (f : X ⟶ Y) (n : ℕ) :
    SmoothOfRelativeDimension n f.left ↔
      Flat f.left ∧
        (∀ y : Y.left, ∀ Z ∈ irreducibleComponents (f.left.fiber y),
          topologicalKrullDim Z = n) ∧
        ∀ x : X.left, finrank (ResidueField (X.left.presheaf.stalk x))
          (ResidueField (X.left.presheaf.stalk x) ⊗[X.left.presheaf.stalk x]
            (Scheme.relativeDifferentials f.left).presheaf.stalk x) = n := by
  refine ⟨fun _ => flat_and_fiber_dim_and_finrank_of_smoothOfRelativeDimension hX hY f n,
    fun ⟨hflat, hdim, hΩ⟩ => ?_⟩
  have : LocallyOfFiniteType X.hom := hX.1
  have : LocallyOfFiniteType Y.hom := hY.1
  have : QuasiCompact X.hom := hX.2
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := {}
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [Over.w f]; infer_instance
  have : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left Y.hom
  have : QuasiCompact f.left := ⟨fun _ _ _ => TopologicalSpace.NoetherianSpace.isCompact _⟩
  exact smoothOfRelativeDimension_of_flat_of_fiber_dim_of_finrank f.left n hdim hΩ

end Fibre

end Hartshorne

/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.SmoothMorphisms.SmoothnessCriterion
import Hartshorne.Cohomology.SmoothMorphisms.DifferentialCriterionSchemeOverField
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Hartshorne's smoothness criterion

Hartshorne, *Algebraic Geometry*, III.10, definition on p. 268.

For a morphism `f : X → Y` of schemes of finite type over a field, Mathlib's smoothness of relative
dimension `n` is equivalent to Hartshorne's three conditions
(`smoothOfRelativeDimension_iff_flat_and_component_dim_and_finrank`): `f` is flat; if `X' ⊆ X` and
`Y' ⊆ Y` are irreducible components with `f(X') ⊆ Y'`, then `dim X' = dim Y' + n`; and
`dim_{k(x)} ((Ω_{X/Y})_x ⊗ k(x)) = n` for every `x ∈ X`.

For flat `f`, the second condition is equivalent to every irreducible component of every
scheme-theoretic fibre having dimension `n`
(`forall_irreducibleComponents_dim_eq_add_iff_forall_fiber`). A flat morphism is generalizing, so
it sends the generic point of a component of `X` to the generic point of a component of `Y`. Take a
closed point `x` of a fibre `X_y` lying on a single component of `X_y`. Proposition III.9.5 gives
`dim 𝒪_{X,x} = dim 𝒪_{X_y,x} + dim 𝒪_{Y,y}`, and the local dimensions are computed from the
components through `x` and `y` because schemes of finite type over a field are catenary. The
fibre form is `smoothOfRelativeDimension_iff_flat_and_fiber_dim_and_finrank`.

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

-- The chart-level pullback isomorphisms and the stalk rewriting need more than the default.
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

/-- **Hartshorne's smoothness criterion, fibre form.** Let `f : X → Y` be a morphism of
schemes of finite type over a field `k`. Then `f` is smooth of relative dimension `n` (Mathlib's
`SmoothOfRelativeDimension`) if and only if `f` is flat, every irreducible component of every
scheme-theoretic fibre `X_y` has dimension `n`, and `dim_{k(x)} ((Ω_{X/Y})_x ⊗ k(x)) = n` for
every `x ∈ X`. Hartshorne states the dimension condition with components of `X` and `Y`
(`smoothOfRelativeDimension_iff_flat_and_component_dim_and_finrank`); under flatness the fibre
form used here is equivalent (`forall_irreducibleComponents_dim_eq_add_iff_forall_fiber`). -/
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

section ComponentDimension

open TopologicalSpace Topology Order FlatEquidimensional

/-- An element of a catenary order lies below `g` with `height g ≤ height x + coheight x`. -/
theorem height_le_height_add_coheight {α : Type*} [Preorder α] {g x : α} (hC : CatenaryAt g)
    (hx : x ≤ g) : height g ≤ height x + coheight x := by
  obtain ⟨N, hN, h⟩ := hC
  rw [hN, ← h x hx]
  gcongr
  exact coheight_le_coheight_apply_of_strictMono Subtype.val (fun _ _ h => h) _

/-- In a catenary order in which every element lies below a maximal one, the coheight of `x` is
at most `c` once every maximal `g ≥ x` has `height g ≤ height x + c`. -/
theorem coheight_le_of_forall_isMax {α : Type*} [Preorder α] (hC : ∀ g : α, CatenaryAt g)
    (hmax : ∀ z : α, ∃ g, z ≤ g ∧ IsMax g) {x : α} {c : ℕ∞} (hx : height x ≠ ⊤)
    (h : ∀ g, x ≤ g → IsMax g → height g ≤ height x + c) : coheight x ≤ c := by
  refine coheight_le fun p hp => ?_
  obtain ⟨g, hg, hgm⟩ := hmax p.last
  have hxl : x ≤ p.last := hp ▸ p.monotone (Fin.zero_le _)
  have hxg : x ≤ g := hxl.trans hg
  have hlen := length_le_coheight_Iic p hp hg hxg
  obtain ⟨N, hN, hcat⟩ := hC g
  have h2 := h g hxg hgm
  rw [hN, ← hcat x hxg] at h2
  exact hlen.trans ((WithTop.add_le_add_iff_left hx).mp h2)

variable {S : Scheme.{u}}

/-- The specialization order on the points of a scheme is antisymmetric. -/
theorem eq_of_le_of_le {a b : S} (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b :=
  (Specializes.antisymm h₂ h₁).eq

/-- The generic point of an irreducible component is maximal for the specialization order. -/
theorem isMax_of_closure_mem_irreducibleComponents {ζ : S}
    (h : closure {ζ} ∈ irreducibleComponents S) : IsMax ζ := by
  intro z hz
  have hsub : closure {ζ} ⊆ closure {z} :=
    closure_minimal (Set.singleton_subset_iff.2 (specializes_iff_mem_closure.1 hz))
      isClosed_closure
  exact specializes_iff_mem_closure.2 (h.2 isIrreducible_singleton.closure hsub
    (subset_closure rfl))

/-- The closure of a maximal point is an irreducible component. -/
theorem closure_mem_irreducibleComponents_of_isMax {ζ : S} (h : IsMax ζ) :
    closure {ζ} ∈ irreducibleComponents S := by
  obtain ⟨g, hg⟩ := exists_closure_eq (irreducibleComponent_mem_irreducibleComponents ζ)
  have hle : ζ ≤ g := specializes_iff_mem_closure.mpr (hg ▸ mem_irreducibleComponent)
  rw [eq_of_le_of_le hle (h hle), hg]
  exact irreducibleComponent_mem_irreducibleComponents ζ

/-- Every point lies below a maximal point, the generic point of an irreducible component. -/
theorem exists_le_isMax (z : S) : ∃ g, z ≤ g ∧ IsMax g := by
  obtain ⟨g, hg⟩ := exists_closure_eq (irreducibleComponent_mem_irreducibleComponents z)
  exact ⟨g, specializes_iff_mem_closure.mpr (hg ▸ mem_irreducibleComponent),
    isMax_of_closure_mem_irreducibleComponents
      (hg ▸ irreducibleComponent_mem_irreducibleComponents z)⟩

/-- A generalizing morphism sends maximal points to maximal points. -/
theorem isMax_apply_of_generalizingMap {T : Scheme.{u}} (f : S ⟶ T) (hf : GeneralizingMap f)
    {ζ : S} (h : IsMax ζ) : IsMax (f ζ) := by
  intro w hw
  obtain ⟨x', hx', rfl⟩ := hf hw
  exact (h hx').map f.continuous

/-- `forall_irreducibleComponents_dim_eq_add_iff_forall_fiber` in terms of maximal points: for a
flat morphism `f : X → Y` of schemes of finite type over a field, `dim cl{ζ} = dim cl{f ζ} + n` for
every maximal point `ζ` of `X` if and only if every irreducible component of every fibre has
dimension `n`. -/
theorem forall_isMax_height_eq_add_iff_forall_fiber {k : Type u} [Field k]
    {X Y : Over (Spec (CommRingCat.of k))}
    (hX : LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom)
    (hY : LocallyOfFiniteType Y.hom ∧ QuasiCompact Y.hom) (f : X ⟶ Y) (hf : Flat f.left)
    (n : ℕ) :
    (∀ ζ : X.left, IsMax ζ → height ζ = height (f.left ζ) + n) ↔
      ∀ y : Y.left, ∀ Z ∈ irreducibleComponents (f.left.fiber y), topologicalKrullDim Z = n := by
  have : LocallyOfFiniteType X.hom := hX.1
  have : LocallyOfFiniteType Y.hom := hY.1
  have : QuasiCompact X.hom := hX.2
  have : LocallyOfFiniteType f.left := by
    have : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [Over.w f]; infer_instance
    exact locallyOfFiniteType_of_comp f.left Y.hom
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := {}
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  have : Flat f.left := hf
  have hFft : ∀ y : Y.left, FiniteType (f.left.fiberToSpecResidueField y) :=
    fun y => ⟨inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd _ _)),
      inferInstanceAs (QuasiCompact (Limits.pullback.snd _ _))⟩
  have hFnoeth : ∀ y : Y.left, IsNoetherian (f.left.fiber y) := fun y => by
    have : LocallyOfFiniteType (f.left.fiberToSpecResidueField y) := (hFft y).1
    have : IsLocallyNoetherian (f.left.fiber y) :=
      LocallyOfFiniteType.isLocallyNoetherian (f.left.fiberToSpecResidueField y)
    exact {}
  have hCX : ∀ g : X.left, CatenaryAt g := catenaryAt_of_finiteType X.hom hX
  have hCY : ∀ g : Y.left, CatenaryAt g := catenaryAt_of_finiteType Y.hom hY
  have hCF : ∀ (y : Y.left) (g : f.left.fiber y), CatenaryAt g := fun y =>
    catenaryAt_of_finiteType (K := Y.left.residueField y) _ (hFft y)
  have hfib : ∀ (y : Y.left) (x : f.left.fiber y), f.left (f.left.fiberι y x) = y := fun y x => by
    have : f.left.fiberι y x ∈ Set.range (f.left.fiberι y) := ⟨x, rfl⟩
    rwa [Scheme.Hom.range_fiberι] at this
  have h95 : ∀ (y : Y.left) (x : f.left.fiber y),
      coheight x + coheight y = coheight (f.left.fiberι y x) := by
    have key : ∀ (y₁ y₂ : Y.left), y₁ = y₂ → ∀ (x₁ : f.left.fiber y₁) (x₂ : f.left.fiber y₂),
        f.left.fiberι y₁ x₁ = f.left.fiberι y₂ x₂ →
          (coheight x₁ : WithBot ℕ∞) + coheight y₁ = coheight x₂ + coheight y₂ := by
      rintro y₁ _ rfl x₁ x₂ hx
      rw [(f.left.fiberι y₁).isEmbedding.injective hx]
    intro y x
    have h := ringKrullDim_stalk_fiber_add_ringKrullDim_stalk_of_flat hX hY f hf
      (f.left.fiberι y x)
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight,
      ringKrullDim_stalk_eq_coheight] at h
    have h' := (key _ _ (hfib y x) _ _ (Scheme.Hom.fiberι_asFiber _ _)).symm.trans h
    exact_mod_cast h'
  -- A point closed in its fibre has the height of its image.
  have hmin : ∀ (y : Y.left) (x : f.left.fiber y), IsClosed ({x} : Set (f.left.fiber y)) →
      height (f.left.fiberι y x) = height y := by
    intro y x hxc
    have hm : ∀ z, z ≤ f.left.fiberι y x → f.left z = f.left (f.left.fiberι y x) →
        z = f.left.fiberι y x := by
      intro z hz hfz
      rw [hfib] at hfz
      obtain ⟨z', rfl⟩ : z ∈ Set.range (f.left.fiberι y) := by
        rw [Scheme.Hom.range_fiberι]; exact hfz
      have hz' : x ⤳ z' := (f.left.fiberι y).isEmbedding.isInducing.specializes_iff.mp hz
      rw [hz'.mem_closed hxc rfl]
    have hD := height_eq_height_of_forall X.hom Y.hom hX hY f.left _ hm
    rwa [hfib] at hD
  have hgen : GeneralizingMap f.left := AlgebraicGeometry.Flat.generalizingMap f.left
  have hmaxf : ∀ ζ : X.left, IsMax ζ → IsMax (f.left ζ) := fun ζ h =>
    isMax_apply_of_generalizingMap f.left hgen h
  have hmono : ∀ {a b : X.left}, a ≤ b → f.left a ≤ f.left b := fun h => h.map f.left.continuous
  constructor
  · -- Hartshorne's clause implies the fibre form.
    intro h y Z hZ
    have := hFnoeth y
    obtain ⟨x₁, hx₁Z, hx₁c, hx₁up⟩ := exists_isClosed_forall_mem hZ
    obtain ⟨ξ, hξ⟩ := exists_closure_eq hZ
    have hmemZ : ∀ z, z ∈ Z ↔ z ≤ ξ := fun z => by
      rw [← hξ]; exact specializes_iff_mem_closure.symm
    have hx₁ : coheight x₁ = height ξ := by
      have := coheight_add_height_eq_of_forall (hCF y ξ) ((hmemZ x₁).mp hx₁Z)
        (fun z hz => (hmemZ z).mp (hx₁up z hz))
      rwa [Scheme.height_of_isClosed hx₁c, add_zero] at this
    have hD := hmin y x₁ hx₁c
    have hfx₁ := hfib y x₁
    set x₁' := f.left.fiberι y x₁ with hx₁'
    have hyfin : coheight y ≠ ⊤ := by
      have h0 := ringKrullDim_ne_top (R := Y.left.presheaf.stalk y)
      rw [ringKrullDim_stalk_eq_coheight] at h0
      exact fun ht => h0 (by rw [ht]; rfl)
    have hhy : height y ≠ ⊤ := by
      obtain ⟨N, hN, -⟩ := hCY y
      rw [hN]; exact ENat.natCast_ne_top _
    have hup : coheight x₁' ≤ coheight y + n := by
      refine coheight_le_of_forall_isMax hCX exists_le_isMax (hD ▸ hhy) fun g hg hgm => ?_
      have hfg : y ≤ f.left g := hfx₁ ▸ hmono hg
      rw [h g hgm, hD, ← add_assoc]
      gcongr
      exact height_le_height_add_coheight (hCY _) hfg
    have hlow : coheight y + n ≤ coheight x₁' := by
      by_cases htop : coheight x₁' = ⊤
      · rw [htop]; exact le_top
      obtain ⟨B, hB⟩ := ENat.ne_top_iff_exists.mp htop
      have key : ∀ q : LTSeries Y.left, q.head = y → q.length + n ≤ B := by
        intro q hq
        obtain ⟨η, hη, hηm⟩ := exists_le_isMax q.last
        have hyl : y ≤ q.last := hq ▸ q.monotone (Fin.zero_le _)
        have hyη : y ≤ η := hyl.trans hη
        have hlen := length_le_coheight_Iic q hq hη hyη
        obtain ⟨Nη, hNη, hcatη⟩ := hCY η
        have e1 := hcatη y hyη
        have hfx : f.left x₁' ≤ η := hfx₁.symm ▸ hyη
        obtain ⟨x'', hx'', hfx''⟩ := hgen hfx
        obtain ⟨ζ, hζ, hζm⟩ := exists_le_isMax x''
        have hle : η ≤ f.left ζ := hfx'' ▸ hmono hζ
        have hfζ : f.left ζ = η := eq_of_le_of_le (hηm hle) hle
        have e3 := height_le_height_add_coheight (hCX ζ) ((show x₁' ≤ x'' from hx'').trans hζ)
        rw [h ζ hζm, hfζ, hNη, hD, ← hB] at e3
        obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hhy
        have hcfin : coheight (⟨y, hyη⟩ : Set.Iic η) ≠ ⊤ := fun ht => by
          rw [ht, add_top] at e1
          exact ENat.top_ne_natCast _ e1
        obtain ⟨c, hc⟩ : ∃ c : ℕ, coheight (⟨y, hyη⟩ : Set.Iic η) = c :=
          (ENat.ne_top_iff_exists.mp hcfin).imp fun _ e => e.symm
        rw [← hm, hc] at e1
        rw [← hm] at e3
        rw [hc] at hlen
        have i1 : m + c = Nη := by exact_mod_cast e1
        have i2 : Nη + n ≤ m + B := by exact_mod_cast e3
        have i3 : q.length ≤ c := by exact_mod_cast hlen
        exact_mod_cast (show q.length + n ≤ B by omega)
      have hnB : n ≤ B := by simpa using key (RelSeries.singleton _ y) rfl
      have hcy : coheight y ≤ ((B - n : ℕ) : ℕ∞) := coheight_le fun q hq => by
        have := key q hq
        have : q.length + n ≤ B := by exact_mod_cast this
        exact_mod_cast (show q.length ≤ B - n by omega)
      rw [← hB]
      calc coheight y + n ≤ ((B - n : ℕ) : ℕ∞) + n := by gcongr
        _ = B := by norm_cast; omega
    have heq : coheight x₁' = coheight y + n := le_antisymm hup hlow
    have h1 := h95 y x₁
    rw [← hx₁', heq, add_comm (coheight y)] at h1
    rw [add_comm, add_comm (n : ℕ∞)] at h1
    have h2 : coheight x₁ = n := (WithTop.add_left_inj hyfin).mp h1
    rw [← hξ, topologicalKrullDim_closure_singleton, ← hx₁, h2]
    rfl
  · -- The fibre form implies Hartshorne's clause.
    intro h ζ hζ
    have hym := hmaxf ζ hζ
    have := hFnoeth (f.left ζ)
    have hxmax : IsMax (f.left.asFiber ζ) := by
      intro z hz
      have h1 : f.left.fiberι _ (f.left.asFiber ζ) ≤ f.left.fiberι _ z :=
        hz.map (f.left.fiberι _).continuous
      have h2 := (hζ ((Scheme.Hom.fiberι_asFiber f.left ζ).symm.trans_le h1)).trans_eq
        (Scheme.Hom.fiberι_asFiber f.left ζ).symm
      exact (f.left.fiberι _).isEmbedding.isInducing.specializes_iff.mp h2
    have hZ := closure_mem_irreducibleComponents_of_isMax hxmax
    have hdimZ := h _ _ hZ
    rw [topologicalKrullDim_closure_singleton] at hdimZ
    have hx : height (f.left.asFiber ζ) = n := by exact_mod_cast hdimZ
    obtain ⟨x₁, hx₁Z, hx₁c, hx₁up⟩ := exists_isClosed_forall_mem hZ
    have hmemZ : ∀ z, z ∈ closure {f.left.asFiber ζ} ↔ z ≤ f.left.asFiber ζ := fun z =>
      specializes_iff_mem_closure.symm
    have hx₁ : coheight x₁ = n := by
      have := coheight_add_height_eq_of_forall (hCF _ _) ((hmemZ x₁).mp hx₁Z)
        (fun z hz => (hmemZ z).mp (hx₁up z hz))
      rwa [Scheme.height_of_isClosed hx₁c, add_zero, hx] at this
    have hD := hmin _ x₁ hx₁c
    have h1 := h95 _ x₁
    rw [hx₁, coheight_eq_zero.mpr hym, add_zero] at h1
    have hle : f.left.fiberι _ x₁ ≤ ζ := by
      exact (show f.left.fiberι (f.left ζ) x₁ ≤ f.left.fiberι (f.left ζ) (f.left.asFiber ζ) from
        ((hmemZ x₁).mp hx₁Z).map (f.left.fiberι (f.left ζ)).continuous).trans_eq
          (Scheme.Hom.fiberι_asFiber f.left ζ)
    have hup : ∀ z, f.left.fiberι _ x₁ ≤ z → z ≤ ζ := by
      intro z hz
      have hfz : f.left ζ ≤ f.left z := hfib _ x₁ ▸ hmono hz
      have hfz' : f.left z = f.left ζ := eq_of_le_of_le (hym hfz) hfz
      obtain ⟨z', rfl⟩ : z ∈ Set.range (f.left.fiberι (f.left ζ)) := by
        rw [Scheme.Hom.range_fiberι]; exact hfz'
      have hz' : x₁ ≤ z' := (f.left.fiberι _).isEmbedding.isInducing.specializes_iff.mp hz
      exact (show f.left.fiberι (f.left ζ) z' ≤ f.left.fiberι (f.left ζ) (f.left.asFiber ζ) from
        ((hmemZ z').mp (hx₁up z' hz')).map (f.left.fiberι (f.left ζ)).continuous).trans_eq
          (Scheme.Hom.fiberι_asFiber f.left ζ)
    have := coheight_add_height_eq_of_forall (hCX ζ) hle hup
    rw [← h1, hD] at this
    rw [← this, add_comm]

/-- **Hartshorne's dimension clause and the fibre form.** Let `f : X → Y` be a flat morphism of
schemes of finite type over a field `k` and `n` a natural number. The condition of Hartshorne's
definition of smoothness (III.10, p. 268): for irreducible components `X' ⊆ X` and `Y' ⊆ Y` with
`f(X') ⊆ Y'`, `dim X' = dim Y' + n`, holds if and only if every irreducible component of every
scheme-theoretic fibre `X_y` has dimension `n`. This supplements Corollary III.9.6, which assumes
`Y` irreducible; the proof uses Proposition III.9.5 at a closed point of a fibre lying on a single
component of the fibre, and going-down for flat morphisms. -/
theorem forall_irreducibleComponents_dim_eq_add_iff_forall_fiber {k : Type u} [Field k]
    {X Y : Over (Spec (CommRingCat.of k))}
    (hX : LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom)
    (hY : LocallyOfFiniteType Y.hom ∧ QuasiCompact Y.hom) (f : X ⟶ Y) (hf : Flat f.left)
    (n : ℕ) :
    (∀ X' ∈ irreducibleComponents X.left, ∀ Y' ∈ irreducibleComponents Y.left,
        f.left '' X' ⊆ Y' → topologicalKrullDim X' = topologicalKrullDim Y' + n) ↔
      ∀ y : Y.left, ∀ Z ∈ irreducibleComponents (f.left.fiber y), topologicalKrullDim Z = n := by
  have : Flat f.left := hf
  have hgen : GeneralizingMap f.left := AlgebraicGeometry.Flat.generalizingMap f.left
  have hmaxf : ∀ ζ : X.left, IsMax ζ → IsMax (f.left ζ) := fun ζ h =>
    isMax_apply_of_generalizingMap f.left hgen h
  -- Hartshorne's clause in terms of maximal points.
  have hiff : (∀ X' ∈ irreducibleComponents X.left, ∀ Y' ∈ irreducibleComponents Y.left,
        f.left '' X' ⊆ Y' → topologicalKrullDim X' = topologicalKrullDim Y' + n) ↔
      ∀ ζ : X.left, IsMax ζ → height ζ = height (f.left ζ) + n := by
    constructor
    · intro h ζ hζ
      have hsub : f.left '' closure {ζ} ⊆ closure {f.left ζ} := by
        rw [← Set.image_singleton]
        exact image_closure_subset_closure_image f.left.continuous
      have h1 := h _ (closure_mem_irreducibleComponents_of_isMax hζ) _
        (closure_mem_irreducibleComponents_of_isMax (hmaxf ζ hζ)) hsub
      rw [topologicalKrullDim_closure_singleton, topologicalKrullDim_closure_singleton] at h1
      exact_mod_cast h1
    · intro h X' hX' Y' hY' hsub
      obtain ⟨ζ, rfl⟩ := exists_closure_eq hX'
      obtain ⟨η, rfl⟩ := exists_closure_eq hY'
      have hζ := isMax_of_closure_mem_irreducibleComponents hX'
      have hle : f.left ζ ≤ η :=
        specializes_iff_mem_closure.mpr (hsub ⟨ζ, subset_closure rfl, rfl⟩)
      rw [topologicalKrullDim_closure_singleton, topologicalKrullDim_closure_singleton, h ζ hζ,
        eq_of_le_of_le hle (hmaxf ζ hζ hle)]
      norm_cast
  rw [hiff]
  exact forall_isMax_height_eq_add_iff_forall_fiber hX hY f hf n

/-- **Hartshorne III.10, definition of smoothness (p. 268).** Let `f : X → Y` be a morphism of
schemes of finite type over a field `k`. Then `f` is smooth of relative dimension `n` (Mathlib's
`SmoothOfRelativeDimension`) if and only if
1. `f` is flat;
2. if `X' ⊆ X` and `Y' ⊆ Y` are irreducible components with `f(X') ⊆ Y'`, then
   `dim X' = dim Y' + n`; and
3. `dim_{k(x)} ((Ω_{X/Y})_x ⊗ k(x)) = n` for every `x ∈ X`.

Under flatness, clause 2 is equivalent to every irreducible component of every fibre having
dimension `n` (`forall_irreducibleComponents_dim_eq_add_iff_forall_fiber`), which is the form of
`smoothOfRelativeDimension_iff_flat_and_fiber_dim_and_finrank`. -/
theorem smoothOfRelativeDimension_iff_flat_and_component_dim_and_finrank {k : Type u} [Field k]
    {X Y : Over (Spec (CommRingCat.of k))}
    (hX : LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom)
    (hY : LocallyOfFiniteType Y.hom ∧ QuasiCompact Y.hom) (f : X ⟶ Y) (n : ℕ) :
    SmoothOfRelativeDimension n f.left ↔
      Flat f.left ∧
        (∀ X' ∈ irreducibleComponents X.left, ∀ Y' ∈ irreducibleComponents Y.left,
          f.left '' X' ⊆ Y' → topologicalKrullDim X' = topologicalKrullDim Y' + n) ∧
        ∀ x : X.left, finrank (ResidueField (X.left.presheaf.stalk x))
          (ResidueField (X.left.presheaf.stalk x) ⊗[X.left.presheaf.stalk x]
            (Scheme.relativeDifferentials f.left).presheaf.stalk x) = n := by
  rw [smoothOfRelativeDimension_iff_flat_and_fiber_dim_and_finrank hX hY f n]
  constructor
  · rintro ⟨hf, hd, hΩ⟩
    exact ⟨hf, (forall_irreducibleComponents_dim_eq_add_iff_forall_fiber hX hY f hf n).2 hd, hΩ⟩
  · rintro ⟨hf, hd, hΩ⟩
    exact ⟨hf, (forall_irreducibleComponents_dim_eq_add_iff_forall_fiber hX hY f hf n).1 hd, hΩ⟩

end ComponentDimension

end Hartshorne

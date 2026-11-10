/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.SmoothMorphisms.SmoothOverAlgClosedRegular
import Hartshorne.Cohomology.SmoothMorphisms.SmoothnessCriterionReduction
import Hartshorne.Scheme.Differentials.RelativeDifferentialsBaseChange
import Hartshorne.Scheme.ModulePullbackStalk
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Smoothness and geometrically regular fibres

Hartshorne, *Algebraic Geometry*, III.10, Theorem 10.2 (pp. 269-270); Stacks Project, Lemma
29.35.3 (tag 01V8).

Let `f : X → Y` be a morphism of schemes of finite type over a field `k`. Then `f` is smooth of
relative dimension `n` if and only if `f` is flat and, for every `y ∈ Y`, the fibre `X_y` base
changed to an algebraic closure `k(y)‾` of `k(y)` is regular with all irreducible components of
dimension `n` (`smoothOfRelativeDimension_iff_flat_and_geometric_fiber`).

## Proof

For a scheme `Z` of finite type over a field `K` and an algebraically closed extension `L`
(`smoothOfRelativeDimension_iff_baseChange_isRegularAt`), smoothness of relative dimension `n` of
`Z_L → Spec L` is regularity together with equidimensionality of `Z_L`
(`smoothOfRelativeDimension_iff_forall_isRegularAt`). Smoothness of relative dimension `n` is
stable under base change. Conversely, smoothness descends along the faithfully flat, surjective
and quasi-compact morphism `Spec L → Spec K` (Mathlib's fpqc descent of smoothness), and the
relative dimension is read off from the fibres of the differentials: for `Z' = Z ×_Y Y'`,
`Ω_{Z'/Y'} ≅ g'^* Ω_{Z/Y}` (Hartshorne II.8.10), and the fibre of a pullback `h^*F` at `z'` is
`k(z') ⊗_{k(h z')} (F_{h z'} ⊗ k(h z'))`, of the same dimension as the fibre of `F` at `h(z')`
(`finrank_fibre_relativeDifferentials_pullback_snd`). Since `Z_L → Z` is surjective, every fibre
of `Ω_{Z/K}` then has dimension `n`.

For `f`, the forward direction passes to the fibres `X_y → Spec k(y)` by base change. For the
converse, every `X_y → Spec k(y)` is smooth of relative dimension `n` by the above; `f` is flat with
smooth fibres, so smooth, and each fibre of `Ω_{X/Y}` has the dimension of a fibre of
`Ω_{X_y/k(y)}`, namely `n` (`Scheme.smoothOfRelativeDimension_of_flat_of_smooth_fiber`).
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct IsLocalRing Module

namespace Hartshorne

universe u

/-- Fibres of isomorphic module sheaves have the same dimension. -/
theorem finrank_fibre_eq_of_iso {X : Scheme.{u}} {F G : X.Modules} (e : F ≅ G) (x : X) :
    finrank (ResidueField (X.presheaf.stalk x))
        (ResidueField (X.presheaf.stalk x) ⊗[X.presheaf.stalk x] F.presheaf.stalk x) =
      finrank (ResidueField (X.presheaf.stalk x))
        (ResidueField (X.presheaf.stalk x) ⊗[X.presheaf.stalk x] G.presheaf.stalk x) := by
  let e₀ : F.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] G.presheaf.stalk x :=
    ((Ringed.moduleStalkFunctor (R := X.sheaf) x).mapIso e).toLinearEquiv
  exact (e₀.baseChange _ _ _ _).finrank_eq

/-- The fibre of the pullback `h^*F` at `x'` has the dimension of the fibre of `F` at `h(x')`. -/
theorem finrank_fibre_modulesPullback {X' X : Scheme.{u}} (h : X' ⟶ X) (F : X.Modules)
    (x' : X') :
    finrank (ResidueField (X'.presheaf.stalk x'))
        (ResidueField (X'.presheaf.stalk x') ⊗[X'.presheaf.stalk x']
          ((Scheme.Modules.pullback h).obj F).presheaf.stalk x') =
      finrank (ResidueField (X.presheaf.stalk (h x')))
        (ResidueField (X.presheaf.stalk (h x')) ⊗[X.presheaf.stalk (h x')]
          F.presheaf.stalk (h x')) := by
  let A := X.presheaf.stalk (h x')
  let C := X'.presheaf.stalk x'
  let kA := ResidueField A
  let kC := ResidueField C
  let M := F.presheaf.stalk (h x')
  let N := ((Scheme.Modules.pullback h).obj F).presheaf.stalk x'
  let : Algebra A C := (h.stalkMap x').hom.toAlgebra
  let : Algebra kA kC := (ResidueField.map (h.stalkMap x').hom).toAlgebra
  have : IsScalarTower A C kC := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A kA kC := IsScalarTower.of_algebraMap_eq fun a =>
    (ResidueField.map_residue (h.stalkMap x').hom a).symm
  let : Module (ringSheafStalk X'.sheaf x') ((ModuleCat.extendScalars (h.stalkMap x').hom).obj
      ((Ringed.moduleStalkFunctor (R := X.sheaf) (h x')).obj F)) := ModuleCat.isModule _
  let e₀ : ↑((Ringed.moduleStalkFunctor (R := X'.sheaf) x').obj
        ((Scheme.Modules.pullback h).obj F)) ≃ₗ[ringSheafStalk X'.sheaf x']
      ↑((ModuleCat.extendScalars (h.stalkMap x').hom).obj
        ((Ringed.moduleStalkFunctor (R := X.sheaf) (h x')).obj F)) :=
    pullbackStalkLinearEquiv h x' F
  let e₁ : N ≃ₗ[C] C ⊗[A] M :=
    { toFun := fun n => e₀ n
      invFun := fun t => e₀.symm t
      map_add' := fun m m' => e₀.map_add m m'
      map_smul' := fun c m => e₀.map_smul c m
      left_inv := e₀.left_inv
      right_inv := e₀.right_inv }
  let e₂ : kC ⊗[C] N ≃ₗ[kC] kC ⊗[A] M :=
    (AlgebraTensorModule.congr (LinearEquiv.refl kC kC) e₁).trans
      (AlgebraTensorModule.cancelBaseChange A C kC kC M)
  let e₃ : kC ⊗[kA] (kA ⊗[A] M) ≃ₗ[kC] kC ⊗[A] M :=
    AlgebraTensorModule.cancelBaseChange A kA kC kC M
  rw [e₂.finrank_eq, ← e₃.finrank_eq, Module.finrank_baseChange]

/-- For `X' = X ×_Y Y'`, the fibre of `Ω_{X'/Y'}` at `x'` has the dimension of the fibre of
`Ω_{X/Y}` at the image of `x'` in `X`. -/
theorem finrank_fibre_relativeDifferentials_pullback_snd {X Y Y' : Scheme.{u}} (f : X ⟶ Y)
    (g : Y' ⟶ Y) (x' : ↥(pullback f g)) :
    finrank (ResidueField ((pullback f g).presheaf.stalk x'))
        (ResidueField ((pullback f g).presheaf.stalk x') ⊗[(pullback f g).presheaf.stalk x']
          (Scheme.relativeDifferentials (pullback.snd f g)).presheaf.stalk x') =
      finrank (ResidueField (X.presheaf.stalk (pullback.fst f g x')))
        (ResidueField (X.presheaf.stalk (pullback.fst f g x')) ⊗[
          X.presheaf.stalk (pullback.fst f g x')]
          (Scheme.relativeDifferentials f).presheaf.stalk (pullback.fst f g x')) :=
  (finrank_fibre_eq_of_iso (Scheme.relativeDifferentialsBaseChangeIso f g) x').trans
    (finrank_fibre_modulesPullback _ _ x')

/-- Let `Z` be a scheme of finite type over a field `K` and `L` an algebraically closed extension
of `K`. Then `Z ⟶ Spec K` is smooth of relative dimension `n` if and only if `Z_L = Z ×_K L` is
regular with all irreducible components of dimension `n`. -/
theorem smoothOfRelativeDimension_iff_baseChange_isRegularAt {K L : Type u} [Field K] [Field L]
    [IsAlgClosed L] [Algebra K L] {Z : Scheme.{u}} (s : Z ⟶ Spec (.of K)) (hs : FiniteType s)
    (n : ℕ) :
    SmoothOfRelativeDimension n s ↔
      (∀ z, (pullback s (Spec.map (CommRingCat.ofHom (algebraMap K L)))).IsRegularAt z) ∧
        ∀ C ∈ irreducibleComponents
          ↥(pullback s (Spec.map (CommRingCat.ofHom (algebraMap K L))) : Scheme.{u}),
          topologicalKrullDim C = n := by
  set g := Spec.map (CommRingCat.ofHom (algebraMap K L))
  have : LocallyOfFiniteType s := hs.1
  have : QuasiCompact s := hs.2
  rw [← smoothOfRelativeDimension_iff_forall_isRegularAt (pullback.snd s g)
    ⟨inferInstance, inferInstance⟩ n]
  refine ⟨fun h => (smoothOfRelativeDimension_isStableUnderBaseChange n).of_isPullback
    (IsPullback.of_hasPullback s g) h, fun h => ?_⟩
  have : Surjective g := ⟨fun _ => ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  have : Flat g := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat), CommRingCat.hom_ofHom,
      RingHom.flat_algebraMap_iff]
    infer_instance
  have : Smooth (pullback.snd s g) := SmoothOfRelativeDimension.smooth n _
  have : Smooth s := MorphismProperty.of_pullback_snd_of_descendsAlong (P := @Smooth)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) ⟨⟨‹_›, ‹_›⟩, inferInstance⟩ ‹_›
  refine Scheme.smoothOfRelativeDimension_of_smooth_of_finrank_fibre s n fun x => ?_
  obtain ⟨w, rfl⟩ := (pullback.fst s g).surjective x
  rw [← finrank_fibre_relativeDifferentials_pullback_snd]
  exact ((Scheme.smoothOfRelativeDimension_iff_smooth_and_finrank_fibre _ n).1 h).2 w

/-- **Smoothness and geometrically regular fibres** (Hartshorne III, Theorem 10.2). Let
`f : X → Y` be a morphism of schemes of finite type over a field `k`. Then `f` is smooth of
relative dimension `n` if and only if `f` is flat and, for every `y ∈ Y`, the fibre `X_y` base
changed to an algebraic closure of `k(y)` is regular with every irreducible component of
dimension `n`. -/
theorem smoothOfRelativeDimension_iff_flat_and_geometric_fiber {k : Type u} [Field k]
    {X Y : Over (Spec (CommRingCat.of k))}
    (hX : LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom)
    (hY : LocallyOfFiniteType Y.hom ∧ QuasiCompact Y.hom) (f : X ⟶ Y) (n : ℕ) :
    SmoothOfRelativeDimension n f.left ↔
      Flat f.left ∧ ∀ y : Y.left,
        (∀ z, (pullback (f.left.fiberToSpecResidueField y)
          (Spec.map (CommRingCat.ofHom (algebraMap (Y.left.residueField y)
            (AlgebraicClosure (Y.left.residueField y)))))).IsRegularAt z) ∧
        ∀ C ∈ irreducibleComponents ↥(pullback (f.left.fiberToSpecResidueField y)
          (Spec.map (CommRingCat.ofHom
            (algebraMap (Y.left.residueField y) (AlgebraicClosure (Y.left.residueField y))))) :
              Scheme.{u}),
          topologicalKrullDim C = n := by
  have : LocallyOfFiniteType X.hom := hX.1
  have : LocallyOfFiniteType Y.hom := hY.1
  have : QuasiCompact X.hom := hX.2
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : IsNoetherian X.left := {}
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [Over.w f]; infer_instance
  have : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left Y.hom
  have : QuasiCompact f.left := ⟨fun _ _ _ => TopologicalSpace.NoetherianSpace.isCompact _⟩
  have hft : ∀ y : Y.left, FiniteType (f.left.fiberToSpecResidueField y) := fun y =>
    ⟨inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _)),
      inferInstanceAs (QuasiCompact (pullback.snd _ _))⟩
  have hiff := fun y : Y.left => smoothOfRelativeDimension_iff_baseChange_isRegularAt
    (K := Y.left.residueField y) (L := AlgebraicClosure (Y.left.residueField y))
    (f.left.fiberToSpecResidueField y) (hft y) n
  refine ⟨fun h => ?_, fun ⟨hflat, h⟩ => ?_⟩
  · have : Smooth f.left := SmoothOfRelativeDimension.smooth n _
    exact ⟨inferInstance, fun y =>
      (hiff y).1 (Scheme.smoothOfRelativeDimension_fiberToSpecResidueField f.left n y)⟩
  · have hfib := fun y => (hiff y).2 (h y)
    have : LocallyOfFinitePresentation f.left :=
      LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 inferInstance
    refine Scheme.smoothOfRelativeDimension_of_flat_of_smooth_fiber f.left n
      (fun y => SmoothOfRelativeDimension.smooth n _) fun x => ?_
    rw [← f.left.fiberι_asFiber x]
    exact (finrank_fibre_relativeDifferentials_pullback_snd _ _ _).symm.trans
      (((Scheme.smoothOfRelativeDimension_iff_smooth_and_finrank_fibre _ n).1
        (hfib (f.left x))).2 _)

end Hartshorne

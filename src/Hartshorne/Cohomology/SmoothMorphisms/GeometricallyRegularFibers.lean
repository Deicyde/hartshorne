/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.FlatFamilies.FlatFibreLocalDimension
import Hartshorne.Cohomology.Flatness.CoherentSelfFlatLocallyFree
import Hartshorne.Cohomology.SmoothMorphisms.SmoothOverAlgClosedRegular
import Hartshorne.Cohomology.SmoothMorphisms.SmoothnessCriterionReduction
import Hartshorne.Scheme.CoherentFibreRank
import Hartshorne.Scheme.Differentials.RelativeDifferentialsBaseChange
import Hartshorne.Scheme.ModulePullbackStalk
import Hartshorne.Scheme.SmoothRelativeDimensionCalculus
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Smoothness and geometrically regular fibres

Hartshorne, *Algebraic Geometry*, III.10, Theorem 10.2 (pp. 269-270); Stacks Project, Lemma
29.35.3 (tag 01V8).

Let `f : X → Y` be a morphism of schemes of finite type over a field `k`. Then `f` is smooth of
relative dimension `n` if and only if `f` is flat and, for every `y ∈ Y`, the fibre `X_y` base
changed to an algebraic closure `k(y)‾` of `k(y)` is regular with all irreducible components of
dimension `n` (`smoothOfRelativeDimension_iff_flat_and_geometric_fiber`).

## Proof

This follows the route of the proof on p. 270. Let `Z` be a scheme of finite type over a field `K`
and `L` an algebraically closed extension of `K`
(`smoothOfRelativeDimension_iff_baseChange_isRegularAt`).

* If `Z → Spec K` is smooth of relative dimension `n`, so is its base change `Z_L → Spec L`
  (Proposition 10.1(b), `smoothOfRelativeDimension_baseChange`), and then `Z_L` is regular with
  every irreducible component of dimension `n` (Example 10.0.3,
  `smoothOfRelativeDimension_iff_forall_isRegularAt`).
* Conversely, if `Z_L` is regular and equidimensional of dimension `n`, then `Z_L → Spec L` is
  smooth of relative dimension `n` (Example 10.0.3), so `Ω_{Z_L/L}` is locally free of rank `n`
  (`Scheme.relativeDifferentials_isLocallyFreeOfRank_of_smoothOfRelativeDimension`). Since
  `Ω_{Z_L/L} ≅ g'^* Ω_{Z/K}` for the projection `g' : Z_L → Z` (II.8.10), and `g'` is flat and
  surjective, `Ω_{Z/K}` is locally free of rank `n` by faithfully flat descent
  (`relativeDifferentials_isLocallyFreeOfRank_of_pullback_snd`): at `z' ↦ z` the local
  homomorphism `𝒪_{Z,z} → 𝒪_{Z_L,z'}` is flat, `Ω_{Z/K,z}` is finite, and
  `𝒪_{Z_L,z'} ⊗ Ω_{Z/K,z}` is free, so `Ω_{Z/K,z}` is flat, hence free
  (`free_of_flat_tensorProduct_of_isLocalHom`). This is the step Hartshorne cites from Matsumura
  (4.E).
* The irreducible components of `Z` have dimension `n`, because those of `Z_L` do
  (`topologicalKrullDim_irreducibleComponents_of_baseChange`). At a closed point `z` of `Z` on a
  single component `C`, `dim C = dim 𝒪_{Z,z}`; the fibre of `Z_L → Z` over `z` is discrete, so
  for a closed point `z'` of `Z_L` over `z` the flat local homomorphism `𝒪_{Z,z} → 𝒪_{Z_L,z'}` has
  zero-dimensional closed fibre and `dim 𝒪_{Z,z} = dim 𝒪_{Z_L,z'} = n`.
* So `Z → Spec K` satisfies Hartshorne's definition of smoothness of relative dimension `n`
  (flat, components of dimension `n`, and `dim_{k(z)} Ω_{Z/K} ⊗ k(z) = n` for every `z`), and
  Hartshorne's smoothness criterion (`smoothOfRelativeDimension_iff_flat_and_fiber_dim_and_finrank`)
  gives smoothness of relative dimension `n`.

For `f` (`smoothOfRelativeDimension_iff_flat_and_geometric_fiber`), the forward direction passes
to the fibres `X_y → Spec k(y)` by base change (Proposition 10.1(b)). For the converse, each fibre
`X_y` has `Ω_{X_y/k(y)}` locally free of rank `n` and all components of dimension `n`, by the
above; since `Ω_{X_y/k(y)} ≅ ι^* Ω_{X/Y}` (II.8.10), and the fibre of a pullback `h^*F` at `x'` has
the dimension of the fibre of `F` at `h(x')` (`finrank_fibre_relativeDifferentials_pullback_snd`),
every fibre of `Ω_{X/Y}` has dimension `n`. As `f` is flat, Hartshorne's smoothness criterion
applies.
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

/-- **Faithfully flat descent of freeness.** Let `A → B` be a flat local homomorphism of local
rings and `M` a finite `A`-module. If `B ⊗_A M` is a flat (for instance free) `B`-module, then `M`
is a free `A`-module. This is the commutative-algebra fact behind the descent step in the proof of
Hartshorne III, Theorem 10.2 (p. 270), which cites Matsumura, *Commutative Algebra*, (4.E). -/
theorem free_of_flat_tensorProduct_of_isLocalHom {A B M : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    [Module.Flat A B] [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.Flat B (B ⊗[A] M)] : Module.Free A M := by
  have : Module.FaithfullyFlat A B := .of_flat_of_isLocalHom
  have : Module.Flat A M := .of_flat_tensorProduct A M B
  exact Module.free_of_flat_of_isLocalRing

/-- Let `h : X' → X` be flat and `F` a coherent `𝒪_X`-module. If the stalk of `h^*F` at `x'` is
free, then the stalk of `F` at `h(x')` is free. -/
theorem free_stalk_of_free_stalk_modulesPullback {X' X : Scheme.{u}} (h : X' ⟶ X) [Flat h]
    (F : X.Modules) (hF : IsCoherent F) (x' : X')
    (hfree : Module.Free (X'.presheaf.stalk x')
      (((Scheme.Modules.pullback h).obj F).presheaf.stalk x')) :
    Module.Free (X.presheaf.stalk (h x')) (F.presheaf.stalk (h x')) := by
  let A := X.presheaf.stalk (h x')
  let C := X'.presheaf.stalk x'
  let M := F.presheaf.stalk (h x')
  let N := ((Scheme.Modules.pullback h).obj F).presheaf.stalk x'
  let : Algebra A C := (h.stalkMap x').hom.toAlgebra
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
  have : Module.Free C (C ⊗[A] M) := .of_equiv e₁
  have : Module.Flat A C := (Flat.iff_flat_stalkMap h).mp inferInstance x'
  have : Module.Finite A M := finite_stalk_of_isCoherent F hF (h x')
  have : IsLocalHom (algebraMap A C) := inferInstanceAs (IsLocalHom (h.stalkMap x').hom)
  exact free_of_flat_tensorProduct_of_isLocalHom (B := C)

/-- **Faithfully flat descent of local freeness of differentials.** Let `f : X → Y` be locally of
finite type with `X` locally Noetherian, and `g : Y' → Y` flat and surjective. If
`Ω_{X'/Y'}` is locally free of rank `n` on `X' = X ×_Y Y'`, then `Ω_{X/Y}` is locally free of
rank `n`. (In the proof of Hartshorne III, Theorem 10.2, this is applied to the base change of a
fibre to an algebraic closure of the residue field.) -/
theorem relativeDifferentials_isLocallyFreeOfRank_of_pullback_snd {X Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) [Flat g] [Surjective g] [LocallyOfFiniteType f]
    [IsLocallyNoetherian X] (n : ℕ)
    (h : (Scheme.relativeDifferentials (pullback.snd f g)).IsLocallyFreeOfRank n) :
    (Scheme.relativeDifferentials f).IsLocallyFreeOfRank n := by
  have hcoh := Scheme.relativeDifferentials_isCoherent_of_locallyOfFiniteType f
  have hlf' := ((Scheme.relativeDifferentials (pullback.snd f g)).isLocallyFreeOfRank_iff n).1 h
  have hfree : ∀ x : X, Module.Free (X.presheaf.stalk x)
      ((Scheme.relativeDifferentials f).presheaf.stalk x) := fun x => by
    obtain ⟨x', rfl⟩ := (pullback.fst f g).surjective x
    have h₁ := free_stalk_of_isLocallyFree _ hlf'.1 x'
    let e₀ : (Scheme.relativeDifferentials (pullback.snd f g)).presheaf.stalk x' ≃ₗ[
        (pullback f g).presheaf.stalk x'] ((Scheme.Modules.pullback (pullback.fst f g)).obj
          (Scheme.relativeDifferentials f)).presheaf.stalk x' :=
      ((Ringed.moduleStalkFunctor (R := (pullback f g).sheaf) x').mapIso
        (Scheme.relativeDifferentialsBaseChangeIso f g)).toLinearEquiv
    have : Module.Free ((pullback f g).presheaf.stalk x')
        (((Scheme.Modules.pullback (pullback.fst f g)).obj
          (Scheme.relativeDifferentials f)).presheaf.stalk x') := .of_equiv e₀
    exact free_stalk_of_free_stalk_modulesPullback _ _ hcoh x' this
  have hlf := (isLocallyFree_iff_forall_free_stalk_of_isLocallyNoetherian _ hcoh).2 hfree
  refine ((Scheme.relativeDifferentials f).isLocallyFreeOfRank_iff n).2 ⟨hlf, fun x => ?_⟩
  obtain ⟨U, hxU, I, ⟨α⟩⟩ := hlf x
  rw [Scheme.Modules.rankAt_eq _ α hxU, ← rank_fibre_of_restrict_iso_free _ α hxU]
  obtain ⟨x', rfl⟩ := (pullback.fst f g).surjective x
  have hn := (finrank_fibre_relativeDifferentials_pullback_snd f g x').symm.trans
    (finrank_fibre_of_isLocallyFreeOfRank _ n h x')
  have : Module.Finite (X.presheaf.stalk (pullback.fst f g x'))
      ((Scheme.relativeDifferentials f).presheaf.stalk (pullback.fst f g x')) :=
    finite_stalk_of_isCoherent _ hcoh _
  rw [← Module.finrank_eq_rank, hn]

open FlatEquidimensional Order in
/-- Let `Z` be a scheme of finite type over a field `K` and `L` an extension field of `K`. If
every irreducible component of `Z_L = Z ×_K L` has dimension `n`, then every irreducible component
of `Z` has dimension `n`. -/
theorem topologicalKrullDim_irreducibleComponents_of_baseChange {K L : Type u} [Field K]
    [Field L] [Algebra K L] {Z : Scheme.{u}} (s : Z ⟶ Spec (.of K)) (hs : FiniteType s) {n : ℕ}
    (hC : ∀ C ∈ irreducibleComponents
      ↥(pullback s (Spec.map (CommRingCat.ofHom (algebraMap K L))) : Scheme.{u}),
      topologicalKrullDim C = n) :
    ∀ C ∈ irreducibleComponents Z, topologicalKrullDim C = n := by
  set g := Spec.map (CommRingCat.ofHom (algebraMap K L))
  set g' := pullback.fst s g
  have : LocallyOfFiniteType s := hs.1
  have : QuasiCompact s := hs.2
  have hs' : FiniteType (pullback.snd s g) := ⟨inferInstance, inferInstance⟩
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian s
  have : IsLocallyNoetherian (pullback s g) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd s g)
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace s
  have : CompactSpace ↥(pullback s g : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd s g)
  have : IsNoetherian Z := {}
  have : JacobsonSpace Z := LocallyOfFiniteType.jacobsonSpace s
  have : Surjective g := ⟨fun _ => ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  have : Flat g := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat), CommRingCat.hom_ofHom,
      RingHom.flat_algebraMap_iff]
    infer_instance
  intro C hC'
  obtain ⟨z, hzC, hzc, hzup⟩ := exists_isClosed_forall_mem hC'
  obtain ⟨ζ, hζ⟩ := exists_closure_eq hC'
  have hmemC : ∀ w, w ∈ C ↔ w ≤ ζ := fun w => by
    rw [← hζ]; exact specializes_iff_mem_closure.symm
  have hz1 : coheight z = height ζ := by
    have := coheight_add_height_eq_of_forall (catenaryAt_of_finiteType s hs ζ)
      ((hmemC z).mp hzC) (fun w hw => (hmemC w).mp (hzup w hw))
    rwa [Scheme.height_of_isClosed hzc, add_zero] at this
  rw [← hζ, topologicalKrullDim_closure_singleton, ← hz1, ← ringKrullDim_stalk_eq_coheight]
  -- A point `z'` of `Z_L` over `z`, closed in `Z_L`.
  obtain ⟨z', hz'z, hz'c⟩ := (hzc.preimage g'.continuous).exists_closed_singleton
    (g'.surjective z)
  replace hz'z : g' z' = z := hz'z
  subst hz'z
  -- The fibre of `Z_L → Z` over the closed point `z` is discrete.
  have : IsClosedImmersion (Z.fromSpecResidueField (g' z')) :=
    isClosed_singleton_iff_isClosedImmersion.mp hzc
  have : LocallyQuasiFinite (Z.fromSpecResidueField (g' z') ≫ s) :=
    .of_injective fun _ _ _ => Subsingleton.elim _ _
  let p : g'.fiber (g' z') ⟶ Spec (.of L) := (pullbackSymmetry _ _).hom ≫
    (pullbackRightPullbackFstIso s g (Z.fromSpecResidueField (g' z'))).hom ≫ pullback.snd _ _
  have : LocallyQuasiFinite p := by
    have h₁ : LocallyQuasiFinite (pullback.snd (Z.fromSpecResidueField (g' z') ≫ s) g) :=
      inferInstance
    have h₂ : LocallyQuasiFinite (pullbackRightPullbackFstIso s g
      (Z.fromSpecResidueField (g' z'))).hom := inferInstance
    have h₃ : LocallyQuasiFinite (pullbackSymmetry g' (Z.fromSpecResidueField (g' z'))).hom :=
      inferInstance
    exact MorphismProperty.comp_mem @LocallyQuasiFinite _ _ h₃
      (MorphismProperty.comp_mem @LocallyQuasiFinite _ _ h₂ h₁)
  have hdisc : DiscreteTopology (g'.fiber (g' z')) := by
    have h := p.isDiscrete_preimage_singleton (Nonempty.some inferInstance)
    have hu : p ⁻¹' {Nonempty.some inferInstance} = Set.univ :=
      Set.eq_univ_of_forall fun _ => Subsingleton.elim _ _
    rw [hu] at h
    exact isDiscrete_univ_iff.mp h
  have h4 : ringKrullDim ((g'.fiber (g' z')).presheaf.stalk (g'.asFiber z')) = 0 := by
    rw [ringKrullDim_stalk_eq_coheight]
    norm_cast
    rw [coheight_eq_zero]
    intro w hw
    exact le_of_eq (Specializes.eq (X := g'.fiber (g' z')) hw)
  have h3 := ringKrullDim_stalk_eq_ringKrullDim_quotient_of_range_eq
    (g'.fiberι (g' z')) g' (g'.asFiber z')
    (by rw [Scheme.Hom.fiberι_asFiber, Scheme.Hom.range_fiberι])
  rw [Scheme.Hom.fiberι_asFiber] at h3
  have h2 := ringKrullDim_eq_add_ringKrullDim_quotient_of_flat (g'.stalkMap z').hom
    ((Flat.iff_flat_stalkMap g').mp inferInstance z')
  have h1 := DifferentialsNonsingular.ringKrullDim_stalk_of_isClosed_of_equidim _ hs' hC z' hz'c
  rw [h2, ← h3, h4, add_zero] at h1
  exact h1

/-- Let `Z` be a scheme of finite type over a field `K` and `L` an algebraically closed extension
of `K`. If `Z_L = Z ×_K L` is regular with every irreducible component of dimension `n`, then
`Ω_{Z/K}` is locally free of rank `n` and every irreducible component of `Z` has dimension `n`. -/
theorem relativeDifferentials_isLocallyFreeOfRank_of_baseChange_isRegularAt {K L : Type u}
    [Field K] [Field L] [IsAlgClosed L] [Algebra K L] {Z : Scheme.{u}} (s : Z ⟶ Spec (.of K))
    (hs : FiniteType s) (n : ℕ)
    (hreg : ∀ z, (pullback s (Spec.map (CommRingCat.ofHom (algebraMap K L)))).IsRegularAt z)
    (hC : ∀ C ∈ irreducibleComponents
      ↥(pullback s (Spec.map (CommRingCat.ofHom (algebraMap K L))) : Scheme.{u}),
      topologicalKrullDim C = n) :
    (Scheme.relativeDifferentials s).IsLocallyFreeOfRank n ∧
      ∀ C ∈ irreducibleComponents Z, topologicalKrullDim C = n := by
  set g := Spec.map (CommRingCat.ofHom (algebraMap K L))
  have : LocallyOfFiniteType s := hs.1
  have : QuasiCompact s := hs.2
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian s
  have : Surjective g := ⟨fun _ => ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  have : Flat g := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat), CommRingCat.hom_ofHom,
      RingHom.flat_algebraMap_iff]
    infer_instance
  -- Example 10.0.3: `Z_L` is smooth of relative dimension `n` over `L`.
  have : SmoothOfRelativeDimension n (pullback.snd s g) :=
    (smoothOfRelativeDimension_iff_forall_isRegularAt (pullback.snd s g)
      ⟨inferInstance, inferInstance⟩ n).2 ⟨hreg, hC⟩
  exact ⟨relativeDifferentials_isLocallyFreeOfRank_of_pullback_snd s g n
      (Scheme.relativeDifferentials_isLocallyFreeOfRank_of_smoothOfRelativeDimension _ n),
    topologicalKrullDim_irreducibleComponents_of_baseChange s hs hC⟩

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
  refine ⟨fun h => ?_, fun ⟨hreg, hC⟩ => ?_⟩
  · -- Proposition 10.1(b), then Example 10.0.3 on `Z_L`.
    have : SmoothOfRelativeDimension n (pullback.snd s g) :=
      smoothOfRelativeDimension_baseChange (IsPullback.of_hasPullback s g)
    exact (smoothOfRelativeDimension_iff_forall_isRegularAt (pullback.snd s g)
      ⟨inferInstance, inferInstance⟩ n).1 this
  · obtain ⟨hΩ, hCZ⟩ :=
      relativeDifferentials_isLocallyFreeOfRank_of_baseChange_isRegularAt s hs n hreg hC
    have h := smoothOfRelativeDimension_iff_flat_and_fiber_dim_and_finrank
      (X := Over.mk s) (Y := Over.mk (𝟙 (Spec (.of K)))) ⟨hs.1, hs.2⟩
      ⟨show LocallyOfFiniteType (𝟙 (Spec (.of K))) from inferInstance,
        show QuasiCompact (𝟙 (Spec (.of K))) from inferInstance⟩ (Over.homMk s (by simp)) n
    change SmoothOfRelativeDimension n s ↔ _ at h
    exact h.2 ⟨show Flat s from inferInstance,
      topologicalKrullDim_irreducibleComponents_fiber s hCZ,
      finrank_fibre_of_isLocallyFreeOfRank _ n hΩ⟩

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
  refine ⟨fun h => ?_, fun ⟨hflat, h⟩ => ?_⟩
  · have : Smooth f.left := SmoothOfRelativeDimension.smooth n _
    refine ⟨inferInstance, fun y => ?_⟩
    -- Proposition 10.1(b): the fibre `X_y → Spec k(y)` is smooth of relative dimension `n`.
    have : SmoothOfRelativeDimension n (f.left.fiberToSpecResidueField y) :=
      smoothOfRelativeDimension_baseChange (IsPullback.of_hasPullback f.left
        (Y.left.fromSpecResidueField y))
    exact (smoothOfRelativeDimension_iff_baseChange_isRegularAt
      (K := Y.left.residueField y) (L := AlgebraicClosure (Y.left.residueField y)) _ (hft y)
      n).1 this
  · have hfib := fun y : Y.left =>
      relativeDifferentials_isLocallyFreeOfRank_of_baseChange_isRegularAt
        (K := Y.left.residueField y) (L := AlgebraicClosure (Y.left.residueField y))
        (f.left.fiberToSpecResidueField y)
        (hft y) n (h y).1 (h y).2
    rw [smoothOfRelativeDimension_iff_flat_and_fiber_dim_and_finrank hX hY f n]
    refine ⟨hflat, fun y => (hfib y).2, fun x => ?_⟩
    -- II.8.10: the fibres of `Ω_{X/Y}` are the fibres of `Ω_{X_y/k(y)}`.
    rw [← f.left.fiberι_asFiber x]
    exact (finrank_fibre_relativeDifferentials_pullback_snd _ _ _).symm.trans
      (finrank_fibre_of_isLocallyFreeOfRank _ n (hfib (f.left x)).1 _)

end Hartshorne

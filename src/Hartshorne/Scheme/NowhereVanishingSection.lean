/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.NowhereVanishingSectionCount
import Hartshorne.Scheme.LocalFrameGerms
import Hartshorne.Scheme.LinearSystemBase
import Hartshorne.Scheme.DimensionCodimension
import Hartshorne.Scheme.CoherentFibreRank
import Hartshorne.Scheme.QuasicoherentAbelianClosure
import Hartshorne.Scheme.SymmetricAlgebraSheaf
import Hartshorne.Scheme.Differentials.NonsingularClosedImmersionConormal

/-!
# A nowhere-vanishing section of a generated bundle of large rank

Hartshorne, *Algebraic Geometry*, II, Exercise 8.2 (p. 187); used in V, Exercise 2.3(a).

Let `X` be a variety of dimension `n` over an algebraically closed field `k`, let `E` be a
locally free sheaf of rank `r > n`, and let `V ⊆ Γ(X, E)` be the `k`-span of finitely many
global sections `v_0, …, v_N` which generate `E`. Then some `s ∈ V` satisfies `s_x ∉ 𝔪_x E_x`
for every `x ∈ X`, and the morphism `𝒪_X → E`, `1 ↦ s`, sits in an exact sequence
`0 → 𝒪_X → E → E' → 0` with `E'` locally free (of rank `r - 1`).

## Proof

*The section.* Near every point some `r` of the `v_l` form a local frame of `E`
(`exists_embedding_isLocalFrame`); shrink to an affine open `W = Spec A`, so `A` is a domain of
finite type over `k` of dimension `n`. Writing `v_l = ∑_j a_{j l} v_{σ j}` on `W`, the section
`∑_l t_l v_l` (`t ∈ k^{N+1}`) has coordinates `g_j(t) = ∑_l t_l a_{j l}`, and it is nonzero in
the fibre at a point of `W` exactly when the `g_j(t)` do not all vanish there. The incidence
dimension count (`exists_ne_zero_forall_span_eq_top`) gives a nonzero polynomial `P_W` on
`k^{N+1}` such that the `g_j(t)` generate the unit ideal of `A` whenever `P_W(t) ≠ 0`. Finitely
many such `W` cover `X`, and since `k` is infinite some `t` is a non-root of every `P_W`.

*The exact sequence.* Let `E'` be the cokernel of `𝒪_X → E`, `1 ↦ s`. On sections this map is
`b ↦ b s`, injective since `s_x` is part of a basis of the free module `E_x` for every `x`. Taking
stalks is right exact, so `E'_x = E_x / 𝒪_{X,x} s_x`, and `E'_x ⊗ k(x)` is the quotient of
`E_x ⊗ k(x) ≅ k(x)^r` by the line spanned by the nonzero image of `s_x`: it has dimension
`r - 1` at every point. As `E'` is coherent and `X` is reduced and Noetherian, `E'` is locally
free of rank `r - 1` by the constant fibre dimension criterion (II, Exercise 5.8(c)).
-/

noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry IsLocalRing MvPolynomial
  CategoryTheory.Limits
open scoped TensorProduct

namespace Hartshorne

universe u

namespace NowhereVanishingSection

/-! ### Linear algebra over a local ring -/

section Algebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- An element outside `I • M` has a coordinate outside `I` in every finite basis. -/
theorem exists_repr_notMem_of_notMem_smul_top {κ : Type*} [Fintype κ]
    (b : Module.Basis κ R M) (I : Ideal R) {m : M} (hm : m ∉ I • (⊤ : Submodule R M)) :
    ∃ j, b.repr m j ∉ I := by
  by_contra h
  push Not at h
  apply hm
  rw [← b.sum_repr m]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem_smul (h j) Submodule.mem_top

variable [IsLocalRing R]

/-- In a module with a finite basis over a local ring, an element outside `𝔪 M` has zero
annihilator. -/
theorem eq_zero_of_smul_eq_zero_of_notMem {κ : Type*} [Fintype κ] (b : Module.Basis κ R M)
    {m : M} (hm : m ∉ maximalIdeal R • (⊤ : Submodule R M)) {a : R} (ha : a • m = 0) :
    a = 0 := by
  obtain ⟨j, hj⟩ := exists_repr_notMem_of_notMem_smul_top b _ hm
  have hu : IsUnit (b.repr m j) := by
    by_contra h
    exact hj ((mem_maximalIdeal _).mpr h)
  have h0 : a * b.repr m j = 0 := by
    have := congrArg (fun z => b.repr z j) ha
    simpa using this
  exact (hu.mul_left_eq_zero).mp h0

variable {N Q : Type*} [AddCommGroup N] [Module R N] [AddCommGroup Q] [Module R Q]

/-- **The fibre of a quotient by a unimodular element.** Let `M` be finite free over the local
ring `R`, let `N → M → Q → 0` be exact, and suppose the image of `N` is `R m` with
`m ∉ 𝔪 M`. Then `Q ⊗ k` has dimension `rank M - 1` over the residue field `k`. -/
theorem finrank_residueField_tensor_eq_sub_one [Module.Free R M] [Module.Finite R M]
    (f : N →ₗ[R] M) (g : M →ₗ[R] Q) (hfg : Function.Exact f g) (hg : Function.Surjective g)
    {m : M} (hm : m ∉ maximalIdeal R • (⊤ : Submodule R M))
    (hf : LinearMap.range f = Submodule.span R {m}) :
    Module.finrank (ResidueField R) (ResidueField R ⊗[R] Q) = Module.finrank R M - 1 := by
  set k := ResidueField R
  let f' := f.baseChange k
  let g' := g.baseChange k
  have hex : Function.Exact f' g' := lTensor_exact k hfg hg
  have hg' : Function.Surjective g' := LinearMap.lTensor_surjective k hg
  have h1m : (1 : k) ⊗ₜ[R] m ≠ 0 := by
    intro h
    apply hm
    have : m ∈ LinearMap.ker (TensorProduct.mk R (R ⧸ maximalIdeal R) M 1) := h
    rwa [LinearMap.ker_tensorProductMk] at this
  have hmf : m ∈ LinearMap.range f := by
    rw [hf]; exact Submodule.mem_span_singleton_self m
  have hrange : LinearMap.range f' = Submodule.span k {(1 : k) ⊗ₜ[R] m} := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨z, rfl⟩
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul c n =>
        have hn : f n ∈ Submodule.span R {m} := hf ▸ LinearMap.mem_range_self f n
        obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hn
        refine Submodule.mem_span_singleton.mpr ⟨a • c, ?_⟩
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, LinearMap.baseChange_tmul, ← ha,
          ← TensorProduct.smul_tmul]
      | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      obtain ⟨n, hn⟩ := hmf
      exact ⟨1 ⊗ₜ n, by rw [LinearMap.baseChange_tmul, hn]⟩
  have hker : LinearMap.ker g' = LinearMap.range f' := LinearMap.exact_iff.mp hex
  have hrn := LinearMap.finrank_range_add_finrank_ker g'
  rw [LinearMap.range_eq_top.mpr hg', finrank_top, hker, hrange,
    finrank_span_singleton h1m, Module.finrank_baseChange (R := k) (M' := M)] at hrn
  change Module.finrank k (k ⊗[R] Q) = _
  omega

end Algebra

/-! ### The section -/

section Section

variable {k : Type u} [Field k] {X : Scheme.{u}} (q : X ⟶ Spec (.of k))

/-- The `k`-algebra structure on the functions on an open `W`, through `q`. -/
abbrev sectionsAlgebra (W : X.Opens) : Algebra k Γ(X, W) :=
  ((X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom.comp (kConst q)).toAlgebra

/-- Over an affine open, the functions form a `k`-algebra of finite type. -/
theorem sectionsAlgebra_finiteType (hq : FiniteType q) {W : X.Opens} (hW : IsAffineOpen W) :
    letI := sectionsAlgebra q W
    Algebra.FiniteType k Γ(X, W) := by
  let := sectionsAlgebra q W
  let _ : LocallyOfFiniteType q := hq.1
  have hWle : W ≤ q ⁻¹ᵁ (⊤ : (Spec (.of k)).Opens) := by simp
  have hinv : Function.Surjective (Scheme.ΓSpecIso (.of k)).inv := by
    intro z
    exact ⟨(Scheme.ΓSpecIso (.of k)).hom z, by simp⟩
  have h : (algebraMap k Γ(X, W)) =
      (q.appLE ⊤ W hWle).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom := rfl
  change (algebraMap k Γ(X, W)).FiniteType
  rw [h]
  exact (q.finiteType_appLE (isAffineOpen_top _) hW hWle).comp
    (RingHom.FiniteType.of_surjective _ hinv)

variable [IsIntegral X] (hq : FiniteType q) {n : ℕ} (hn : topologicalKrullDim X = n)
  {E : X.Modules} {r : ℕ} (hE : E.IsLocallyFreeOfRank r) (hr : n < r) {N : ℕ}
  (v : Fin (N + 1) → Γ(E, ⊤))
  (hv : E.IsGeneratedBySections (fun i : ULift.{u} (Fin (N + 1)) => v i.down))

include hq hn hE hr hv in
/-- **The local polynomial.** Every point `x` has an open neighbourhood `W` and a nonzero
polynomial `P` on `k^{N+1}` such that `∑_l t_l v_l` is nonzero in the fibre at every point of
`W` whenever `P(t) ≠ 0`. -/
theorem exists_open_polynomial (x : X) :
    ∃ (W : X.Opens) (P : MvPolynomial (Fin (N + 1)) k), x ∈ W ∧ P ≠ 0 ∧
      ∀ t : Fin (N + 1) → k, eval t P ≠ 0 → ∀ y ∈ W,
        y ∈ nonvanishingLocus E (linearSystemSection q v t) := by
  classical
  obtain ⟨σ₀, U, hxU, hU⟩ := exists_embedding_isLocalFrame hE _ hv x
  let σ : Fin r ↪ Fin (N + 1) := σ₀.trans Equiv.ulift.toEmbedding
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU U.isOpen
  replace hWU : W ≤ U := hWU
  -- the frame `w_j = v_{σ j}|_W`
  let w : Fin r → Γ(E, W) := fun j => E.presheaf.map (homOfLE le_top).op (v (σ j))
  have hw : Ringed.IsLocalFrame (R := X.sheaf) E W w := by
    have h := hU.restrictLE hWU
    have hfam : (fun j => E.presheaf.map (homOfLE hWU).op
        (E.presheaf.map (homOfLE le_top).op (v (σ₀ j).down))) = w := by
      funext j
      exact res_res_frame E le_top hWU le_top _
    rw [← hfam]
    exact h
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  let := sectionsAlgebra q W
  have : Algebra.FiniteType k Γ(X, W) := sectionsAlgebra_finiteType q hq hW
  have hdim : ringKrullDim Γ(X, W) ≤ n := by
    obtain ⟨N', hN', hXN'⟩ := DimensionCodimension.exists_ringKrullDim_eq q hq W hW
    rw [hN', ← hXN', hn]
  -- coordinates of the `v_l` in the frame
  let a : Fin r → Fin (N + 1) → Γ(X, W) := fun j l =>
    hw.coord le_rfl (E.presheaf.map (homOfLE le_top).op (v l)) j
  have hcoord : ∀ l, E.presheaf.map (homOfLE le_top).op (v l) = ∑ j, a j l • w j := by
    intro l
    have h := (hw.localFrameMap_coord le_rfl (E.presheaf.map (homOfLE le_top).op (v l))).symm
    refine h.trans ((localFrameMap_apply_scheme w le_rfl _).trans ?_)
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    change E.presheaf.map (𝟙 _) (w j) = w j
    rw [CategoryTheory.Functor.map_id]
    rfl
  have ha : ∀ j j', a j (σ j') = if j = j' then 1 else 0 := by
    intro j j'
    have h := hw.coord_self le_rfl j'
    have hid : E.presheaf.map (homOfLE (le_refl W)).op (w j') = w j' := by
      change E.presheaf.map (𝟙 _) (w j') = w j'
      rw [CategoryTheory.Functor.map_id]
      rfl
    erw [hid] at h
    have := congrFun h j
    change a j (σ j') = _ at this
    rw [this]
    by_cases hjj : j = j' <;> simp [hjj] <;> rfl
  obtain ⟨P, hP, hgood⟩ :=
    exists_ne_zero_forall_span_eq_top (k := k) σ a ha hdim (by simpa using hr)
  refine ⟨W, P, hxW, hP, fun t ht y hy => ?_⟩
  have hspan := hgood t ht
  set g : Fin r → Γ(X, W) := fun j => ∑ l, algebraMap k Γ(X, W) (t l) * a j l with hg
  -- the restriction of `∑_l t_l v_l` to `W`
  have hres : E.presheaf.map (homOfLE le_top).op (linearSystemSection q v t) =
      ∑ j, g j • w j := by
    rw [linearSystemSection, map_sum]
    simp_rw [Scheme.Modules.map_smul, hcoord, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hg, Finset.sum_smul]
    rfl
  obtain ⟨b, hb⟩ := exists_basis_germ_of_isLocalFrame hw hy
  intro hmem
  have hgerm : E.presheaf.germ ⊤ y trivial (linearSystemSection q v t) =
      ∑ j, X.presheaf.germ W y hy (g j) • b j := by
    rw [← E.presheaf.germ_res_apply (homOfLE le_top) y hy, hres, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [germ_smul_frame, hb]
  have hrepr : ∀ j, X.presheaf.germ W y hy (g j) ∈ maximalIdeal (X.presheaf.stalk y) := by
    intro j
    have := repr_mem_of_mem_smul_top b _ hmem j
    rwa [hgerm, b.repr_sum_self] at this
  have h1 : (1 : Γ(X, W)) ∈ Ideal.span (Set.range g) := by
    rw [hspan]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Ideal.mem_span_range_iff_exists_fun).mp h1
  have h2 := congrArg (X.presheaf.germ W y hy) hc
  rw [map_one, map_sum] at h2
  apply (maximalIdeal (X.presheaf.stalk y)).ne_top_iff_one.mp (maximalIdeal.isMaximal _).ne_top
  rw [← h2]
  refine Ideal.sum_mem _ fun j _ => ?_
  rw [map_mul]
  exact Ideal.mul_mem_left _ _ (hrepr j)

include hq hn hE hr hv in
/-- **A nowhere-vanishing section.** Over an infinite field, some element of the linear system
spanned by the `v_l` is nonzero in the fibre at every point. -/
theorem exists_mem_linearSystem_nonvanishingLocus_eq_univ [Infinite k] :
    ∃ s ∈ linearSystem q v, nonvanishingLocus E s = Set.univ := by
  classical
  choose W P hxW hP hgood using exists_open_polynomial q hq hn hE hr v hv
  have : QuasiCompact q := hq.2
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover (fun x => (W x : Set X))
    (fun x => (W x).isOpen) (fun x _ => Set.mem_iUnion.mpr ⟨x, hxW x⟩)
  obtain ⟨t, ht⟩ := exists_forall_eval_ne_zero S P (fun x _ => hP x)
  refine ⟨linearSystemSection q v t, ⟨t, rfl⟩, Set.eq_univ_of_forall fun y => ?_⟩
  obtain ⟨x, hxS, hy⟩ := Set.mem_iUnion₂.mp (hS (Set.mem_univ y))
  exact hgood x t (ht x hxS) y hy

end Section

/-! ### The exact sequence -/

section ExactSequence

variable {X : Scheme.{u}}

/-- The morphism `𝒪_X → E` sending `1` to the global section `s`. -/
def sectionHom (E : X.Modules) (s : Γ(E, ⊤)) : structureModuleOf X ⟶ E :=
  E.unitHomEquiv.symm (Scheme.Modules.GloballyGenerated.sectionsOfTop E s)

/-- On sections over `U`, the morphism `𝒪_X → E`, `1 ↦ s`, is `b ↦ b s|_U`. -/
theorem sectionHom_app (E : X.Modules) (s : Γ(E, ⊤)) (U : X.Opens) (b : Γ(X, U)) :
    Scheme.Modules.Hom.app (sectionHom E s) U b = b • E.presheaf.map (homOfLE le_top).op s := by
  have h1 := Scheme.Modules.Hom.app_smul (M := SheafOfModules.unit X.ringCatSheaf)
    (sectionHom E s) b (1 : Γ(X, U))
  erw [smul_eq_mul, mul_one] at h1
  refine h1.trans ?_
  congr 1
  have := congrArg (fun σ => σ.val (op U))
    (E.unitHomEquiv.apply_symm_apply (Scheme.Modules.GloballyGenerated.sectionsOfTop E s))
  exact this

variable {E : X.Modules} {r : ℕ} (hE : E.IsLocallyFreeOfRank r) {s : Γ(E, ⊤)}
  (hs : nonvanishingLocus E s = Set.univ)

include hE hs in
/-- The morphism `𝒪_X → E`, `1 ↦ s`, is a monomorphism when `s` is nowhere vanishing. -/
theorem mono_sectionHom : Mono (sectionHom E s) := by
  have hzero : ∀ (U : X.Opens) (b : Γ(X, U)),
      b • E.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s = 0 → b = 0 := by
    intro U b hb
    refine TopCat.Presheaf.IsSheaf.section_ext X.sheaf.2 fun y hy => ?_
    obtain ⟨U', f, hyU', hf⟩ := Ringed.exists_isLocalFrame_of_isLocallyFreeOfRank
      ((Scheme.Modules.isLocallyFreeOfRank_iff_ringed E r).mp hE) y
    obtain ⟨bas, -⟩ := exists_basis_germ_of_isLocalFrame hf hyU'
    have hsy : E.presheaf.germ ⊤ y trivial s ∉
        maximalIdeal (X.presheaf.stalk y) •
          (⊤ : Submodule (X.presheaf.stalk y) (E.presheaf.stalk y)) := by
      have : y ∈ nonvanishingLocus E s := hs ▸ Set.mem_univ y
      exact this
    have h0 : X.presheaf.germ U y hy b • E.presheaf.germ ⊤ y trivial s = 0 := by
      have := congrArg (E.presheaf.germ U y hy) hb
      rw [germ_smul_frame, E.presheaf.germ_res_apply, map_zero] at this
      exact this
    have hg : X.presheaf.germ U y hy b = X.presheaf.germ U y hy 0 := by
      rw [eq_zero_of_smul_eq_zero_of_notMem bas hsy h0, map_zero]
    obtain ⟨W, hyW, i₁, i₂, heq⟩ := X.presheaf.germ_eq y hy hy b 0 hg
    refine ⟨W, i₁.le, hyW, ?_⟩
    have h₁ : i₁ = homOfLE i₁.le := Subsingleton.elim _ _
    have h₂ : i₂ = homOfLE i₁.le := Subsingleton.elim _ _
    rw [h₁, h₂] at heq
    exact heq
  have happ : ∀ U : X.Opens, Function.Injective (Scheme.Modules.Hom.app (sectionHom E s) U) := by
    intro U
    rw [injective_iff_map_eq_zero]
    intro b hb
    exact hzero U b ((sectionHom_app E s U b).symm.trans hb)
  have h1 : Mono ((PresheafOfModules.toPresheaf _).map (sectionHom E s).val) := by
    have : ∀ U, Mono (((PresheafOfModules.toPresheaf _).map (sectionHom E s).val).app U) :=
      fun U => (AddCommGrpCat.mono_iff_injective _).mpr (happ U.unop)
    exact NatTrans.mono_of_mono_app _
  have h2 : Mono (sectionHom E s).val := (PresheafOfModules.toPresheaf _).mono_of_mono_map h1
  exact (SheafOfModules.forget _).mono_of_mono_map h2

include hE hs in
/-- **The quotient by a nowhere-vanishing section.** On a reduced locally Noetherian scheme, if
`E` is locally free of rank `r` and `s` is nowhere vanishing, then
`0 → 𝒪_X → E → E / 𝒪_X s → 0` is exact and the cokernel is locally free of rank `r - 1`. -/
theorem shortExact_and_isLocallyFreeOfRank_cokernel [IsReduced X] [IsLocallyNoetherian X] :
    (ShortComplex.mk (C := X.Modules) (sectionHom E s) (cokernel.π (sectionHom E s))
        (cokernel.condition _)).ShortExact ∧
      Scheme.Modules.IsLocallyFreeOfRank (cokernel (C := X.Modules) (sectionHom E s))
        (r - 1) := by
  have hmono := mono_sectionHom hE hs
  let S := ShortComplex.mk (C := X.Modules) (sectionHom E s) (cokernel.π (sectionHom E s))
    (cokernel.condition _)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (S.exact_of_g_is_cokernel (cokernelIsCokernel _))
      hmono inferInstance
  refine ⟨hS, ?_⟩
  -- coherence of `E` and of the cokernel
  have hfl : Ringed.IsFiniteLocallyFree (R := X.sheaf) E := fun x => by
    obtain ⟨U, hxU, h⟩ := (Scheme.Modules.isLocallyFreeOfRank_iff_ringed E r).mp hE x
    exact ⟨U, hxU, r, h⟩
  have hEc : IsCoherent E :=
    ((coherent_affine_local_tfae E).out 1 0).mp
      (Ringed.IsFiniteLocallyFree.isFinitePresentation hfl)
  have hE'c : IsCoherent (cokernel (C := X.Modules) (sectionHom E s)) :=
    isCoherent_cokernel _ (isCoherent_structureSheafModule X) hEc
  refine (isLocallyFreeOfRank_iff_forall_finrank_fibre _ hE'c (r - 1)).mpr fun x => ?_
  have : IsLocalRing (ringSheafStalk X.sheaf x) :=
    inferInstanceAs (IsLocalRing (X.presheaf.stalk x))
  obtain ⟨hex, hsurj⟩ := NonsingularConormal.stalk_exact_and_surjective (R := X.sheaf) S
    hS.exact hS.epi_g x
  obtain ⟨U', f, hxU', hf⟩ := Ringed.exists_isLocalFrame_of_isLocallyFreeOfRank
    ((Scheme.Modules.isLocallyFreeOfRank_iff_ringed E r).mp hE) x
  obtain ⟨bas, -⟩ := exists_basis_germ_of_isLocalFrame hf hxU'
  have : Module.Free (X.presheaf.stalk x) (E.presheaf.stalk x) := Module.Free.of_basis bas
  have : Module.Finite (X.presheaf.stalk x) (E.presheaf.stalk x) := Module.Finite.of_basis bas
  have hrank : Module.finrank (X.presheaf.stalk x) (E.presheaf.stalk x) = r := by
    rw [Module.finrank_eq_card_basis bas]
    simp
  have hsx : E.presheaf.germ ⊤ x trivial s ∉
      maximalIdeal (X.presheaf.stalk x) •
        (⊤ : Submodule (X.presheaf.stalk x) (E.presheaf.stalk x)) := by
    have : x ∈ nonvanishingLocus E s := hs ▸ Set.mem_univ x
    exact this
  let Fx := Ringed.moduleStalkFunctor (R := X.sheaf) x
  let φ := (Fx.map S.f).hom
  let ψ := (Fx.map S.g).hom
  let m : Fx.obj E := E.presheaf.germ ⊤ x trivial s
  have hm : m ∉ maximalIdeal (ringSheafStalk X.sheaf x) •
      (⊤ : Submodule (ringSheafStalk X.sheaf x) (Fx.obj E)) := hsx
  have hφ : ∀ (U : X.Opens) (hU : x ∈ U) (t : Γ(X, U)),
      φ (ModuleSheafTensor.sectionGerm _ x U hU t) =
        (show ringSheafStalk X.sheaf x from X.presheaf.germ U x hU t) • m := by
    intro U hU t
    have h1 := Ringed.moduleStalkFunctor_map_germ (R := X.sheaf) x (sectionHom E s) U hU t
    refine h1.trans ?_
    change E.presheaf.germ U x hU (Scheme.Modules.Hom.app (sectionHom E s) U t) = _
    rw [sectionHom_app, germ_smul_frame, E.presheaf.germ_res_apply]
    rfl
  have hrange : LinearMap.range φ = Submodule.span (ringSheafStalk X.sheaf x) {m} := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨z, rfl⟩
      obtain ⟨U, hU, t, rfl⟩ := ModuleSheafTensor.exists_sectionGerm _ x z
      rw [hφ U hU t]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      refine ⟨ModuleSheafTensor.sectionGerm _ x ⊤ trivial (1 : Γ(X, ⊤)), ?_⟩
      refine (hφ ⊤ trivial (1 : Γ(X, ⊤))).trans ?_
      convert one_smul (ringSheafStalk X.sheaf x) m using 2
      exact map_one (X.presheaf.germ ⊤ x trivial).hom
  have : Module.Free (ringSheafStalk X.sheaf x) (Fx.obj E) := Module.Free.of_basis bas
  have : Module.Finite (ringSheafStalk X.sheaf x) (Fx.obj E) := Module.Finite.of_basis bas
  have key := finrank_residueField_tensor_eq_sub_one φ ψ hex hsurj hm hrange
  have hrank' : Module.finrank (ringSheafStalk X.sheaf x) (Fx.obj E) = r := hrank
  rw [hrank'] at key
  exact key

end ExactSequence

end NowhereVanishingSection

/-! ### Main result -/

open NowhereVanishingSection in
/-- **Hartshorne II, Exercise 8.2.** Let `X` be a variety of dimension `n` over an algebraically
closed field `k` (an integral separated scheme of finite type over `k`), let `E` be a locally
free `𝒪_X`-module of rank `r > n`, and let `V ⊆ Γ(X, E)` be the `k`-span of global sections
`v_0, …, v_N` which generate `E`. Then some `s ∈ V` satisfies `s_x ∉ 𝔪_x E_x` for every
`x ∈ X`, and the morphism `𝒪_X → E`, `1 ↦ s`, sits in a short exact sequence
`0 → 𝒪_X → E → E' → 0` with `E'` locally free (of rank `r - 1`). -/
theorem exists_nonvanishing_section_shortExact {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (q : X ⟶ Spec (.of k)) [IsIntegral X] (hq : FiniteType q) [IsSeparated q]
    {n : ℕ} (hn : topologicalKrullDim X = n) {E : X.Modules} {r : ℕ}
    (hE : E.IsLocallyFreeOfRank r) (hr : n < r) {N : ℕ} (v : Fin (N + 1) → Γ(E, ⊤))
    (hv : E.IsGeneratedBySections (fun i : ULift.{u} (Fin (N + 1)) => v i.down)) :
    ∃ s ∈ linearSystem q v, nonvanishingLocus E s = Set.univ ∧
      ∃ (E' : X.Modules) (p : E ⟶ E') (w : sectionHom E s ≫ p = 0),
        (ShortComplex.mk (sectionHom E s) p w).ShortExact ∧ E'.IsLocallyFreeOfRank (r - 1) := by
  obtain ⟨s, hsV, hs⟩ :=
    exists_mem_linearSystem_nonvanishingLocus_eq_univ q hq hn hE hr v hv
  have : LocallyOfFiniteType q := hq.1
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian q
  obtain ⟨hS, hfree⟩ := shortExact_and_isLocallyFreeOfRank_cokernel hE hs
  exact ⟨s, hsV, hs, _, _, _, hS, hfree⟩

end Hartshorne

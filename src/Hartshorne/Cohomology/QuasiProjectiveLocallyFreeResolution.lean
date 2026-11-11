/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.VeryAmplePowerImpliesAmple
import Hartshorne.Scheme.FiniteTwistedFreeCover
import Hartshorne.Scheme.PicardPullback
import Hartshorne.Scheme.SymmetricAlgebraSheaf
import Hartshorne.Scheme.QuasicoherentAbelianClosure
import Hartshorne.Scheme.ProjectiveSpaceOverScheme
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.SingleHomology

/-!
# Locally free resolutions on quasi-projective schemes

Hartshorne, *Algebraic Geometry*, III.6, Example 6.5.1 (p. 235).

Let `X` be quasi-projective over a Noetherian ring `A`, that is, `X ⟶ Spec A` factors as an open
immersion `X ⟶ Z` followed by a projective morphism `Z ⟶ Spec A`. Every coherent `𝒪_X`-module
`F` has a resolution `⋯ ⟶ L₁ ⟶ L₀ ⟶ F ⟶ 0`, possibly unbounded to the left, by locally free
`𝒪_X`-modules of finite rank: a chain complex `L` indexed by `ℕ` with a quasi-isomorphism
`L ⟶ F[0]` (`Hartshorne.exists_quasiIso_locallyFreeResolution_of_quasiProjective`). This is the
form of resolution that computes `ℰxt` (Hartshorne III, Proposition 6.5,
`Hartshorne.Ringed.sheafExtIsoHomologyOfLocallyFreeResolution`). That result is stated for module
sheaves on a ringed space, whose category instances differ from those of `X.Modules`. The variant
`Hartshorne.exists_quasiIso_locallyFreeResolution_of_quasiProjective_sheafOfModules` gives the
resolution in that category.

## Proof

The scheme `Z` is projective over the Noetherian ring `A`, hence Noetherian, and `X` is locally
Noetherian. Write `Z ⟶ ℙʳ_A` for the closed immersion and `M` for the pullback of `𝒪(1)`, which is
very ample on `Z` relative to `Spec A`.

* A coherent `F` on `X` extends to a coherent `G` on `Z`
  (`Hartshorne.VeryAmplePower.exists_isCoherent_restrict_iso_of_isOpenImmersion`).
* By Hartshorne II, Corollary 5.18 (`Hartshorne.exists_epi_sigma_tensorZPow_of_projective`), `G`
  is a quotient of a finite direct sum `⨁ᵢ M^{⊗ mᵢ}`. Pulling back to `X` (a left adjoint, so
  preserving epimorphisms and coproducts) gives an epimorphism `E ⟶ F` from a finite direct sum
  of invertible sheaves, which is locally free of finite rank and hence coherent.
* The kernel of `E ⟶ F` is again coherent, `X` being locally Noetherian, so the construction
  can be repeated.

Splicing the short exact sequences `0 ⟶ Kₙ₊₁ ⟶ Eₙ ⟶ Kₙ ⟶ 0` (with `K₀ = F`) gives the resolution;
this last step is the general homological lemma
`Hartshorne.QuasiProjectiveResolution.exists_quasiIso_toSingle₀`.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace Hartshorne

namespace QuasiProjectiveResolution

/-! ### Resolutions from epimorphisms with good kernels -/

section Splice

variable {C : Type*} [Category C] [Abelian C] {P : C → Prop} (E : ∀ F, P F → C)
  (π : ∀ F hF, E F hF ⟶ F) (hK : ∀ F hF, P (kernel (π F hF))) (F : C) (hF : P F)

/-- The successive kernels: `K₀ = F` and `Kₙ₊₁ = ker(E(Kₙ) ⟶ Kₙ)`. -/
noncomputable def stage : ℕ → {K : C // P K}
  | 0 => ⟨F, hF⟩
  | n + 1 => ⟨kernel (π (stage n).1 (stage n).2), hK _ _⟩

/-- The `n`-th term `E(Kₙ)` of the resolution. -/
noncomputable def obj (n : ℕ) : C := E (stage E π hK F hF n).1 (stage E π hK F hF n).2

/-- The epimorphism `E(Kₙ) ⟶ Kₙ`. -/
noncomputable def pr (n : ℕ) : obj E π hK F hF n ⟶ (stage E π hK F hF n).1 := π _ _

/-- The inclusion `Kₙ₊₁ = ker(E(Kₙ) ⟶ Kₙ) ⟶ E(Kₙ)`. -/
noncomputable def ιK (n : ℕ) : (stage E π hK F hF (n + 1)).1 ⟶ obj E π hK F hF n :=
  kernel.ι (pr E π hK F hF n)

@[reassoc (attr := simp)]
lemma ιK_pr (n : ℕ) : ιK E π hK F hF n ≫ pr E π hK F hF n = 0 := kernel.condition _

instance (n : ℕ) : Mono (ιK E π hK F hF n) := inferInstanceAs (Mono (kernel.ι _))

/-- `Kₙ₊₁ ⟶ E(Kₙ)` is a kernel of `E(Kₙ) ⟶ Kₙ`. -/
noncomputable def ιKIsLimit (n : ℕ) :
    IsLimit (KernelFork.ofι (ιK E π hK F hF n) (ιK_pr E π hK F hF n)) :=
  kernelIsKernel _

/-- The spliced complex `⋯ ⟶ E(K₁) ⟶ E(K₀)`, with differential `E(Kₙ₊₁) ⟶ Kₙ₊₁ ⟶ E(Kₙ)`. -/
noncomputable def complex : ChainComplex C ℕ :=
  ChainComplex.of (obj E π hK F hF) (fun n => pr E π hK F hF (n + 1) ≫ ιK E π hK F hF n)
    (fun n => by simp only [Category.assoc, ιK_pr_assoc, zero_comp, comp_zero])

lemma complex_X (n : ℕ) : (complex E π hK F hF).X n = obj E π hK F hF n := rfl

lemma complex_d_succ (n : ℕ) :
    (complex E π hK F hF).d (n + 1) n = pr E π hK F hF (n + 1) ≫ ιK E π hK F hF n := by
  exact ChainComplex.of_d (obj E π hK F hF) (fun n => pr E π hK F hF (n + 1) ≫ ιK E π hK F hF n) n

variable {E π hK} in
lemma exact_pr (hπ : ∀ F hF, Epi (π F hF)) (n : ℕ) :
    (ShortComplex.mk (pr E π hK F hF (n + 1) ≫ ιK E π hK F hF n) (pr E π hK F hF n)
      (by simp only [Category.assoc, ιK_pr, comp_zero])).Exact := by
  have : Epi (pr E π hK F hF (n + 1)) := hπ _ _
  let α : ShortComplex.mk (pr E π hK F hF (n + 1) ≫ ιK E π hK F hF n) (pr E π hK F hF n)
      (by simp only [Category.assoc, ιK_pr, comp_zero]) ⟶
      ShortComplex.mk (ιK E π hK F hF n) (pr E π hK F hF n) (ιK_pr E π hK F hF n) :=
    { τ₁ := pr E π hK F hF (n + 1)
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := (Category.comp_id _).symm
      comm₂₃ := (Category.id_comp _).trans (Category.comp_id _).symm }
  have : Epi α.τ₁ := hπ _ _
  have : IsIso α.τ₂ := inferInstanceAs (IsIso (𝟙 _))
  have : Mono α.τ₃ := inferInstanceAs (Mono (𝟙 _))
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono α).2
    (ShortComplex.exact_of_f_is_kernel _ (ιKIsLimit E π hK F hF n))

variable {E π hK} in
lemma complex_exactAt_succ (hπ : ∀ F hF, Epi (π F hF)) (n : ℕ) :
    (complex E π hK F hF).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 1 + 1) (n + 1) n (by simp) (by simp)]
  let α : ShortComplex.mk (pr E π hK F hF (n + 1 + 1) ≫ ιK E π hK F hF (n + 1))
      (pr E π hK F hF (n + 1)) (by simp only [Category.assoc, ιK_pr, comp_zero]) ⟶
      (complex E π hK F hF).sc' (n + 1 + 1) (n + 1) n :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := ιK E π hK F hF n
      comm₁₂ := (Category.id_comp _).trans
        ((complex_d_succ E π hK F hF (n + 1)).trans (Category.comp_id _).symm)
      comm₂₃ := (Category.id_comp _).trans (complex_d_succ E π hK F hF n) }
  have : Epi α.τ₁ := inferInstanceAs (Epi (𝟙 _))
  have : IsIso α.τ₂ := inferInstanceAs (IsIso (𝟙 _))
  have : Mono α.τ₃ := inferInstanceAs (Mono (ιK E π hK F hF n))
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono α).1 (exact_pr F hF hπ (n + 1))

/-- The augmentation `E(K₀) ⟶ K₀ = F`, as a morphism to `F[0]`. -/
noncomputable def augmentation : complex E π hK F hF ⟶ (ChainComplex.single₀ C).obj F :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨pr E π hK F hF 0, by
    exact (congrArg (· ≫ pr E π hK F hF 0) (complex_d_succ E π hK F hF 0)).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (pr E π hK F hF 1 ≫ ·) (ιK_pr E π hK F hF 0)).trans comp_zero))⟩

lemma augmentation_f_zero : (augmentation E π hK F hF).f 0 = pr E π hK F hF 0 :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

variable {E π hK} in
lemma quasiIso_augmentation (hπ : ∀ F hF, Epi (π F hF)) :
    QuasiIso (augmentation E π hK F hF) := ⟨fun n => by
  cases n
  · rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
    · have : Epi (pr E π hK F hF 0) := hπ _ _
      refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2 ⟨exact_pr F hF hπ 0, by
        dsimp; infer_instance⟩
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        ((Category.id_comp _).trans ((complex_d_succ E π hK F hF 0).symm.trans
          (Category.comp_id _).symm))
        ((Category.id_comp _).trans ((augmentation_f_zero E π hK F hF).symm.trans
          (Category.comp_id _).symm))
    all_goals rfl
  · rw [quasiIsoAt_iff_exactAt']
    · exact complex_exactAt_succ F hF hπ _
    · exact ChainComplex.exactAt_succ_single_obj _ _⟩

end Splice

/-- **Resolutions from epimorphisms with good kernels.** In an abelian category, let `P` and `Q` be
properties of objects such that every object `F` with `P` is the target of an epimorphism `E ⟶ F`
with `Q E` and `P (ker(E ⟶ F))`. Then every `F` with `P` has a resolution `L_• ⟶ F[0]`, a
quasi-isomorphism from a chain complex indexed by `ℕ`, whose terms all satisfy `Q`. -/
theorem exists_quasiIso_toSingle₀ {C : Type*} [Category C] [Abelian C] (P Q : C → Prop)
    (h : ∀ F, P F → ∃ (E : C) (π : E ⟶ F), Epi π ∧ Q E ∧ P (kernel π)) (F : C) (hF : P F) :
    ∃ (L : ChainComplex C ℕ) (π : L ⟶ (ChainComplex.single₀ C).obj F),
      QuasiIso π ∧ ∀ n, Q (L.X n) := by
  choose E π hπ hQ hK using h
  exact ⟨complex E π hK F hF, augmentation E π hK F hF, quasiIso_augmentation F hF hπ,
    fun n => hQ _ _⟩

/-! ### Finite sums of invertible sheaves -/

/-- The integer tensor powers `L^{⊗ m}` of an invertible sheaf are invertible. -/
theorem isInvertible_tensorZPow {X : Scheme.{u}} {L : X.Modules}
    (hL : Ringed.IsInvertible (R := X.sheaf) L) :
    ∀ m : ℤ, Ringed.IsInvertible (R := X.sheaf) (tensorZPow L m)
  | .ofNat n => Ringed.isInvertible_moduleSheafTensorPower hL n
  | .negSucc n =>
    Ringed.isInvertible_moduleSheafDual (Ringed.isInvertible_moduleSheafTensorPower hL (n + 1))

/-- A finite direct sum of invertible sheaves is locally free of rank the number of summands. -/
theorem isLocallyFreeOfRank_sigma_of_isInvertible {X : Scheme.{u}} {ι : Type u} [Fintype ι]
    (L : ι → X.Modules) (hL : ∀ i, Ringed.IsInvertible (R := X.sheaf) (L i)) :
    (∐ L).IsLocallyFreeOfRank (Fintype.card ι) := by
  classical
  intro x
  choose U e hx he using fun i => Ringed.exists_isLocalFrame_of_isLocallyFreeOfRank (hL i) x
  let V : X.Opens := ⟨⋂ i, (U i : Set X), isOpen_iInter_of_finite fun i => (U i).isOpen⟩
  have hVU : ∀ i, V ≤ U i := fun i => Set.iInter_subset _ i
  have hα : ∀ i, Nonempty ((L i).restrict V.ι ≅ SheafOfModules.free (ULift.{u} (Fin 1))) :=
    fun i => (Scheme.Modules.nonempty_restrict_iso_free_iff _ V _).mpr
      (Ringed.nonempty_over_iso_free_of_isLocalFrame ((he i).restrictLE (hVU i)))
  let G := Scheme.Modules.restrictFunctor V.ι
  have : PreservesColimitsOfShape (Discrete ι) G :=
    (Scheme.Modules.restrictAdjunction V.ι).leftAdjoint_preservesColimits.{u, u}
      |>.preservesColimitsOfShape
  refine ⟨V, Set.mem_iInter.mpr hx, ⟨?_⟩⟩
  exact PreservesCoproduct.iso G L ≪≫
    Sigma.mapIso (fun i => (hα i).some ≪≫ coproductUniqueIso _) ≪≫
    SheafOfModules.freeFunctor.mapIso ((Fintype.equivFin ι).trans Equiv.ulift.symm).toIso

/-! ### The first step of the resolution -/

/-- On a scheme `X` quasi-projective over a Noetherian ring `A`, every coherent `𝒪_X`-module `F`
is the target of an epimorphism `E ⟶ F` from a locally free `𝒪_X`-module of finite rank with
coherent kernel. -/
theorem exists_epi_isFiniteLocallyFree {A : Type u} [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} {f : X ⟶ Spec (.of A)} (hf : QuasiProjective f) (F : X.Modules)
    (hF : IsCoherent F) :
    ∃ (E : X.Modules) (π : E ⟶ F), Epi π ∧ Ringed.IsFiniteLocallyFree (R := X.sheaf) E ∧
      IsCoherent (kernel π) := by
  obtain ⟨Z, o, g, ho, hg, -⟩ := hf
  obtain ⟨r, c, hc, hcg⟩ := id hg
  let M := (Scheme.Modules.pullback c).obj (projectiveSpaceTwistingSheaf r (Spec (.of A)) 1)
  have hM : IsVeryAmpleRelative g M :=
    ⟨Scheme.Modules.IsInvertible.pullback c (isInvertible_projectiveSpaceTwistingSheaf r _ 1),
      r, Z, 𝟙 Z, c, inferInstance, hc, by rw [Category.id_comp, hcg],
      ⟨(Scheme.Modules.pullbackCongr (Category.id_comp c)).app _⟩⟩
  have : IsNoetherian Z := by
    have := hg.isProper
    exact finiteType_isNoetherian g ⟨inferInstance, inferInstance⟩
  have : IsLocallyNoetherian X := isLocallyNoetherian_of_isOpenImmersion o
  obtain ⟨G, hG, ⟨γ⟩⟩ := VeryAmplePower.exists_isCoherent_restrict_iso_of_isOpenImmersion o F hF
  obtain ⟨ι, hι, m, π, hπ⟩ := exists_epi_sigma_tensorZPow_of_projective hg hM G hG
  have := Fintype.ofFinite ι
  have hMinv : Ringed.IsInvertible (R := Z.sheaf) M :=
    (Scheme.Modules.isInvertible_iff_ringed M).mp hM.1
  let Φ := Scheme.Modules.pullback o
  have : PreservesColimitsOfShape (Discrete ι) Φ :=
    (Scheme.Modules.pullbackPushforwardAdjunction o).leftAdjoint_preservesColimits.{u, u}
      |>.preservesColimitsOfShape
  let E : X.Modules := ∐ fun i => Φ.obj (tensorZPow M (m i))
  let π' : E ⟶ F := (PreservesCoproduct.iso Φ _).inv ≫ Φ.map π ≫
    ((Scheme.Modules.restrictFunctorIsoPullback o).app G).inv ≫ γ.hom
  have hΦπ : Epi (Φ.map π) := Φ.map_epi π
  have hπ' : Epi π' := epi_comp _ _
  have hE : Ringed.IsFiniteLocallyFree (R := X.sheaf) E :=
    ((Scheme.Modules.isLocallyFreeOfRank_iff_ringed _ _).mp
      (isLocallyFreeOfRank_sigma_of_isInvertible _ fun i =>
        isInvertible_pullback o (isInvertible_tensorZPow hMinv (m i)))).isFiniteLocallyFree
  have : SheafOfModules.IsFinitePresentation.{u, u, u} E := hE.isFinitePresentation
  exact ⟨E, π', hπ', hE, isCoherent_kernel π' (isCoherent_of_isFinitePresentation E) hF⟩

end QuasiProjectiveResolution

/- As in `Hartshorne.RingedSpace.SheafExtLocallyFreeResolution`, state chain complexes of module
sheaves with the preadditive structure coming from the abelian structure, so that the
`SheafOfModules` form below can be fed to
`Hartshorne.Ringed.sheafExtIsoHomologyOfLocallyFreeResolution`. -/
attribute [local instance 2000] Abelian.toPreadditive

open QuasiProjectiveResolution in
/-- **Locally free resolutions on quasi-projective schemes** (Hartshorne III, Example 6.5.1,
p. 235). Let `X` be quasi-projective over a Noetherian ring `A`, that is, `f : X ⟶ Spec A` is an
open immersion followed by a projective morphism. Every coherent `𝒪_X`-module `F` has a
resolution `⋯ ⟶ L₁ ⟶ L₀ ⟶ F ⟶ 0`, possibly unbounded to the left, by locally free
`𝒪_X`-modules of finite rank: a chain complex `L` indexed by `ℕ`, with every `Lₙ` locally free of
finite rank, and a quasi-isomorphism `π : L ⟶ F[0]`. -/
theorem exists_quasiIso_locallyFreeResolution_of_quasiProjective {A : Type u} [CommRing A]
    [IsNoetherianRing A] {X : Scheme.{u}} {f : X ⟶ Spec (.of A)} (hf : QuasiProjective f)
    (F : X.Modules) (hF : IsCoherent F) :
    ∃ (L : ChainComplex X.Modules ℕ) (π : L ⟶ (ChainComplex.single₀ X.Modules).obj F),
      QuasiIso π ∧ ∀ n, Ringed.IsFiniteLocallyFree (R := X.sheaf) (L.X n) :=
  exists_quasiIso_toSingle₀ IsCoherent (Ringed.IsFiniteLocallyFree (R := X.sheaf))
    (fun G hG => exists_epi_isFiniteLocallyFree hf G hG) F hF

open QuasiProjectiveResolution in
/-- **Locally free resolutions on quasi-projective schemes**, in the category of module sheaves
over the ringed space `(X, 𝒪_X)` (Hartshorne III, Example 6.5.1, p. 235). This is
`exists_quasiIso_locallyFreeResolution_of_quasiProjective` for `SheafOfModules (ringCatSheafOf
X.sheaf)`, which is the category of `X.Modules` with different instances. In this form the
resolution can be passed directly to `Hartshorne.Ringed.sheafExtIsoHomologyOfLocallyFreeResolution`
(Hartshorne III, Proposition 6.5). -/
theorem exists_quasiIso_locallyFreeResolution_of_quasiProjective_sheafOfModules {A : Type u}
    [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}} {f : X ⟶ Spec (.of A)}
    (hf : QuasiProjective f) (F : SheafOfModules.{u} (ringCatSheafOf X.sheaf))
    (hF : IsCoherent (X := X) F) :
    ∃ (L : ChainComplex (SheafOfModules.{u} (ringCatSheafOf X.sheaf)) ℕ)
      (π : L ⟶ (ChainComplex.single₀ _).obj F),
      QuasiIso π ∧ ∀ n, Ringed.IsFiniteLocallyFree (L.X n) :=
  exists_quasiIso_toSingle₀ (C := SheafOfModules.{u} (ringCatSheafOf X.sheaf))
    (fun G => IsCoherent (X := X) G) Ringed.IsFiniteLocallyFree
    (fun G hG => exists_epi_isFiniteLocallyFree hf G hG) F hF

end Hartshorne

/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.RightDerivedLongExactSequence
import Hartshorne.Cohomology.ResolutionToInjectiveComplex
import Hartshorne.Cohomology.CechDerivedComparison
import Hartshorne.Cohomology.FlasqueCechAcyclic
import Hartshorne.Cohomology.SheafCohomologyFlasque
import Hartshorne.Cohomology.SheafCohomologyLongExactSequence
import Hartshorne.Cohomology.QuasicoherentFlasqueEnvelope
import Hartshorne.Cohomology.AffineQuasicoherentAcyclic
import Hartshorne.Scheme.AffineGlobalSectionsExact
import Hartshorne.Scheme.QuasicoherentAbelianClosure

/-!
# Affine covers compute quasi-coherent cohomology

Hartshorne, *Algebraic Geometry*, III, Theorem 4.5 (p. 222).

Let `X` be a Noetherian separated scheme, `U` an open affine cover of `X` and `F` a
quasi-coherent `𝒪_X`-module. Then the natural maps `Ȟ^p(U, F) ⟶ H^p(X, F)` of Lemma III.4.4 are
isomorphisms for all `p` (`Hartshorne.isIso_cechToSheafCohomology_of_isQuasicoherent`,
`Hartshorne.cechCohomologyIsoOfIsQuasicoherent`).

## Proof

We follow Hartshorne. Embed `F` in a flasque quasi-coherent sheaf `G` (Corollary III.3.6) and let
`R = G/F`, which is quasi-coherent. Finite intersections of the open affines `U_i` are affine
because `X` is separated, so on each of them `0 ⟶ F ⟶ G ⟶ R ⟶ 0` stays exact on sections
(Proposition II.5.6). Hence the Čech complexes form a short exact sequence, and so do the
sheafified Čech complexes `𝒞^•(U, -)`, which are resolutions (Lemma III.4.2). Since `G` is
flasque, `Ȟ^p(U, G) = 0` (Proposition III.4.3) and `H^p(X, G) = 0` for `p > 0`. Comparing the two
long exact sequences shows that `Ȟ^{p+1}(U, F)` and `H^{p+1}(X, F)` are the cokernels of
`Ȟ^p(U, G) ⟶ Ȟ^p(U, R)` and of `H^p(X, G) ⟶ H^p(X, R)`, compatibly with the comparison maps, so
induction on `p` (the case `p = 0` being Lemma III.4.4) applied to `G` and `R` gives the result.

The compatibility of the comparison maps with the connecting morphisms
(`Hartshorne.AffineCoverComparison.cechδ_comp_cechToSheafCohomology`) is an instance of a general
statement (`Hartshorne.ResolutionDelta.Data.δ_comp_comparison`): a degreewise short exact sequence
of resolutions of a short exact sequence maps to the horseshoe injective resolution used to define
the connecting morphisms of right derived functors, extending given comparison maps on the outer
terms.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Hartshorne

universe v u

namespace ResolutionDelta

open HomologicalComplex CochainComplex RightDerivedLES RightDerivedLES.Horseshoe

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The degree-`0` component of an augmentation, with source written as `A`. -/
def e {A : C} {L : CochainComplex C ℕ} (ε : (CochainComplex.single₀ C).obj A ⟶ L) :
    A ⟶ L.X 0 :=
  ((CochainComplex.fromSingle₀Equiv _ _) ε).1

@[reassoc (attr := simp)]
lemma e_d {A : C} {L : CochainComplex C ℕ} (ε : (CochainComplex.single₀ C).obj A ⟶ L) :
    e ε ≫ L.d 0 1 = 0 :=
  ((CochainComplex.fromSingle₀Equiv _ _) ε).2

lemma e_comp {A : C} {L L' : CochainComplex C ℕ} (ε : (CochainComplex.single₀ C).obj A ⟶ L)
    (φ : L ⟶ L') : e ε ≫ φ.f 0 = e (ε ≫ φ) := rfl

lemma single_comp_e {A B : C} {L : CochainComplex C ℕ} (f : A ⟶ B)
    (ε : (CochainComplex.single₀ C).obj B ⟶ L) :
    f ≫ e ε = e ((CochainComplex.single₀ C).map f ≫ ε) := by
  simp [e]

variable (C) in
/-- A short exact sequence `S` in `C`, a degreewise short exact sequence `K` of resolutions of
its terms, and comparison maps from the outer resolutions to injective resolutions. -/
structure Data where
  /-- The short exact sequence of objects. -/
  S : ShortComplex C
  /-- `S` is short exact. -/
  hS : S.ShortExact
  /-- The sequence of complexes. -/
  K : ShortComplex (CochainComplex C ℕ)
  /-- `K` is short exact in each degree. -/
  hK : ∀ n, (K.map (HomologicalComplex.eval C (ComplexShape.up ℕ) n)).ShortExact
  /-- The augmentation of the first term. -/
  ε₁ : (CochainComplex.single₀ C).obj S.X₁ ⟶ K.X₁
  /-- The augmentation of the second term. -/
  ε₂ : (CochainComplex.single₀ C).obj S.X₂ ⟶ K.X₂
  /-- The augmentation of the third term. -/
  ε₃ : (CochainComplex.single₀ C).obj S.X₃ ⟶ K.X₃
  /-- The third augmentation is a resolution. -/
  quasiIso₃ : QuasiIso ε₃
  /-- The augmentations commute with the first maps. -/
  hε₁₂ : ε₁ ≫ K.f = (CochainComplex.single₀ C).map S.f ≫ ε₂
  /-- The augmentations commute with the second maps. -/
  hε₂₃ : ε₂ ≫ K.g = (CochainComplex.single₀ C).map S.g ≫ ε₃
  /-- An injective resolution of the first term. -/
  J₁ : InjectiveResolution S.X₁
  /-- An injective resolution of the third term. -/
  J₃ : InjectiveResolution S.X₃
  /-- A comparison map from the first resolution. -/
  φ₁ : K.X₁ ⟶ J₁.cocomplex
  /-- A comparison map from the third resolution. -/
  φ₃ : K.X₃ ⟶ J₃.cocomplex
  /-- `φ₁` is compatible with the augmentations. -/
  hφ₁ : ε₁ ≫ φ₁ = J₁.ι
  /-- `φ₃` is compatible with the augmentations. -/
  hφ₃ : ε₃ ≫ φ₃ = J₃.ι

namespace Data

variable (D : Data C)

attribute [instance] quasiIso₃

lemma mono_f (n : ℕ) : Mono (D.K.f.f n) := (D.hK n).mono_f

lemma epi_g (n : ℕ) : Epi (D.K.g.f n) := (D.hK n).epi_g

@[reassoc (attr := simp)]
lemma f_g (n : ℕ) : D.K.f.f n ≫ D.K.g.f n = 0 := by
  rw [← HomologicalComplex.comp_f, D.K.zero, HomologicalComplex.zero_f]

/-- An extension of `φ₁ⁿ` along the monomorphism `K₁ⁿ ⟶ K₂ⁿ`. -/
def α (n : ℕ) : D.K.X₂.X n ⟶ D.J₁.cocomplex.X n :=
  haveI := D.mono_f n
  Injective.factorThru (D.φ₁.f n) (D.K.f.f n)

@[reassoc (attr := simp)]
lemma f_α (n : ℕ) : D.K.f.f n ≫ D.α n = D.φ₁.f n := by
  have := D.mono_f n
  exact Injective.comp_factorThru _ _

/-- The failure of `α` to be a cochain map, as a map `K₃ⁿ ⟶ J₁ⁿ⁺¹`. -/
def τ (n : ℕ) : D.K.X₃.X n ⟶ D.J₁.cocomplex.X (n + 1) :=
  (CokernelCofork.IsColimit.desc' (D.hK n).gIsCokernel
    (D.K.X₂.d n (n + 1) ≫ D.α (n + 1) - D.α n ≫ D.J₁.cocomplex.d n (n + 1)) (by
      change D.K.f.f n ≫ _ = 0
      rw [Preadditive.comp_sub, Hom.comm_assoc, f_α, f_α_assoc, D.φ₁.comm, sub_self])).1

@[reassoc]
lemma g_τ (n : ℕ) : D.K.g.f n ≫ D.τ n =
    D.K.X₂.d n (n + 1) ≫ D.α (n + 1) - D.α n ≫ D.J₁.cocomplex.d n (n + 1) :=
  (CokernelCofork.IsColimit.desc' (D.hK n).gIsCokernel
    (D.K.X₂.d n (n + 1) ≫ D.α (n + 1) - D.α n ≫ D.J₁.cocomplex.d n (n + 1)) (by
      change D.K.f.f n ≫ _ = 0
      rw [Preadditive.comp_sub, Hom.comm_assoc, f_α, f_α_assoc, D.φ₁.comm, sub_self])).2

/-- `τ` as a cochain map `K₃ ⟶ J₁[1]` (negated differentials on the target). -/
def T : D.K.X₃ ⟶ (shiftNeg D.J₁).cocomplex where
  f n := D.τ n
  comm' i j hij := by
    simp only [ComplexShape.up_Rel] at hij
    subst hij
    have := D.epi_g i
    rw [← cancel_epi (D.K.g.f i)]
    change D.K.g.f i ≫ D.τ i ≫ (-D.J₁.cocomplex.d (i + 1) (i + 1 + 1)) =
      D.K.g.f i ≫ D.K.X₃.d i (i + 1) ≫ D.τ (i + 1)
    rw [g_τ_assoc, Hom.comm_assoc, g_τ]
    simp only [Preadditive.comp_neg, Preadditive.sub_comp, Preadditive.comp_sub, Category.assoc,
      HomologicalComplex.d_comp_d, HomologicalComplex.d_comp_d_assoc, comp_zero, zero_comp,
      sub_zero, zero_sub]

lemma f_ε₂_α : D.S.f ≫ e D.ε₂ ≫ D.α 0 = aug D.J₁ := by
  have h₁ : e D.ε₁ ≫ D.K.f.f 0 = D.S.f ≫ e D.ε₂ := by rw [e_comp, D.hε₁₂, single_comp_e]
  rw [← reassoc_of% h₁, f_α, e_comp, D.hφ₁]
  rfl

lemma mono_ε₃ : Mono (e D.ε₃) := by
  have : Mono (e D.ε₃ ≫ D.φ₃.f 0) := by
    rw [e_comp, D.hφ₃]; exact inferInstanceAs (Mono (aug D.J₃))
  exact mono_of_mono _ (D.φ₃.f 0)

/-- The defect in degree `0`: `S.g ≫ v = ε₂ ≫ α⁰ - ext`. -/
def v : D.S.X₃ ⟶ D.J₁.cocomplex.X 0 :=
  (CokernelCofork.IsColimit.desc' D.hS.gIsCokernel (e D.ε₂ ≫ D.α 0 - ext D.hS D.J₁) (by
    rw [Preadditive.comp_sub, f_ε₂_α, f_ext, sub_self])).1

@[reassoc]
lemma g_v : D.S.g ≫ D.v = e D.ε₂ ≫ D.α 0 - ext D.hS D.J₁ :=
  (CokernelCofork.IsColimit.desc' D.hS.gIsCokernel (e D.ε₂ ≫ D.α 0 - ext D.hS D.J₁) (by
    rw [Preadditive.comp_sub, f_ε₂_α, f_ext, sub_self])).2

/-- The degree-`0` correction `K₃⁰ ⟶ J₁⁰`. -/
def k₀ : D.K.X₃.X 0 ⟶ D.J₁.cocomplex.X 0 :=
  haveI := D.mono_ε₃
  Injective.factorThru D.v (e D.ε₃)

@[reassoc]
lemma ε₃_k₀ : e D.ε₃ ≫ D.k₀ = D.v := by
  have := D.mono_ε₃
  exact Injective.comp_factorThru _ _

/-- The correction term, concentrated in degree `0`. -/
def N : D.K.X₃ ⟶ (shiftNeg D.J₁).cocomplex where
  f n := match n with
    | 0 => D.k₀ ≫ D.J₁.cocomplex.d 0 1
    | _ + 1 => 0
  comm' i j hij := by
    simp only [ComplexShape.up_Rel] at hij
    subst hij
    cases i with
    | zero => simp
    | succ i => simp

/-- The homotopy between `φ₃ ≫ h` and `T + N`. -/
def H : Homotopy (D.φ₃ ≫ h D.hS D.J₁ D.J₃) (D.T + D.N) :=
  ResolutionToInjectiveComplex.homotopy D.ε₃ _ _ (by
    have := D.hS.epi_g
    apply HomologicalComplex.from_single_hom_ext
    have h₃ : e D.ε₃ ≫ D.φ₃.f 0 = aug D.J₃ := by rw [e_comp, D.hφ₃]; rfl
    have h₂₃ : e D.ε₂ ≫ D.K.g.f 0 = D.S.g ≫ e D.ε₃ := by
      rw [e_comp, D.hε₂₃, single_comp_e]
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, HomologicalComplex.comp_f,
      HomologicalComplex.add_f_apply]
    change e D.ε₃ ≫ D.φ₃.f 0 ≫ hf D.hS D.J₁ D.J₃ 0 =
      e D.ε₃ ≫ (D.τ 0 + D.k₀ ≫ D.J₁.cocomplex.d 0 1)
    rw [reassoc_of% h₃, ← cancel_epi D.S.g, g_aug_hf, Preadditive.comp_add,
      Preadditive.comp_add, ε₃_k₀_assoc, g_v_assoc, ← reassoc_of% h₂₃, g_τ]
    have hz : e D.ε₂ ≫ D.K.X₂.d 0 (0 + 1) ≫ D.α (0 + 1) = 0 := by
      rw [← Category.assoc, e_d, zero_comp]
    simp only [Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc, hz]
    abel)

/-- The off-diagonal corrections `K₃ⁿ ⟶ J₁ⁿ`. -/
def kk : ∀ n : ℕ, D.K.X₃.X n ⟶ D.J₁.cocomplex.X n
  | 0 => -D.k₀
  | n + 1 => D.H.hom (n + 1) n

lemma kk_rel (n : ℕ) :
    D.kk n ≫ D.J₁.cocomplex.d n (n + 1) + D.φ₃.f n ≫ hf D.hS D.J₁ D.J₃ n =
      D.τ n + D.K.X₃.d n (n + 1) ≫ D.kk (n + 1) := by
  have h₁ := D.H.comm n
  rw [Homotopy.dNext_cochainComplex] at h₁
  change D.φ₃.f n ≫ hf D.hS D.J₁ D.J₃ n = _ at h₁
  cases n with
  | zero =>
    rw [Homotopy.prevD_zero_cochainComplex] at h₁
    change _ = _ + 0 + (D.τ 0 + D.k₀ ≫ D.J₁.cocomplex.d 0 1) at h₁
    change (-D.k₀) ≫ D.J₁.cocomplex.d 0 1 + _ = _ + D.K.X₃.d 0 1 ≫ D.H.hom 1 0
    rw [h₁, Preadditive.neg_comp]
    abel
  | succ n =>
    rw [Homotopy.prevD_succ_cochainComplex] at h₁
    change _ = _ + D.H.hom (n + 1) n ≫ (-D.J₁.cocomplex.d (n + 1) (n + 2)) +
        (D.τ (n + 1) + 0) at h₁
    change D.H.hom (n + 1) n ≫ D.J₁.cocomplex.d (n + 1) (n + 2) + _ =
      _ + D.K.X₃.d (n + 1) (n + 2) ≫ D.H.hom (n + 2) (n + 1)
    rw [h₁, Preadditive.comp_neg]
    abel

/-- The middle component `K₂ ⟶ J₁ ⊞ J₃` of the morphism to the horseshoe. -/
def M : D.K.X₂ ⟶ cocomplex D.hS D.J₁ D.J₃ where
  f n := (biprod.lift (D.α n + D.K.g.f n ≫ D.kk n) (D.K.g.f n ≫ D.φ₃.f n) :
    D.K.X₂.X n ⟶ X D.J₁ D.J₃ n)
  comm' i j hij := by
    simp only [ComplexShape.up_Rel] at hij
    subst hij
    rw [cocomplex_d]
    apply biprod.hom_ext
    · have e1 := D.g_τ i
      have e2 := congrArg (fun t => D.K.g.f i ≫ t) (D.kk_rel i)
      have e3 : D.K.g.f i ≫ D.K.X₃.d i (i + 1) = D.K.X₂.d i (i + 1) ≫ D.K.g.f (i + 1) :=
        D.K.g.comm i (i + 1)
      simp only [Preadditive.comp_add] at e2
      simp only [Horseshoe.d, Category.assoc, biprod.lift_desc_assoc, Preadditive.add_comp,
        biprod.inl_fst, biprod.inr_fst, Category.comp_id, comp_zero, add_zero,
        biprod.lift_fst, Preadditive.comp_add]
      rw [← reassoc_of% e3, add_assoc, e2, e1]
      abel
    · simp only [Horseshoe.d, Category.assoc, biprod.lift_desc_assoc, Preadditive.add_comp,
        biprod.inl_snd, biprod.inr_snd, Category.comp_id, comp_zero, zero_add,
        biprod.lift_snd]
      rw [D.φ₃.comm, ← Category.assoc, ← Category.assoc, D.K.g.comm]

/-- The morphism from the short exact sequence of resolutions to the horseshoe. -/
def Ψ : D.K ⟶ shortComplex D.hS D.J₁ D.J₃ where
  τ₁ := D.φ₁
  τ₂ := D.M
  τ₃ := D.φ₃
  comm₁₂ := by
    ext n : 1
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, inl_f]
    apply biprod.hom_ext
    · simp [M]
    · simp [M]
  comm₂₃ := by
    ext n : 1
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, snd_f]
    simp [M]

variable {E : Type*} [Category* E] [Abelian E] (Γ : C ⥤ E) [Γ.Additive]

/-- The image under `Γ` of `Ψ`. -/
def ΨMap : D.K.map (Γ.mapHomologicalComplex _) ⟶ shortComplexMap D.hS D.J₁ D.J₃ Γ where
  τ₁ := (Γ.mapHomologicalComplex _).map D.φ₁
  τ₂ := (Γ.mapHomologicalComplex _).map D.M
  τ₃ := (Γ.mapHomologicalComplex _).map D.φ₃
  comm₁₂ := ((Γ.mapHomologicalComplex _).map_comp _ _).symm.trans
    ((congrArg (Γ.mapHomologicalComplex _).map D.Ψ.comm₁₂).trans
      ((Γ.mapHomologicalComplex _).map_comp _ _))
  comm₂₃ := ((Γ.mapHomologicalComplex _).map_comp _ _).symm.trans
    ((congrArg (Γ.mapHomologicalComplex _).map D.Ψ.comm₂₃).trans
      ((Γ.mapHomologicalComplex _).map_comp _ _))

/-- **Compatibility of comparison maps with connecting morphisms.** If `Γ` takes the short exact
sequence of resolutions `K` to a short exact sequence of complexes, then the comparison maps
`Hⁿ(Γ K₃) ⟶ RⁿΓ(S.X₃)` and `Hⁿ⁺¹(Γ K₁) ⟶ Rⁿ⁺¹Γ(S.X₁)` commute with the connecting morphisms. -/
theorem δ_comp_comparison [HasInjectiveResolutions C]
    (hKΓ : (D.K.map (Γ.mapHomologicalComplex _)).ShortExact) (n : ℕ) :
    hKΓ.δ n (n + 1) (upRel n) ≫ homologyMap ((Γ.mapHomologicalComplex _).map D.φ₁) (n + 1) ≫
        (D.J₁.isoRightDerivedObj Γ (n + 1)).inv =
      homologyMap ((Γ.mapHomologicalComplex _).map D.φ₃) n ≫
        (D.J₃.isoRightDerivedObj Γ n).inv ≫ Horseshoe.δ Γ D.hS D.J₁ D.J₃ n := by
  have hnat := HomologicalComplex.HomologySequence.δ_naturality (D.ΨMap Γ) hKΓ
    (shortExact_map D.hS D.J₁ D.J₃ Γ) n (n + 1) (upRel n)
  have h3 : homologyMap ((Γ.mapHomologicalComplex _).map D.φ₃) n ≫
      (D.J₃.isoRightDerivedObj Γ n).inv ≫ Horseshoe.δ Γ D.hS D.J₁ D.J₃ n =
      (homologyMap (D.ΨMap Γ).τ₃ n ≫ (shortExact_map D.hS D.J₁ D.J₃ Γ).δ n (n + 1) (upRel n)) ≫
        (D.J₁.isoRightDerivedObj Γ (n + 1)).inv := by
    exact (congrArg (homologyMap ((Γ.mapHomologicalComplex _).map D.φ₃) n ≫ ·)
      (Iso.inv_hom_id_assoc (D.J₃.isoRightDerivedObj Γ n) _)).trans (Category.assoc _ _ _).symm
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hnat).trans h3.symm)

end Data

end ResolutionDelta


namespace AffineCoverComparison

open HomologicalComplex CochainComplex TopologicalSpace Opposite

variable {X : TopCat.{u}} {ι : Type u} [LinearOrder ι] (U : ι → Opens X) (hU : IsOpenCover U)
  {S : ShortComplex (X.Sheaf AddCommGrpCat.{u})}

/-- The sequence of sheafified Čech complexes of a short complex of sheaves. -/
abbrev sheafifiedCechSC (S : ShortComplex (X.Sheaf AddCommGrpCat.{u})) :
    ShortComplex (CochainComplex (X.Sheaf AddCommGrpCat.{u}) ℕ) :=
  ShortComplex.mk (SheafifiedCech.sheafifiedCechComplexMap U S.f)
    (SheafifiedCech.sheafifiedCechComplexMap U S.g) (by
      ext p : 1
      apply Sheaf.hom_ext
      ext V s
      funext a
      change S.g.hom.app _ (S.f.hom.app _ (s a)) = 0
      rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app]
      exact (ConcreteCategory.congr_hom (congrArg (fun φ => φ.hom.app _) S.zero) (s a)).trans rfl)

/-- The sequence of ordered Čech complexes of a short complex of sheaves. -/
abbrev cechSC (S : ShortComplex (X.Sheaf AddCommGrpCat.{u})) :
    ShortComplex (CochainComplex AddCommGrpCat.{u} ℕ) :=
  ShortComplex.mk (orderedCechComplexMap U S.f) (orderedCechComplexMap U S.g) (by
      ext p : 1
      ext s
      funext a
      change S.g.hom.app _ (S.f.hom.app _ (s a)) = 0
      rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app]
      exact (ConcreteCategory.congr_hom (congrArg (fun φ => φ.hom.app _) S.zero) (s a)).trans rfl)

/-- The data of `ResolutionDelta` for the sheafified Čech resolutions of a short exact sequence
of sheaves whose sheafified Čech complexes form a degreewise short exact sequence. -/
def cechData (hS : S.ShortExact)
    (hK : ∀ n, ((sheafifiedCechSC U S).map
      (HomologicalComplex.eval _ (ComplexShape.up ℕ) n)).ShortExact) :
    ResolutionDelta.Data (X.Sheaf AddCommGrpCat.{u}) where
  S := S
  hS := hS
  K := sheafifiedCechSC U S
  hK := hK
  ε₁ := SheafifiedCech.augmentationHom U S.X₁
  ε₂ := SheafifiedCech.augmentationHom U S.X₂
  ε₃ := SheafifiedCech.augmentationHom U S.X₃
  quasiIso₃ := SheafifiedCech.quasiIso_augmentationHom U hU S.X₃
  hε₁₂ := ((SheafifiedCech.augmentationNatTrans U).naturality S.f).symm
  hε₂₃ := ((SheafifiedCech.augmentationNatTrans U).naturality S.g).symm
  J₁ := injectiveResolution S.X₁
  J₃ := injectiveResolution S.X₃
  φ₁ := CechDerivedComparison.comparisonHom U hU S.X₁
  φ₃ := CechDerivedComparison.comparisonHom U hU S.X₃
  hφ₁ := CechDerivedComparison.augmentationHom_comp_comparisonHom U hU S.X₁
  hφ₃ := CechDerivedComparison.augmentationHom_comp_comparisonHom U hU S.X₃

/-- Global sections identify the image of the sheafified Čech sequence with the ordered Čech
sequence. -/
def globalSectionsSCIso :
    (sheafifiedCechSC U S).map ((sheafSectionsOver (X := X) ⊤).mapHomologicalComplex _) ≅
      cechSC U S := by
  refine ShortComplex.isoMk (CechDerivedComparison.globalSectionsIso U S.X₁)
    (CechDerivedComparison.globalSectionsIso U S.X₂)
    (CechDerivedComparison.globalSectionsIso U S.X₃) ?_ ?_
  · exact ((SheafifiedCech.globalSectionsNatIso U).hom.naturality S.f).symm
  · exact ((SheafifiedCech.globalSectionsNatIso U).hom.naturality S.g).symm

/-- **The comparison maps commute with connecting morphisms.** For a short exact sequence of
abelian sheaves whose sheafified Čech complexes and ordered Čech complexes form short exact
sequences, the comparison maps `Ȟ^p(U, -) ⟶ H^p(X, -)` of Hartshorne III, Lemma 4.4, commute
with the connecting morphisms of the two long exact sequences. -/
theorem cechδ_comp_cechToSheafCohomology (hS : S.ShortExact)
    (hK : ∀ n, ((sheafifiedCechSC U S).map
      (HomologicalComplex.eval _ (ComplexShape.up ℕ) n)).ShortExact)
    (hC : (cechSC U S).ShortExact) (n : ℕ) :
    hC.δ n (n + 1) (RightDerivedLES.upRel n) ≫ (cechToSheafCohomology U hU (n + 1)).app S.X₁ =
      (cechToSheafCohomology U hU n).app S.X₃ ≫
        rightDerivedδ (sheafSectionsOver (X := X) ⊤) hS n := by
  have hKΓ : ((sheafifiedCechSC U S).map
      ((sheafSectionsOver (X := X) ⊤).mapHomologicalComplex _)).ShortExact :=
    ShortComplex.shortExact_of_iso (globalSectionsSCIso U (S := S)).symm hC
  have hnat : hC.δ n (n + 1) (RightDerivedLES.upRel n) ≫
      homologyMap (CechDerivedComparison.globalSectionsIso U S.X₁).inv (n + 1) =
        homologyMap (CechDerivedComparison.globalSectionsIso U S.X₃).inv n ≫
          hKΓ.δ n (n + 1) (RightDerivedLES.upRel n) :=
    HomologicalComplex.HomologySequence.δ_naturality (globalSectionsSCIso U (S := S)).inv hC hKΓ
      n (n + 1) (RightDerivedLES.upRel n)
  have key := (cechData U hU hS hK).δ_comp_comparison (sheafSectionsOver (X := X) ⊤) hKΓ n
  change hC.δ n (n + 1) (RightDerivedLES.upRel n) ≫
      homologyMap ((CechDerivedComparison.globalSectionsIso U S.X₁).inv ≫
        ((sheafSectionsOver (X := X) ⊤).mapHomologicalComplex _).map
          (CechDerivedComparison.comparisonHom U hU S.X₁)) (n + 1) ≫
        ((injectiveResolution S.X₁).isoRightDerivedObj (sheafSectionsOver (X := X) ⊤) (n + 1)).inv =
    homologyMap ((CechDerivedComparison.globalSectionsIso U S.X₃).inv ≫
      ((sheafSectionsOver (X := X) ⊤).mapHomologicalComplex _).map
        (CechDerivedComparison.comparisonHom U hU S.X₃)) n ≫
      ((injectiveResolution S.X₃).isoRightDerivedObj (sheafSectionsOver (X := X) ⊤) n).inv ≫
        rightDerivedδ (sheafSectionsOver (X := X) ⊤) hS n
  rw [homologyMap_comp, homologyMap_comp]
  exact (congrArg (hC.δ n (n + 1) (RightDerivedLES.upRel n) ≫ ·) (Category.assoc _ _ _)).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hnat).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (homologyMap (CechDerivedComparison.globalSectionsIso U S.X₃).inv n ≫ ·)
          key).trans (Category.assoc _ _ _).symm))))

end AffineCoverComparison

namespace AffineCoverComparison

open TopologicalSpace Opposite AlgebraicGeometry

variable {X : Scheme.{u}} {S : ShortComplex X.Modules} (hS : S.ShortExact)

include hS in
/-- Over an affine open `V`, the sections of a short exact sequence of `𝒪_X`-modules with
quasi-coherent first term are surjective in the last term (Hartshorne II.5.6 applied to `V`). -/
theorem sections_surjective [S.X₁.IsQuasicoherent] {V : X.Opens} (hV : IsAffineOpen V)
    (t : Γ(S.X₃, V)) : ∃ s : Γ(S.X₂, V), S.g.app V s = t := by
  have : IsAffine V := hV
  let T := S.map (Scheme.Modules.restrictFunctor V.ι)
  have hT : T.ShortExact := hS.map_of_exact _
  have : T.X₁.IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor V.ι S.X₁
  have hepi := (affine_globalSections_shortExact T hT).epi_g
  rw [ModuleCat.epi_iff_surjective] at hepi
  have htop : V.ι ''ᵁ ⊤ = V := V.ι_image_top
  obtain ⟨s₀, hs₀⟩ := hepi (S.X₃.presheaf.map (eqToHom htop).op t)
  let s : Γ(S.X₂, V.ι ''ᵁ ⊤) := s₀
  have hs : S.g.app (V.ι ''ᵁ ⊤) s = S.X₃.presheaf.map (eqToHom htop).op t := hs₀
  refine ⟨S.X₂.presheaf.map (eqToHom htop.symm).op s, ?_⟩
  have h := ConcreteCategory.congr_hom (S.g.mapPresheaf.naturality (eqToHom htop.symm).op) s
  simp only [Scheme.Modules.mapPresheaf_app] at h
  refine h.trans ?_
  rw [ConcreteCategory.comp_apply, hs, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← op_comp, eqToHom_trans, eqToHom_refl, op_id, CategoryTheory.Functor.map_id]
  rfl


/-- A short complex of `𝒪_X`-modules, as a short complex in `SheafOfModules`. -/
abbrev toSOM (S : ShortComplex X.Modules) : ShortComplex (SheafOfModules.{u} X.ringCatSheaf) :=
  S

/-- The underlying short complex of abelian sheaves. -/
abbrev Sab (S : ShortComplex X.Modules) : ShortComplex (X.toTopCat.Sheaf AddCommGrpCat.{u}) :=
  (toSOM S).map (ModuleCohomology.toTopSheaf X.ringCatSheaf)

variable {ι : Type u} [LinearOrder ι]

/-- The sequence of ordered Čech cochains of a short complex of sheaves, for any family of
opens. -/
abbrev cochainsSC (W : ι → X.Opens) (p : ℕ) : ShortComplex AddCommGrpCat.{u} :=
  ShortComplex.mk (orderedCechCochainsMap W (Sab S).f p) (orderedCechCochainsMap W (Sab S).g p)
    (by
      ext s
      funext a
      change (Sab S).g.hom.app _ ((Sab S).f.hom.app _ (s a)) = 0
      rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app]
      exact (ConcreteCategory.congr_hom (congrArg (fun φ => φ.hom.app _) (Sab S).zero)
        (s a)).trans rfl)

include hS in
theorem cochainsSC_mono (W : ι → X.Opens) (p : ℕ) : Mono (cochainsSC (S := S) W p).f := by
  have : Mono S.f := hS.mono_f
  rw [AddCommGrpCat.mono_iff_injective]
  intro x y hxy
  funext a
  exact modules_app_injective S.f (orderedCechIntersection W a) (congr_fun hxy a)

include hS in
theorem cochainsSC_exact (W : ι → X.Opens) (p : ℕ) : (cochainsSC (S := S) W p).Exact := by
  have : Mono S.f := hS.mono_f
  rw [ShortComplex.ab_exact_iff]
  intro x hx
  choose y hy using fun a => modules_sections_exact hS.exact
    (U := orderedCechIntersection W a) (x a) (congr_fun hx a)
  exact ⟨y, funext hy⟩

include hS in
theorem cochainsSC_shortExact [S.X₁.IsQuasicoherent] (W : ι → X.Opens) (p : ℕ)
    (hW : ∀ a : OrderedCechIndex ι p, IsAffineOpen (orderedCechIntersection W a)) :
    (cochainsSC (S := S) W p).ShortExact where
  exact := cochainsSC_exact hS W p
  mono_f := cochainsSC_mono hS W p
  epi_g := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro t
    choose s hs using fun a => sections_surjective hS (hW a)
      (show Γ(S.X₃, orderedCechIntersection W a) from t a)
    exact ⟨s, funext hs⟩

theorem isAffineOpen_orderedCechIntersection [X.IsSeparated] {U : ι → X.Opens}
    (hU : ∀ i, IsAffineOpen (U i)) {p : ℕ} (a : OrderedCechIndex ι p) :
    IsAffineOpen (orderedCechIntersection U a) :=
  IsAffineOpen.iInf fun j => hU (a.1 j)

include hS in
/-- On a separated scheme with an affine open cover `U`, the sheafified Čech complexes of a short
exact sequence of `𝒪_X`-modules with quasi-coherent first term form a degreewise short exact
sequence of abelian sheaves. -/
theorem sheafifiedCech_shortExact [X.IsSeparated] [S.X₁.IsQuasicoherent] {U : ι → X.Opens}
    (hU : ∀ i, IsAffineOpen (U i)) (p : ℕ) :
    ((sheafifiedCechSC (X := X.toTopCat) U (Sab S)).map
      (HomologicalComplex.eval _ (ComplexShape.up ℕ) p)).ShortExact where
  exact := by
    refine SheafifiedCech.shortComplex_exact_of_local _ fun x => ⟨⊤, trivial, fun V _ b hb => ?_⟩
    exact (ShortComplex.ab_exact_iff _).1 (cochainsSC_exact hS (fun i => V ⊓ U i) p) b hb
  mono_f := by
    have : ∀ V : (Opens X.toTopCat)ᵒᵖ,
        Mono ((SheafifiedCech.cochainSheafMap U (Sab S).f p).hom.app V) :=
      fun V => cochainsSC_mono hS (fun i => V.unop ⊓ U i) p
    have := NatTrans.mono_of_mono_app (SheafifiedCech.cochainSheafMap U (Sab S).f p).hom
    exact Sheaf.Hom.mono_of_presheaf_mono _ _ (SheafifiedCech.cochainSheafMap U (Sab S).f p)
  epi_g := by
    refine (TopCat.Sheaf.isLocallySurjective_iff_epi _).1
      ((TopCat.Presheaf.isLocallySurjective_iff _).2 fun V t x hx => ?_)
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hx V.isOpen
    have hWV' : W ≤ V := hWV
    have hsurj := (AddCommGrpCat.epi_iff_surjective _).1
      (cochainsSC_shortExact hS (fun i => W ⊓ U i) p
        (isAffineOpen_orderedCechIntersection (fun i => hW.inf (hU i)))).epi_g
    obtain ⟨s, hs⟩ := hsurj (TopCat.Presheaf.restrict t (homOfLE hWV'))
    exact ⟨W, hWV', ⟨s, hs⟩, hxW⟩

/-- A map between cokernels: given a complex `A₂ ⟶ A₃ ⟶ A₄ ⟶ 0` with `A₃ ⟶ A₄` surjective and
an exact row `B₂ ⟶ B₃ ⟶ B₄ ⟶ 0` of abelian groups and a commutative ladder whose first map is
surjective and whose second map is an isomorphism, the third map is an isomorphism. -/
theorem isIso_of_cokernel_ladder {A₂ A₃ A₄ B₂ B₃ B₄ : AddCommGrpCat.{u}}
    {u₁ : A₂ ⟶ A₃} {d₁ : A₃ ⟶ A₄} {u₂ : B₂ ⟶ B₃} {d₂ : B₃ ⟶ B₄}
    (w₁ : u₁ ≫ d₁ = 0) (w₂ : u₂ ≫ d₂ = 0) (h₂ : (ShortComplex.mk u₂ d₂ w₂).Exact)
    [hd₁ : Epi d₁] [hd₂ : Epi d₂] (a₂ : A₂ ⟶ B₂) (a₃ : A₃ ⟶ B₃) (a₄ : A₄ ⟶ B₄)
    [ha₂ : Epi a₂] [ha₃ : IsIso a₃]
    (c₁ : u₁ ≫ a₃ = a₂ ≫ u₂) (c₂ : d₁ ≫ a₄ = a₃ ≫ d₂) : IsIso a₄ := by
  have hepi : Epi a₄ := by
    have : Epi (d₁ ≫ a₄) := by rw [c₂]; infer_instance
    exact epi_of_epi d₁ a₄
  have hmono : Mono a₄ := by
    rw [AddCommGrpCat.mono_iff_injective, injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (AddCommGrpCat.epi_iff_surjective d₁).1 inferInstance x
    have hy : d₂ (a₃ y) = 0 := by
      rw [← ConcreteCategory.comp_apply, ← c₂, ConcreteCategory.comp_apply, hx]
    obtain ⟨z, hz⟩ := (ShortComplex.ab_exact_iff _).1 h₂ (a₃ y) hy
    obtain ⟨w, rfl⟩ := (AddCommGrpCat.epi_iff_surjective a₂).1 inferInstance z
    have hw : u₁ w = y := by
      apply (AddCommGrpCat.mono_iff_injective a₃).1 inferInstance
      rw [← ConcreteCategory.comp_apply, c₁, ConcreteCategory.comp_apply]
      exact hz
    rw [← hw, ← ConcreteCategory.comp_apply, w₁]
    rfl
  exact isIso_of_mono_of_epi a₄

/-- The short exact sequence `0 ⟶ F ⟶ G ⟶ G/F ⟶ 0` attached to a monomorphism. -/
noncomputable abbrev monoSC {F G : X.Modules} (ι : F ⟶ G) : ShortComplex X.Modules :=
  ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)

theorem monoSC_shortExact {F G : X.Modules} (ι : F ⟶ G) [Mono ι] : (monoSC ι).ShortExact :=
  ShortComplex.ShortExact.mk' ((monoSC ι).exact_of_g_is_cokernel (cokernelIsCokernel _))
    inferInstance inferInstance

end AffineCoverComparison

open AffineCoverComparison AlgebraicGeometry TopologicalSpace in
/-- **Hartshorne III, Theorem 4.5.** Let `X` be a Noetherian separated scheme, let `U` be an open
affine cover of `X` (with a linear order on its index set, used to form ordered Čech cochains), and
let `F` be a quasi-coherent `𝒪_X`-module. Then for every `p` the natural comparison map
`Ȟ^p(U, F) ⟶ H^p(X, F)` of Lemma III.4.4 is an isomorphism; here both sides are formed from the
underlying abelian sheaf of `F`. -/
theorem isIso_cechToSheafCohomology_of_isQuasicoherent {X : Scheme.{u}} [IsNoetherian X]
    [X.IsSeparated] {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUa : ∀ i, IsAffineOpen (U i)) (p : ℕ) (F : X.Modules) [F.IsQuasicoherent] :
    IsIso ((cechToSheafCohomology U hU p).app ((SheafOfModules.toSheaf X.ringCatSheaf).obj F)) := by
  induction p generalizing F with
  | zero => exact NatIso.isIso_app_of_isIso (cechToSheafCohomology U hU 0) _
  | succ p ih =>
    obtain ⟨G, ι, hι, hG, hGq⟩ := exists_mono_isFlasque_isQuasicoherent F
    let S := monoSC ι
    have hS : S.ShortExact := monoSC_shortExact ι
    have : S.X₁.IsQuasicoherent := ‹F.IsQuasicoherent›
    have : S.X₂.IsQuasicoherent := hGq
    have : S.X₃.IsQuasicoherent := isQuasicoherent_cokernel ι
    let T := Sab S
    have hS' : (toSOM S).ShortExact := hS
    have hT : T.ShortExact := hS'.map_of_exact _
    have : T.X₂.IsFlasque := hG
    have hK := sheafifiedCech_shortExact hS hUa
    have hC : (cechSC U T).ShortExact :=
      HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n =>
        cochainsSC_shortExact hS U n fun a => isAffineOpen_orderedCechIntersection hUa a
    have hδ := cechδ_comp_cechToSheafCohomology U hU hT hK hC p
    have hC2 : IsZero ((cechSC U T).X₂.homology (p + 1)) :=
      orderedCechCohomology_isZero_of_isFlasque U hU T.X₂ (p + 1) (Nat.succ_pos p)
    have hH2 : IsZero ((sheafCohomology X.toTopCat (p + 1)).obj T.X₂) :=
      sheafCohomology_isZero_of_isFlasque T.X₂ p
    have hepi₁ : Epi (hC.δ p (p + 1) (RightDerivedLES.upRel p)) :=
      (hC.homology_exact₁ p (p + 1) (RightDerivedLES.upRel p)).epi_f (hC2.eq_of_tgt _ _)
    have hepi₂ : Epi (rightDerivedδ (sheafSectionsOver (X := X.toTopCat) ⊤) hT p) :=
      (rightDerived_exact₁ _ hT p).epi_f (hH2.eq_of_tgt _ _)
    have h₂ := ih S.X₂
    have h₃ := ih S.X₃
    exact isIso_of_cokernel_ladder (hd₁ := hepi₁) (hd₂ := hepi₂)
      (ha₂ := @IsIso.epi_of_iso _ _ _ _ _ h₂)
      (ha₃ := h₃) (hC.comp_δ p (p + 1) (RightDerivedLES.upRel p)) _ (rightDerived_exact₃ _ hT p)
      ((cechToSheafCohomology U hU p).app T.X₂) ((cechToSheafCohomology U hU p).app T.X₃)
      ((cechToSheafCohomology U hU (p + 1)).app T.X₁)
      ((cechToSheafCohomology U hU p).naturality T.g) hδ

open AlgebraicGeometry TopologicalSpace in
/-- **Hartshorne III, Theorem 4.5**, as an isomorphism: for a Noetherian separated scheme `X`, an
open affine cover `U` and a quasi-coherent `𝒪_X`-module `F`, the comparison map gives
`Ȟ^p(U, F) ≅ H^p(X, F)`. -/
def cechCohomologyIsoOfIsQuasicoherent {X : Scheme.{u}} [IsNoetherian X] [X.IsSeparated]
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUa : ∀ i, IsAffineOpen (U i)) (p : ℕ) (F : X.Modules) [F.IsQuasicoherent] :
    (orderedCechCohomologyFunctor U p).obj ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) ≅
      (sheafCohomology X.toTopCat p).obj ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) :=
  haveI := isIso_cechToSheafCohomology_of_isQuasicoherent U hU hUa p F
  asIso ((cechToSheafCohomology U hU p).app ((SheafOfModules.toSheaf X.ringCatSheaf).obj F))

end Hartshorne

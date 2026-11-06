/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# The long exact sequence of right derived functors

Let `F : C ⥤ D` be an additive functor between abelian categories, where `C` has injective
resolutions. For a short exact sequence `S : 0 ⟶ A' ⟶ A ⟶ A'' ⟶ 0` in `C` we construct
connecting morphisms `RⁿF(A'') ⟶ Rⁿ⁺¹F(A')` (`Hartshorne.rightDerivedδ`) and prove that

`0 ⟶ R⁰F(A') ⟶ R⁰F(A) ⟶ R⁰F(A'') ⟶ R¹F(A') ⟶ ⋯ ⟶ RⁿF(A') ⟶ RⁿF(A) ⟶ RⁿF(A'') ⟶ Rⁿ⁺¹F(A') ⟶ ⋯`

is exact (`Hartshorne.rightDerived_mono_map_f`, `Hartshorne.rightDerived_exact₂`,
`Hartshorne.rightDerived_exact₃`, `Hartshorne.rightDerived_exact₁`), and that the connecting
morphisms are natural in morphisms of short exact sequences
(`Hartshorne.rightDerivedδ_naturality`). Left exactness of `F` is not needed for these
statements; it only enters in the identification `R⁰F ≅ F`.

## Construction

Given injective resolutions `I₁` of `A'` and `I₃` of `A''`, the horseshoe lemma produces an
injective resolution of `A` with terms `I₁ⁿ ⊞ I₃ⁿ`; its differential is twisted by a cochain
map `I₃ ⟶ I₁[1]`, obtained by lifting the map `A'' ⟶ coker(A' ⟶ I₁⁰)` to injective resolutions
(the shifted complex `I₁¹ ⟶ I₁² ⟶ ⋯`, with negated differentials, resolves this cokernel).
Applying `F` degreewise gives a degreewise split, hence short exact, sequence of cochain
complexes, and the connecting morphisms are those of its homology long exact sequence.
For a morphism of short exact sequences, the off-diagonal part of a morphism between the
horseshoe resolutions is obtained from a homotopy between two lifts, which yields a morphism
of short exact sequences of complexes and hence naturality of the connecting morphisms.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Hartshorne

universe v u

namespace RightDerivedLES

open HomologicalComplex CochainComplex

section Resolutions

variable {C : Type u} [Category.{v} C] [Abelian C]

set_option backward.isDefEq.respectTransparency false in
/-- A criterion for an augmentation `X ⟶ K⁰` to be a quasi-isomorphism. -/
lemma quasiIso_fromSingle₀ {K : CochainComplex C ℕ} {X : C} (φ : X ⟶ K.X 0)
    (hφ : φ ≫ K.d 0 1 = 0) (h₀ : (ShortComplex.mk _ _ hφ).Exact) [Mono φ]
    (h : ∀ n : ℕ, K.ExactAt (n + 1)) :
    QuasiIso ((CochainComplex.fromSingle₀Equiv K X).symm ⟨φ, hφ⟩) := by
  rw [quasiIso_iff]
  intro n
  cases n with
  | zero =>
    rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
    · refine ⟨?_, ?_⟩
      · refine (ShortComplex.exact_iff_of_iso ?_).1 h₀
        exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      · change Mono (((K.fromSingle₀Equiv X).symm ⟨φ, hφ⟩).f 0)
        rw [fromSingle₀Equiv_symm_apply_f_zero]
        infer_instance
    all_goals simp
  | succ n =>
    rw [quasiIsoAt_iff_exactAt]
    · exact h n
    · exact CochainComplex.exactAt_succ_single_obj _ _

/-- The augmentation `X ⟶ I⁰` of an injective resolution, with its source written as `X`. -/
def aug {X : C} (I : InjectiveResolution X) : X ⟶ I.cocomplex.X 0 :=
  ((CochainComplex.fromSingle₀Equiv _ _) I.ι).1

lemma aug_eq {X : C} (I : InjectiveResolution X) : aug I = I.ι.f 0 := rfl

@[reassoc (attr := simp)]
lemma aug_d {X : C} (I : InjectiveResolution X) : aug I ≫ I.cocomplex.d 0 1 = 0 :=
  ((CochainComplex.fromSingle₀Equiv _ _) I.ι).2

lemma exact_aug {X : C} (I : InjectiveResolution X) :
    (ShortComplex.mk _ _ (aug_d I)).Exact := I.exact₀

instance {X : C} (I : InjectiveResolution X) : Mono (aug I) :=
  inferInstanceAs (Mono (I.ι.f 0))

/-- The complex `I¹ ⟶ I² ⟶ ⋯` with negated differentials. -/
abbrev shiftNegCocomplex {X : C} (I : InjectiveResolution X) : CochainComplex C ℕ where
  X n := I.cocomplex.X (n + 1)
  d i j := -I.cocomplex.d (i + 1) (j + 1)
  shape i j hij := by
    rw [I.cocomplex.shape, neg_zero]
    simp only [ComplexShape.up_Rel] at hij ⊢
    omega
  d_comp_d' i j k _ _ := by simp

/-- The map `coker(X ⟶ I⁰) ⟶ I¹` induced by the differential. -/
def shiftNegAug {X : C} (I : InjectiveResolution X) : cokernel (aug I) ⟶ I.cocomplex.X 1 :=
  cokernel.desc _ (I.cocomplex.d 0 1) (aug_d I)

@[reassoc (attr := simp)]
lemma π_shiftNegAug {X : C} (I : InjectiveResolution X) :
    cokernel.π (aug I) ≫ shiftNegAug I = I.cocomplex.d 0 1 := by
  simp [shiftNegAug]

lemma shiftNegAug_comp_d {X : C} (I : InjectiveResolution X) :
    shiftNegAug I ≫ (shiftNegCocomplex I).d 0 1 = 0 := by
  rw [← cancel_epi (cokernel.π (aug I))]
  simp

instance {X : C} (I : InjectiveResolution X) : Mono (shiftNegAug I) :=
  (exact_aug I).mono_cokernelDesc

set_option backward.isDefEq.respectTransparency false in
/-- The negated shift `I¹ ⟶ I² ⟶ ⋯` of an injective resolution of `X` is an injective
resolution of the cokernel of `X ⟶ I⁰`. -/
abbrev shiftNeg {X : C} (I : InjectiveResolution X) : InjectiveResolution (cokernel (aug I)) where
  cocomplex := shiftNegCocomplex I
  injective n := by dsimp; infer_instance
  ι := (CochainComplex.fromSingle₀Equiv _ _).symm ⟨shiftNegAug I, shiftNegAug_comp_d I⟩
  quasiIso := by
    apply quasiIso_fromSingle₀
    · refine (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
        (S₁ := ShortComplex.mk _ _ (I.cocomplex.d_comp_d 0 1 2))
        { τ₁ := cokernel.π (aug I)
          τ₂ := 𝟙 (I.cocomplex.X 1)
          τ₃ := -𝟙 (I.cocomplex.X 2)
          comm₁₂ := by simp
          comm₂₃ := by simp }).1 (I.exact_succ 0)
    · intro n
      have : IsIso (-𝟙 (I.cocomplex.X (n + 2))) := ⟨⟨-𝟙 _, by simp, by simp⟩⟩
      rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)]
      refine (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
        (S₁ := ShortComplex.mk _ _ (I.cocomplex.d_comp_d (n + 1) (n + 2) (n + 3)))
        { τ₁ := 𝟙 (I.cocomplex.X (n + 1))
          τ₂ := -𝟙 (I.cocomplex.X (n + 2))
          τ₃ := 𝟙 (I.cocomplex.X (n + 3))
          comm₁₂ := by simp
          comm₂₃ := by simp }).1 (I.exact_succ (n + 1))

lemma aug_shiftNeg {X : C} (I : InjectiveResolution X) :
    aug (shiftNeg I) = shiftNegAug I :=
  congrArg Subtype.val (Equiv.apply_symm_apply _ _)

namespace Horseshoe

variable {S : ShortComplex C} (hS : S.ShortExact)
  (I₁ : InjectiveResolution S.X₁) (I₃ : InjectiveResolution S.X₃)

/-- An extension `S.X₂ ⟶ I₁⁰` of the augmentation of `I₁` along `S.f`. -/
def ext : S.X₂ ⟶ I₁.cocomplex.X 0 :=
  haveI := hS.mono_f
  Injective.factorThru (aug I₁) S.f

@[reassoc (attr := simp)]
lemma f_ext : S.f ≫ ext hS I₁ = aug I₁ := by
  have := hS.mono_f
  exact Injective.comp_factorThru _ _

/-- The map `S.X₃ ⟶ coker(S.X₁ ⟶ I₁⁰)` induced by `ext`. -/
def u : S.X₃ ⟶ cokernel (aug I₁) :=
  (CokernelCofork.IsColimit.desc' hS.gIsCokernel (ext hS I₁ ≫ cokernel.π (aug I₁))
    (by rw [f_ext_assoc, cokernel.condition])).1

@[reassoc (attr := simp)]
lemma g_u : S.g ≫ u hS I₁ = ext hS I₁ ≫ cokernel.π (aug I₁) :=
  (CokernelCofork.IsColimit.desc' hS.gIsCokernel (ext hS I₁ ≫ cokernel.π (aug I₁))
    (by rw [f_ext_assoc, cokernel.condition])).2

/-- The twisting cochain map `I₃ ⟶ I₁[1]` (with negated differentials on the target). -/
def h : I₃.cocomplex ⟶ (shiftNeg I₁).cocomplex :=
  InjectiveResolution.desc (-u hS I₁) (shiftNeg I₁) I₃

/-- The degree `n` component of `h`, as a map `I₃ⁿ ⟶ I₁ⁿ⁺¹`. -/
def hf (n : ℕ) : I₃.cocomplex.X n ⟶ I₁.cocomplex.X (n + 1) := (h hS I₁ I₃).f n

@[reassoc]
lemma hf_comm (n : ℕ) :
    hf hS I₁ I₃ n ≫ I₁.cocomplex.d (n + 1) (n + 2) +
      I₃.cocomplex.d n (n + 1) ≫ hf hS I₁ I₃ (n + 1) = 0 := by
  have h₁ : hf hS I₁ I₃ n ≫ (-I₁.cocomplex.d (n + 1) (n + 2)) =
      I₃.cocomplex.d n (n + 1) ≫ hf hS I₁ I₃ (n + 1) := by
    exact (h hS I₁ I₃).comm n (n + 1)
  rw [← h₁, Preadditive.comp_neg, add_neg_cancel]

@[reassoc]
lemma hf_comm' (n : ℕ) {Z : C} (z : I₁.cocomplex.X (n + 2) ⟶ Z) :
    hf hS I₁ I₃ n ≫ I₁.cocomplex.d (n + 1) (n + 2) ≫ z +
      I₃.cocomplex.d n (n + 1) ≫ hf hS I₁ I₃ (n + 1) ≫ z = 0 := by
  rw [← Category.assoc, ← Category.assoc, ← Preadditive.add_comp, hf_comm, zero_comp]

@[reassoc]
lemma aug_hf : aug I₃ ≫ hf hS I₁ I₃ 0 = -(u hS I₁ ≫ shiftNegAug I₁) := by
  have h₁ : aug I₃ ≫ hf hS I₁ I₃ 0 = (-u hS I₁) ≫ aug (shiftNeg I₁) :=
    InjectiveResolution.desc_commutes_zero (-u hS I₁) (shiftNeg I₁) I₃
  rw [h₁, aug_shiftNeg, Preadditive.neg_comp]

@[reassoc]
lemma g_aug_hf : S.g ≫ aug I₃ ≫ hf hS I₁ I₃ 0 = -(ext hS I₁ ≫ I₁.cocomplex.d 0 1) := by
  rw [aug_hf, Preadditive.comp_neg, g_u_assoc, π_shiftNegAug]

/-- The objects `I₁ⁿ ⊞ I₃ⁿ` of the horseshoe complex. -/
abbrev X (n : ℕ) : C := I₁.cocomplex.X n ⊞ I₃.cocomplex.X n

/-- The differential of the horseshoe complex. -/
def d (n : ℕ) : X I₁ I₃ n ⟶ X I₁ I₃ (n + 1) :=
  biprod.desc (I₁.cocomplex.d n (n + 1) ≫ biprod.inl)
    (hf hS I₁ I₃ n ≫ biprod.inl + I₃.cocomplex.d n (n + 1) ≫ biprod.inr)

@[reassoc (attr := simp)]
lemma inl_d (n : ℕ) : biprod.inl ≫ d hS I₁ I₃ n = I₁.cocomplex.d n (n + 1) ≫ biprod.inl := by
  simp [d]

@[reassoc (attr := simp)]
lemma inr_d (n : ℕ) : biprod.inr ≫ d hS I₁ I₃ n =
    hf hS I₁ I₃ n ≫ biprod.inl + I₃.cocomplex.d n (n + 1) ≫ biprod.inr := by
  simp [d]

@[reassoc (attr := simp)]
lemma d_snd (n : ℕ) : d hS I₁ I₃ n ≫ biprod.snd = biprod.snd ≫ I₃.cocomplex.d n (n + 1) := by
  apply biprod.hom_ext' <;> simp

lemma d_comp_d (n : ℕ) : d hS I₁ I₃ n ≫ d hS I₁ I₃ (n + 1) = 0 := by
  apply biprod.hom_ext'
  · simp
  · simp only [inr_d_assoc, Preadditive.add_comp, Category.assoc, inl_d,
      inr_d, Preadditive.comp_add, HomologicalComplex.d_comp_d_assoc, zero_comp, add_zero,
      comp_zero]
    exact hf_comm' hS I₁ I₃ n _

/-- The horseshoe complex `I₁ⁿ ⊞ I₃ⁿ`. -/
abbrev cocomplex : CochainComplex C ℕ :=
  CochainComplex.of (X I₁ I₃) (d hS I₁ I₃) (d_comp_d hS I₁ I₃)

lemma cocomplex_d (n : ℕ) : (cocomplex hS I₁ I₃).d n (n + 1) = d hS I₁ I₃ n := by
  simp

/-- The augmentation `S.X₂ ⟶ I₁⁰ ⊞ I₃⁰`. -/
def ι₀ : S.X₂ ⟶ X I₁ I₃ 0 := biprod.lift (ext hS I₁) (S.g ≫ aug I₃)

@[reassoc (attr := simp)]
lemma f_ι₀ : S.f ≫ ι₀ hS I₁ I₃ = aug I₁ ≫ biprod.inl := by
  apply biprod.hom_ext <;> simp [ι₀]

@[reassoc (attr := simp)]
lemma ι₀_fst : ι₀ hS I₁ I₃ ≫ biprod.fst = ext hS I₁ := by
  simp [ι₀]

@[reassoc (attr := simp)]
lemma ι₀_snd : ι₀ hS I₁ I₃ ≫ biprod.snd = S.g ≫ aug I₃ := by
  simp [ι₀]

lemma ι₀_d : ι₀ hS I₁ I₃ ≫ (cocomplex hS I₁ I₃).d 0 1 = 0 := by
  rw [cocomplex_d]
  apply biprod.hom_ext
  · simp [ι₀, d, g_aug_hf_assoc]
  · simp [ι₀, d]

/-- The inclusion `I₁ ⟶ I₁ ⊞ I₃` of complexes. -/
def inl : I₁.cocomplex ⟶ cocomplex hS I₁ I₃ :=
  CochainComplex.ofHom (fun n => (biprod.inl : _ ⟶ X I₁ I₃ n)) (fun _ => by simp)

/-- The projection `I₁ ⊞ I₃ ⟶ I₃` of complexes. -/
def snd : cocomplex hS I₁ I₃ ⟶ I₃.cocomplex :=
  CochainComplex.ofHom (fun n => (biprod.snd : X I₁ I₃ n ⟶ _)) (fun _ => by simp)

@[simp] lemma inl_f (n : ℕ) : (inl hS I₁ I₃).f n = biprod.inl := rfl

@[simp] lemma snd_f (n : ℕ) : (snd hS I₁ I₃).f n = biprod.snd := rfl

/-- The degreewise split short exact sequence of complexes `0 ⟶ I₁ ⟶ I₁ ⊞ I₃ ⟶ I₃ ⟶ 0`. -/
abbrev shortComplex : ShortComplex (CochainComplex C ℕ) :=
  ShortComplex.mk (inl hS I₁ I₃) (snd hS I₁ I₃) (by ext n; simp)

lemma shortExact : (shortComplex hS I₁ I₃).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun _ =>
    (ShortComplex.Splitting.ofHasBinaryBiproduct _ _).shortExact)

/-- The image of `shortComplex` under `F` applied degreewise. -/
abbrev shortComplexMap {D : Type*} [Category* D] [Abelian D] (F : C ⥤ D) [F.Additive] :
    ShortComplex (CochainComplex D ℕ) :=
  ShortComplex.mk ((F.mapHomologicalComplex _).map (inl hS I₁ I₃))
    ((F.mapHomologicalComplex _).map (snd hS I₁ I₃))
    (by rw [← Functor.map_comp, (shortComplex hS I₁ I₃).zero, Functor.map_zero])

lemma shortExact_map {D : Type*} [Category* D] [Abelian D] (F : C ⥤ D) [F.Additive] :
    (shortComplexMap hS I₁ I₃ F).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun _ =>
    ((ShortComplex.Splitting.ofHasBinaryBiproduct _ _).map F).shortExact)

lemma exact₀_and_mono :
    (ShortComplex.mk _ _ (ι₀_d hS I₁ I₃)).Exact ∧ Mono (ι₀ hS I₁ I₃) := by
  have hT := shortExact hS I₁ I₃
  have := hT.mono_f
  have := hS.epi_g
  let K := cocomplex hS I₁ I₃
  let φ : S ⟶ ShortComplex.mk (cyclesMap (shortComplex hS I₁ I₃).f 0)
      (cyclesMap (shortComplex hS I₁ I₃).g 0)
      (by rw [← cyclesMap_comp, (shortComplex hS I₁ I₃).zero, cyclesMap_zero]) :=
    { τ₁ := I₁.cocomplex.liftCycles (aug I₁) 1 (by simp) (aug_d I₁)
      τ₂ := K.liftCycles (ι₀ hS I₁ I₃) 1 (by simp) (ι₀_d hS I₁ I₃)
      τ₃ := I₃.cocomplex.liftCycles (aug I₃) 1 (by simp) (aug_d I₃)
      comm₁₂ := by
        apply (cancel_mono (K.iCycles 0)).1
        dsimp [shortComplex, K]
        rw [Category.assoc, Category.assoc, HomologicalComplex.cyclesMap_i,
          HomologicalComplex.liftCycles_i_assoc, HomologicalComplex.liftCycles_i, inl_f, f_ι₀]
      comm₂₃ := by
        apply (cancel_mono (I₃.cocomplex.iCycles 0)).1
        dsimp [shortComplex, K]
        rw [Category.assoc, Category.assoc, HomologicalComplex.cyclesMap_i,
          HomologicalComplex.liftCycles_i_assoc, HomologicalComplex.liftCycles_i, snd_f,
          ι₀_snd] }
  have h₁ : IsIso φ.τ₁ :=
    (CochainComplex.isIso_liftCycles_iff _ _ _).2 ⟨exact_aug I₁, inferInstance⟩
  have h₃ : IsIso φ.τ₃ :=
    (CochainComplex.isIso_liftCycles_iff _ _ _).2 ⟨exact_aug I₃, inferInstance⟩
  have hφ : (ShortComplex.mk (cyclesMap (shortComplex hS I₁ I₃).f 0)
      (cyclesMap (shortComplex hS I₁ I₃).g 0)
      (by rw [← cyclesMap_comp, (shortComplex hS I₁ I₃).zero, cyclesMap_zero])).ShortExact :=
    { exact := cycles_left_exact _ hT.exact 0
      mono_f := by dsimp; infer_instance
      epi_g := by
        have : Epi (φ.τ₂ ≫ cyclesMap (shortComplex hS I₁ I₃).g 0) := by
          rw [φ.comm₂₃]
          exact epi_comp _ _
        exact epi_of_epi φ.τ₂ _ }
  have := ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ φ hS hφ
  exact (CochainComplex.isIso_liftCycles_iff _ _ _).1 this

/-- The horseshoe injective resolution `I₁ ⊞ I₃` of `S.X₂`. -/
abbrev resolution : InjectiveResolution S.X₂ where
  cocomplex := cocomplex hS I₁ I₃
  injective n := by dsimp; infer_instance
  ι := (CochainComplex.fromSingle₀Equiv _ _).symm ⟨ι₀ hS I₁ I₃, ι₀_d hS I₁ I₃⟩
  quasiIso := by
    have := (exact₀_and_mono hS I₁ I₃).2
    exact quasiIso_fromSingle₀ _ _ (exact₀_and_mono hS I₁ I₃).1 (fun n =>
      (shortExact hS I₁ I₃).exactAt_X₂ (n + 1) (I₁.cocomplex_exactAt_succ n)
        (I₃.cocomplex_exactAt_succ n))

lemma aug_resolution : aug (resolution hS I₁ I₃) = ι₀ hS I₁ I₃ :=
  congrArg Subtype.val (Equiv.apply_symm_apply _ _)

lemma inl_comm : I₁.ι.f 0 ≫ (inl hS I₁ I₃).f 0 = S.f ≫ (resolution hS I₁ I₃).ι.f 0 := by
  change aug I₁ ≫ _ = S.f ≫ aug (resolution hS I₁ I₃)
  rw [aug_resolution, f_ι₀, inl_f]

lemma snd_comm : (resolution hS I₁ I₃).ι.f 0 ≫ (snd hS I₁ I₃).f 0 = S.g ≫ I₃.ι.f 0 := by
  change aug (resolution hS I₁ I₃) ≫ _ = S.g ≫ aug I₃
  rw [aug_resolution, snd_f, ι₀_snd]

end Horseshoe

namespace Horseshoe

variable {S₁ S₂ : ShortComplex C} (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂)
  (I₁ : InjectiveResolution S₁.X₁) (I₃ : InjectiveResolution S₁.X₃)
  (J₁ : InjectiveResolution S₂.X₁) (J₃ : InjectiveResolution S₂.X₃)

/-- A lift of `φ.τ₁` to the resolutions. -/
abbrev a : I₁.cocomplex ⟶ J₁.cocomplex := InjectiveResolution.desc φ.τ₁ J₁ I₁

/-- A lift of `φ.τ₃` to the resolutions. -/
abbrev c : I₃.cocomplex ⟶ J₃.cocomplex := InjectiveResolution.desc φ.τ₃ J₃ I₃

@[reassoc]
lemma aug_a : aug I₁ ≫ (a φ I₁ J₁).f 0 = φ.τ₁ ≫ aug J₁ :=
  InjectiveResolution.desc_commutes_zero φ.τ₁ J₁ I₁

@[reassoc]
lemma aug_c : aug I₃ ≫ (c φ I₃ J₃).f 0 = φ.τ₃ ≫ aug J₃ :=
  InjectiveResolution.desc_commutes_zero φ.τ₃ J₃ I₃

/-- The defect `S₁.X₃ ⟶ J₁⁰` of the naive middle map in degree `0`. -/
def v : S₁.X₃ ⟶ J₁.cocomplex.X 0 :=
  (CokernelCofork.IsColimit.desc' hS₁.gIsCokernel
    (φ.τ₂ ≫ ext hS₂ J₁ - ext hS₁ I₁ ≫ (a φ I₁ J₁).f 0) (by
      rw [Preadditive.comp_sub, ← φ.comm₁₂_assoc, f_ext, f_ext_assoc, aug_a, sub_self])).1

@[reassoc]
lemma g_v : S₁.g ≫ v hS₁ hS₂ φ I₁ J₁ = φ.τ₂ ≫ ext hS₂ J₁ - ext hS₁ I₁ ≫ (a φ I₁ J₁).f 0 :=
  (CokernelCofork.IsColimit.desc' hS₁.gIsCokernel
    (φ.τ₂ ≫ ext hS₂ J₁ - ext hS₁ I₁ ≫ (a φ I₁ J₁).f 0) (by
      rw [Preadditive.comp_sub, ← φ.comm₁₂_assoc, f_ext, f_ext_assoc, aug_a, sub_self])).2

/-- The degree `0` off-diagonal component of the middle map. -/
def k₀ : I₃.cocomplex.X 0 ⟶ J₁.cocomplex.X 0 :=
  Injective.factorThru (v hS₁ hS₂ φ I₁ J₁) (aug I₃)

@[reassoc]
lemma aug_k₀ : aug I₃ ≫ k₀ hS₁ hS₂ φ I₁ I₃ J₁ = v hS₁ hS₂ φ I₁ J₁ :=
  Injective.comp_factorThru _ _

/-- The shift of `a`. -/
def a' : (shiftNeg I₁).cocomplex ⟶ (shiftNeg J₁).cocomplex where
  f n := (a φ I₁ J₁).f (n + 1)
  comm' i j _ := by
    simp only [Preadditive.comp_neg, Preadditive.neg_comp, HomologicalComplex.Hom.comm]

/-- The correction term, concentrated in degree `0`. -/
def N : I₃.cocomplex ⟶ (shiftNeg J₁).cocomplex where
  f n := match n with
    | 0 => k₀ hS₁ hS₂ φ I₁ I₃ J₁ ≫ J₁.cocomplex.d 0 1
    | _ + 1 => 0
  comm' i j hij := by
    simp only [ComplexShape.up_Rel] at hij
    subst hij
    cases i with
    | zero => simp
    | succ i => simp

/-- The homotopy measuring the failure of the naive middle map to be a chain map. -/
def H : Homotopy (c φ I₃ J₃ ≫ h hS₂ J₁ J₃)
    (h hS₁ I₁ I₃ ≫ a' φ I₁ J₁ - N hS₁ hS₂ φ I₁ I₃ J₁) :=
  InjectiveResolution.descHomotopy (φ.τ₃ ≫ (-u hS₂ J₁)) _ _
    (by
      apply HomologicalComplex.from_single_hom_ext
      rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, HomologicalComplex.comp_f,
        CochainComplex.single₀_map_f_zero]
      change aug I₃ ≫ (c φ I₃ J₃).f 0 ≫ hf hS₂ J₁ J₃ 0 = (φ.τ₃ ≫ (-u hS₂ J₁)) ≫ aug (shiftNeg J₁)
      rw [aug_c_assoc, aug_hf, aug_shiftNeg]
      simp only [Preadditive.comp_neg, Preadditive.neg_comp, Category.assoc])
    (by
      have := hS₁.epi_g
      apply HomologicalComplex.from_single_hom_ext
      rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero,
        HomologicalComplex.sub_f_apply, HomologicalComplex.comp_f]
      change aug I₃ ≫ (hf hS₁ I₁ I₃ 0 ≫ (a φ I₁ J₁).f 1 - k₀ hS₁ hS₂ φ I₁ I₃ J₁ ≫
        J₁.cocomplex.d 0 1) = (φ.τ₃ ≫ (-u hS₂ J₁)) ≫ aug (shiftNeg J₁)
      rw [aug_shiftNeg, ← cancel_epi S₁.g, Preadditive.comp_sub, Preadditive.comp_sub,
        g_aug_hf_assoc, aug_k₀_assoc, g_v_assoc]
      simp only [Category.assoc, Preadditive.neg_comp, Preadditive.comp_neg]
      rw [← φ.comm₂₃_assoc, g_u_assoc, π_shiftNegAug, ← (a φ I₁ J₁).comm 0 1, Preadditive.sub_comp]
      simp only [Category.assoc]
      abel)

/-- The off-diagonal components `I₃ⁿ ⟶ J₁ⁿ` of the middle map. -/
def kk : ∀ n : ℕ, I₃.cocomplex.X n ⟶ J₁.cocomplex.X n
  | 0 => k₀ hS₁ hS₂ φ I₁ I₃ J₁
  | n + 1 => (H hS₁ hS₂ φ I₁ I₃ J₁ J₃).hom (n + 1) n

lemma kk_rel (n : ℕ) :
    kk hS₁ hS₂ φ I₁ I₃ J₁ J₃ n ≫ J₁.cocomplex.d n (n + 1) +
        (c φ I₃ J₃).f n ≫ hf hS₂ J₁ J₃ n =
      hf hS₁ I₁ I₃ n ≫ (a φ I₁ J₁).f (n + 1) +
        I₃.cocomplex.d n (n + 1) ≫ kk hS₁ hS₂ φ I₁ I₃ J₁ J₃ (n + 1) := by
  have h₁ := (H hS₁ hS₂ φ I₁ I₃ J₁ J₃).comm n
  rw [Homotopy.dNext_cochainComplex] at h₁
  change (c φ I₃ J₃).f n ≫ hf hS₂ J₁ J₃ n = _ at h₁
  cases n with
  | zero =>
    rw [Homotopy.prevD_zero_cochainComplex] at h₁
    change _ = _ + 0 + (hf hS₁ I₁ I₃ 0 ≫ (a φ I₁ J₁).f 1 - k₀ hS₁ hS₂ φ I₁ I₃ J₁ ≫
      J₁.cocomplex.d 0 1) at h₁
    change k₀ hS₁ hS₂ φ I₁ I₃ J₁ ≫ J₁.cocomplex.d 0 1 + _ = _ + I₃.cocomplex.d 0 1 ≫
      (H hS₁ hS₂ φ I₁ I₃ J₁ J₃).hom 1 0
    rw [h₁]
    abel
  | succ n =>
    rw [Homotopy.prevD_succ_cochainComplex] at h₁
    change _ = _ + (H hS₁ hS₂ φ I₁ I₃ J₁ J₃).hom (n + 1) n ≫
      (-J₁.cocomplex.d (n + 1) (n + 2)) +
        (hf hS₁ I₁ I₃ (n + 1) ≫ (a φ I₁ J₁).f (n + 2) - 0) at h₁
    change (H hS₁ hS₂ φ I₁ I₃ J₁ J₃).hom (n + 1) n ≫ J₁.cocomplex.d (n + 1) (n + 2) + _ =
      _ + I₃.cocomplex.d (n + 1) (n + 2) ≫ (H hS₁ hS₂ φ I₁ I₃ J₁ J₃).hom (n + 2) (n + 1)
    rw [h₁, Preadditive.comp_neg]
    abel

/-- The middle component `I₁ ⊞ I₃ ⟶ J₁ ⊞ J₃` of the morphism of horseshoes. -/
def m : cocomplex hS₁ I₁ I₃ ⟶ cocomplex hS₂ J₁ J₃ :=
  CochainComplex.ofHom (fun n => (biprod.desc ((a φ I₁ J₁).f n ≫ biprod.inl)
      (kk hS₁ hS₂ φ I₁ I₃ J₁ J₃ n ≫ biprod.inl + (c φ I₃ J₃).f n ≫ biprod.inr) :
        X I₁ I₃ n ⟶ X J₁ J₃ n)) (fun n => by
    rw [cocomplex_d, cocomplex_d]
    apply biprod.hom_ext'
    · simp only [biprod.inl_desc_assoc, Category.assoc, inl_d, inl_d_assoc, biprod.inl_desc]
      rw [← Category.assoc, (a φ I₁ J₁).comm, Category.assoc]
    · simp only [biprod.inr_desc_assoc, Preadditive.add_comp, Category.assoc, inl_d, inr_d,
        inr_d_assoc, biprod.inl_desc, biprod.inr_desc, Preadditive.comp_add]
      apply biprod.hom_ext
      · simp only [Preadditive.add_comp, Category.assoc, biprod.inl_fst, biprod.inr_fst,
          comp_zero, add_zero, Category.comp_id]
        exact kk_rel hS₁ hS₂ φ I₁ I₃ J₁ J₃ n
      · simp only [Preadditive.add_comp, Category.assoc, biprod.inl_snd, biprod.inr_snd,
          comp_zero, zero_add, Category.comp_id]
        exact (c φ I₃ J₃).comm n (n + 1))

lemma m_f (n : ℕ) : (m hS₁ hS₂ φ I₁ I₃ J₁ J₃).f n =
    biprod.desc ((a φ I₁ J₁).f n ≫ biprod.inl)
      (kk hS₁ hS₂ φ I₁ I₃ J₁ J₃ n ≫ biprod.inl + (c φ I₃ J₃).f n ≫ biprod.inr) := rfl

/-- The morphism of horseshoe short exact sequences lifting `φ`. -/
def ψ : shortComplex hS₁ I₁ I₃ ⟶ shortComplex hS₂ J₁ J₃ where
  τ₁ := a φ I₁ J₁
  τ₂ := m hS₁ hS₂ φ I₁ I₃ J₁ J₃
  τ₃ := c φ I₃ J₃
  comm₁₂ := by
    ext n : 1
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, inl_f, inl_f, m_f,
      biprod.inl_desc]
  comm₂₃ := by
    ext n : 1
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, snd_f, snd_f, m_f]
    apply biprod.hom_ext'
    · simp
    · simp

end Horseshoe

end Resolutions

section Functor

variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
  {D : Type*} [Category* D] [Abelian D] (F : C ⥤ D) [F.Additive]

lemma upRel (n : ℕ) : (ComplexShape.up ℕ).Rel n (n + 1) := rfl

/-- `InjectiveResolution.isoRightDerivedObj`, with its target written as a homology object. -/
def isoH {X : C} (I : InjectiveResolution X) (n : ℕ) :
    (F.rightDerived n).obj X ≅ ((F.mapHomologicalComplex _).obj I.cocomplex).homology n :=
  I.isoRightDerivedObj F n

@[reassoc]
lemma map_comp_isoH_hom {X Y : C} (f : X ⟶ Y) (I : InjectiveResolution X)
    (J : InjectiveResolution Y) (φ : I.cocomplex ⟶ J.cocomplex)
    (comm : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (n : ℕ) :
    (F.rightDerived n).map f ≫ (isoH F J n).hom =
      (isoH F I n).hom ≫ homologyMap ((F.mapHomologicalComplex _).map φ) n :=
  InjectiveResolution.isoRightDerivedObj_hom_naturality f I J φ comm F n

@[reassoc]
lemma isoH_inv_comp_map {X Y : C} (f : X ⟶ Y) (I : InjectiveResolution X)
    (J : InjectiveResolution Y) (φ : I.cocomplex ⟶ J.cocomplex)
    (comm : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (n : ℕ) :
    (isoH F I n).inv ≫ (F.rightDerived n).map f =
      homologyMap ((F.mapHomologicalComplex _).map φ) n ≫ (isoH F J n).inv :=
  InjectiveResolution.isoRightDerivedObj_inv_naturality f I J φ comm F n

instance rightDerived_additive (n : ℕ) : (F.rightDerived n).Additive where
  map_add {X Y f g} := by
    let I := injectiveResolution X
    let J := injectiveResolution Y
    rw [← cancel_mono (isoH F J n).hom, Preadditive.add_comp,
      map_comp_isoH_hom F f I J (InjectiveResolution.desc f J I) (InjectiveResolution.desc_commutes_zero f J I) n,
      map_comp_isoH_hom F g I J (InjectiveResolution.desc g J I) (InjectiveResolution.desc_commutes_zero g J I) n,
      map_comp_isoH_hom F (f + g) I J
        (InjectiveResolution.desc f J I + InjectiveResolution.desc g J I) (by
          rw [HomologicalComplex.add_f_apply, Preadditive.comp_add,
            InjectiveResolution.desc_commutes_zero, InjectiveResolution.desc_commutes_zero]
          exact (Preadditive.add_comp _ _ _ _ _ _).symm) n,
      Functor.map_add, homologyMap_add, Preadditive.comp_add]

namespace Horseshoe

variable {S : ShortComplex C} (hS : S.ShortExact)
  (I₁ : InjectiveResolution S.X₁) (I₃ : InjectiveResolution S.X₃)

/-- The connecting morphism `RⁿF(S.X₃) ⟶ Rⁿ⁺¹F(S.X₁)` computed from the horseshoe resolution
built on `I₁` and `I₃`. -/
def δ (n : ℕ) : (F.rightDerived n).obj S.X₃ ⟶ (F.rightDerived (n + 1)).obj S.X₁ :=
  (isoH F I₃ n).hom ≫ (shortExact_map hS I₁ I₃ F).δ n (n + 1) (upRel n) ≫
    (isoH F I₁ (n + 1)).inv

@[reassoc]
lemma map_f_comp_iso (n : ℕ) :
    (F.rightDerived n).map S.f ≫ (isoH F (resolution hS I₁ I₃) n).hom =
      (isoH F I₁ n).hom ≫
        homologyMap (shortComplexMap hS I₁ I₃ F).f n :=
  map_comp_isoH_hom F S.f I₁ (resolution hS I₁ I₃) (inl hS I₁ I₃) (inl_comm hS I₁ I₃) n

@[reassoc]
lemma map_g_comp_iso (n : ℕ) :
    (F.rightDerived n).map S.g ≫ (isoH F I₃ n).hom =
      (isoH F (resolution hS I₁ I₃) n).hom ≫
        homologyMap (shortComplexMap hS I₁ I₃ F).g n :=
  map_comp_isoH_hom F S.g (resolution hS I₁ I₃) I₃ (snd hS I₁ I₃) (snd_comm hS I₁ I₃) n

@[reassoc]
lemma δ_comp_iso (n : ℕ) :
    δ F hS I₁ I₃ n ≫ (isoH F I₁ (n + 1)).hom =
      (isoH F I₃ n).hom ≫ (shortExact_map hS I₁ I₃ F).δ n (n + 1) (upRel n) := by
  rw [δ, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

lemma map_g_comp_δ (n : ℕ) : (F.rightDerived n).map S.g ≫ δ F hS I₁ I₃ n = 0 := by
  have := (shortExact_map hS I₁ I₃ F).comp_δ n (n + 1) (upRel n)
  rw [← cancel_mono (isoH F I₁ (n + 1)).hom, Category.assoc, δ_comp_iso,
    map_g_comp_iso_assoc F hS I₁ I₃ n, this, comp_zero, zero_comp]

lemma δ_comp_map_f (n : ℕ) : δ F hS I₁ I₃ n ≫ (F.rightDerived (n + 1)).map S.f = 0 := by
  have := (shortExact_map hS I₁ I₃ F).δ_comp n (n + 1) (upRel n)
  rw [← cancel_mono (isoH F (resolution hS I₁ I₃) (n + 1)).hom, Category.assoc,
    map_f_comp_iso F hS I₁ I₃ (n + 1), δ_comp_iso_assoc F hS I₁ I₃ n, this, comp_zero,
    zero_comp]

include hS in
lemma exact₂ (n : ℕ) : (ShortComplex.mk ((F.rightDerived n).map S.f) ((F.rightDerived n).map S.g)
    (by rw [← Functor.map_comp, S.zero, Functor.map_zero])).Exact := by
  let I₁ := injectiveResolution S.X₁
  let I₃ := injectiveResolution S.X₃
  refine (ShortComplex.exact_iff_of_iso ?_).2 ((shortExact_map hS I₁ I₃ F).homology_exact₂ n)
  exact ShortComplex.isoMk (isoH F I₁ n) (isoH F (resolution hS I₁ I₃) n)
    (isoH F I₃ n) (map_f_comp_iso F hS I₁ I₃ n).symm (map_g_comp_iso F hS I₁ I₃ n).symm

lemma exact₃ (n : ℕ) : (ShortComplex.mk ((F.rightDerived n).map S.g) (δ F hS I₁ I₃ n)
    (map_g_comp_δ F hS I₁ I₃ n)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).2
    ((shortExact_map hS I₁ I₃ F).homology_exact₃ n (n + 1) (upRel n))
  exact ShortComplex.isoMk (isoH F (resolution hS I₁ I₃) n)
    (isoH F I₃ n) (isoH F I₁ (n + 1))
    (map_g_comp_iso F hS I₁ I₃ n).symm (δ_comp_iso F hS I₁ I₃ n).symm

lemma exact₁ (n : ℕ) : (ShortComplex.mk (δ F hS I₁ I₃ n) ((F.rightDerived (n + 1)).map S.f)
    (δ_comp_map_f F hS I₁ I₃ n)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).2
    ((shortExact_map hS I₁ I₃ F).homology_exact₁ n (n + 1) (upRel n))
  exact ShortComplex.isoMk (isoH F I₃ n) (isoH F I₁ (n + 1))
    (isoH F (resolution hS I₁ I₃) (n + 1))
    (δ_comp_iso F hS I₁ I₃ n).symm (map_f_comp_iso F hS I₁ I₃ (n + 1)).symm

include hS in
lemma mono_map_f : Mono ((F.rightDerived 0).map S.f) := by
  let I₁ := injectiveResolution S.X₁
  let I₃ := injectiveResolution S.X₃
  have hT := shortExact_map hS I₁ I₃ F
  have := hT.mono_f
  let T := shortComplexMap hS I₁ I₃ F
  have : Mono (homologyMap T.f 0) := by
    have : Mono (homologyMap T.f 0 ≫ T.X₂.isoHomologyπ₀.inv) := by
      rw [CochainComplex.isoHomologyπ₀_inv_naturality]
      infer_instance
    exact mono_of_mono _ T.X₂.isoHomologyπ₀.inv
  have : Mono ((F.rightDerived 0).map S.f ≫ (isoH F (resolution hS I₁ I₃) 0).hom) := by
    rw [map_f_comp_iso]
    infer_instance
  exact mono_of_mono _ (isoH F (resolution hS I₁ I₃) 0).hom

end Horseshoe

namespace Horseshoe

variable {S₁ S₂ : ShortComplex C} (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂)
  (I₁ : InjectiveResolution S₁.X₁) (I₃ : InjectiveResolution S₁.X₃)
  (J₁ : InjectiveResolution S₂.X₁) (J₃ : InjectiveResolution S₂.X₃)

/-- The image under `F` of the morphism of horseshoes `ψ`. -/
def ψMap : shortComplexMap hS₁ I₁ I₃ F ⟶ shortComplexMap hS₂ J₁ J₃ F where
  τ₁ := (F.mapHomologicalComplex _).map (a φ I₁ J₁)
  τ₂ := (F.mapHomologicalComplex _).map (m hS₁ hS₂ φ I₁ I₃ J₁ J₃)
  τ₃ := (F.mapHomologicalComplex _).map (c φ I₃ J₃)
  comm₁₂ := by
    simp only [← Functor.map_comp]
    exact congrArg (F.mapHomologicalComplex _).map (ψ hS₁ hS₂ φ I₁ I₃ J₁ J₃).comm₁₂
  comm₂₃ := by
    simp only [← Functor.map_comp]
    exact congrArg (F.mapHomologicalComplex _).map (ψ hS₁ hS₂ φ I₁ I₃ J₁ J₃).comm₂₃

lemma δ_naturality (n : ℕ) :
    δ F hS₁ I₁ I₃ n ≫ (F.rightDerived (n + 1)).map φ.τ₁ =
      (F.rightDerived n).map φ.τ₃ ≫ δ F hS₂ J₁ J₃ n := by
  have hnat := HomologicalComplex.HomologySequence.δ_naturality
    (ψMap F hS₁ hS₂ φ I₁ I₃ J₁ J₃) (shortExact_map hS₁ I₁ I₃ F) (shortExact_map hS₂ J₁ J₃ F)
    n (n + 1) (upRel n)
  have h₁ := isoH_inv_comp_map F φ.τ₁ I₁ J₁ (a φ I₁ J₁)
    (InjectiveResolution.desc_commutes_zero _ _ _) (n + 1)
  have h₃ := map_comp_isoH_hom F φ.τ₃ I₃ J₃ (c φ I₃ J₃)
    (InjectiveResolution.desc_commutes_zero _ _ _) n
  simp only [δ, Category.assoc]
  rw [h₁, reassoc_of% h₃]
  have := congrArg (fun t => (isoH F I₃ n).hom ≫ t ≫ (isoH F J₁ (n + 1)).inv) hnat
  simp only [Category.assoc] at this
  exact this

end Horseshoe

end Functor

end RightDerivedLES

open RightDerivedLES

variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
  {D : Type*} [Category* D] [Abelian D] (F : C ⥤ D) [F.Additive]
  {S : ShortComplex C} (hS : S.ShortExact)

/-- The connecting morphism `RⁿF(A'') ⟶ Rⁿ⁺¹F(A')` attached to a short exact sequence
`0 ⟶ A' ⟶ A ⟶ A'' ⟶ 0`. -/
def rightDerivedδ (n : ℕ) : (F.rightDerived n).obj S.X₃ ⟶ (F.rightDerived (n + 1)).obj S.X₁ :=
  Horseshoe.δ F hS (injectiveResolution S.X₁) (injectiveResolution S.X₃) n

include hS in
/-- The long exact sequence starts with `0`: `R⁰F(A') ⟶ R⁰F(A)` is a monomorphism. -/
theorem rightDerived_mono_map_f : Mono ((F.rightDerived 0).map S.f) :=
  Horseshoe.mono_map_f F hS

include hS in
/-- Exactness of `RⁿF(A') ⟶ RⁿF(A) ⟶ RⁿF(A'')`. -/
theorem rightDerived_exact₂ (n : ℕ) :
    (ShortComplex.mk ((F.rightDerived n).map S.f) ((F.rightDerived n).map S.g)
      (by rw [← Functor.map_comp, S.zero, Functor.map_zero])).Exact :=
  Horseshoe.exact₂ F hS n

/-- Exactness of `RⁿF(A) ⟶ RⁿF(A'') ⟶ Rⁿ⁺¹F(A')`. -/
theorem rightDerived_exact₃ (n : ℕ) :
    (ShortComplex.mk ((F.rightDerived n).map S.g) (rightDerivedδ F hS n)
      (Horseshoe.map_g_comp_δ F hS _ _ n)).Exact :=
  Horseshoe.exact₃ F hS _ _ n

/-- Exactness of `RⁿF(A'') ⟶ Rⁿ⁺¹F(A') ⟶ Rⁿ⁺¹F(A)`. -/
theorem rightDerived_exact₁ (n : ℕ) :
    (ShortComplex.mk (rightDerivedδ F hS n) ((F.rightDerived (n + 1)).map S.f)
      (Horseshoe.δ_comp_map_f F hS _ _ n)).Exact :=
  Horseshoe.exact₁ F hS _ _ n

/-- The connecting morphisms are natural in morphisms of short exact sequences. -/
theorem rightDerivedδ_naturality {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (n : ℕ) :
    rightDerivedδ F hS₁ n ≫ (F.rightDerived (n + 1)).map φ.τ₁ =
      (F.rightDerived n).map φ.τ₃ ≫ rightDerivedδ F hS₂ n :=
  Horseshoe.δ_naturality F hS₁ hS₂ φ _ _ _ _ n

end Hartshorne

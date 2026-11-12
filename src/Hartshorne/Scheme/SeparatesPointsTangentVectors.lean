/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.FiniteLinearSystem
import Hartshorne.Scheme.ProjectionFromPoint
import Hartshorne.Scheme.ProjectiveClosedImmersionChartCriterion
import Hartshorne.Scheme.ProjectiveSpaceProper
import Hartshorne.Scheme.CotangentSurjectivity
import Hartshorne.Scheme.ProjectivePushforwardCoherent
import Hartshorne.Scheme.ProjectiveMorphismCalculus
import Hartshorne.Scheme.CoherentAffineLocalCriterion
import Hartshorne.Cohomology.Flatness.CoherentSelfFlatLocallyFree
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# Separation of points and tangent vectors

Hartshorne, *Algebraic Geometry*, II, Proposition 7.3 and Lemma 7.4 (pp. 152–153).

Let `X` be a scheme over a field `k` (structure morphism `q`), `L` an invertible sheaf on `X`, and
`V ⊆ Γ(X, L)` the subspace spanned by global sections `s₀, …, sₙ`. Following Hartshorne (p. 152):

* `V` **separates points** (`SectionsSeparatePoints`) if for any two distinct closed points
  `P ≠ Q` there is `s ∈ V` with `s_P ∈ 𝔪_P L_P` and `s_Q ∉ 𝔪_Q L_Q`, or vice versa;
* `V` **separates tangent vectors** (`SectionsSeparateTangentVectors`) if for each closed point
  `P`, the set `{s ∈ V : s_P ∈ 𝔪_P L_P}` spans the `k`-vector space `𝔪_P L_P / 𝔪_P² L_P`.

Proposition 7.3 states that, for `X` projective over an algebraically closed field and `V`
generating `L`, the morphism `φ : X ⟶ ℙⁿ_k` defined by `s₀, …, sₙ` is a closed immersion iff `V`
separates points and tangent vectors.

## Main results

* `isClosedImmersion_iff_sectionsSeparatePoints_and_sectionsSeparateTangentVectors`:
  Proposition 7.3.
* `isClosedImmersion_of_sectionsSeparatePoints_of_sectionsSeparateTangentVectors`: the direction
  (⇐); `sectionsSeparatePoints_of_injective` and
  `sectionsSeparateTangentVectors_of_isClosedImmersion`: the direction (⇒).

Steps of (⇐), following Hartshorne:

* `mem_nonvanishingLocus_linearSystemSection_iff`: the section `∑ aᵢ sᵢ ∈ V` is the pullback of
  the linear form `∑ aᵢ xᵢ`, so the hyperplane `∑ aᵢ xᵢ = 0` pulls back to its zeros;
* `isClosedEmbedding_of_sectionsSeparatePoints`: separation of points makes `φ` injective, and `φ`
  is proper, so `φ` is a homeomorphism onto a closed subset;
* `moduleFinite_stalk_of_sectionsSeparatePoints`: `φ_* 𝒪_X` is coherent (Corollary 5.20), so
  `𝒪_{X,P}` is a finite `𝒪_{ℙⁿ, φ(P)}`-module;
* `residueField_map_bijective_of_isClosed` and
  `maximalIdealToCotangent_surjective_of_sectionsSeparateTangentVectors`: at a closed point the
  residue fields agree and `𝔪_{φ(P)} → 𝔪_P / 𝔪_P²` is surjective, so by Lemma 7.4
  (`stalkMap_surjective_of_sectionsSeparateTangentVectors`) `𝒪_{ℙⁿ, φ(P)} → 𝒪_{X,P}` is
  surjective; surjectivity at the other points follows by localization.

For (⇒), a closed point of `ℙⁿ_k` is a `k`-point `(a₀ : ⋯ : aₙ)`, so hyperplanes separate the
images of distinct closed points, and the maximal ideal of `𝒪_{ℙⁿ, z}` at such a point is spanned
modulo its square by linear functions.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

namespace Hartshorne

/-! ### Definitions -/

section Definitions

variable {k : Type u} [Field k] {X : Scheme.{u}} (q : X ⟶ Spec (CommRingCat.of k))
  {L : X.Modules}

/-- The constants `k → 𝒪_{X,P}` of a scheme over `k` (structure morphism `q`): the image of
`kConst q` in the stalk at `P`. This is the `k`-structure on the stalks of `𝒪_X`-modules. -/
def kConstStalk (P : X) : k →+* X.presheaf.stalk P :=
  (X.presheaf.germ ⊤ P trivial).hom.comp (kConst q)

/-- **Separation of points** (Hartshorne II, p. 152). A set `V` of global sections of an
`𝒪_X`-module `L` separates points if for any two distinct closed points `P ≠ Q` of `X` there is
`s ∈ V` with `s_P ∈ 𝔪_P L_P` but `s_Q ∉ 𝔪_Q L_Q`, or vice versa. -/
def SectionsSeparatePoints (V : Set Γ(L, ⊤)) : Prop :=
  ∀ P Q : X, IsClosed {P} → IsClosed {Q} → P ≠ Q → ∃ t ∈ V,
    (L.presheaf.germ ⊤ P trivial t ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk P) •
          (⊤ : Submodule (X.presheaf.stalk P) (L.presheaf.stalk P)) ∧
      L.presheaf.germ ⊤ Q trivial t ∉
        IsLocalRing.maximalIdeal (X.presheaf.stalk Q) •
          (⊤ : Submodule (X.presheaf.stalk Q) (L.presheaf.stalk Q))) ∨
    (L.presheaf.germ ⊤ Q trivial t ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk Q) •
          (⊤ : Submodule (X.presheaf.stalk Q) (L.presheaf.stalk Q)) ∧
      L.presheaf.germ ⊤ P trivial t ∉
        IsLocalRing.maximalIdeal (X.presheaf.stalk P) •
          (⊤ : Submodule (X.presheaf.stalk P) (L.presheaf.stalk P)))

/-- **Separation of tangent vectors** (Hartshorne II, p. 152). A set `V` of global sections of an
`𝒪_X`-module `L` on a scheme over `k` separates tangent vectors if for each closed point `P` of
`X`, the set `{s ∈ V : s_P ∈ 𝔪_P L_P}` spans the `k`-vector space `𝔪_P L_P / 𝔪_P² L_P`: every
`z ∈ 𝔪_P L_P` is congruent modulo `𝔪_P² L_P` to a `k`-linear combination `∑ cᵢ (tᵢ)_P` of germs
of sections `tᵢ ∈ V` with `(tᵢ)_P ∈ 𝔪_P L_P` (`k` acting on `L_P` through `𝒪_{X,P}`). -/
def SectionsSeparateTangentVectors (V : Set Γ(L, ⊤)) : Prop :=
  ∀ P : X, IsClosed {P} → ∀ z ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk P) •
          (⊤ : Submodule (X.presheaf.stalk P) (L.presheaf.stalk P)),
    ∃ (m : ℕ) (c : Fin m → k) (t : Fin m → Γ(L, ⊤)),
      (∀ i, t i ∈ V ∧ L.presheaf.germ ⊤ P trivial (t i) ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk P) •
          (⊤ : Submodule (X.presheaf.stalk P) (L.presheaf.stalk P))) ∧
      z - ∑ i, kConstStalk q P (c i) • L.presheaf.germ ⊤ P trivial (t i) ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk P) ^ 2 •
          (⊤ : Submodule (X.presheaf.stalk P) (L.presheaf.stalk P))

/-- `s_P ∈ 𝔪_P L_P` exactly when `P` is not in the nonvanishing locus `X_s` of `s`. -/
theorem germ_mem_maximalIdeal_smul_top_iff (t : Γ(L, ⊤)) (P : X) :
    L.presheaf.germ ⊤ P trivial t ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk P) •
          (⊤ : Submodule (X.presheaf.stalk P) (L.presheaf.stalk P)) ↔
      P ∉ nonvanishingLocus L t :=
  not_not.symm

end Definitions

/-! ### Hyperplanes pull back to zero loci -/

section Hyperplanes

variable {X : Scheme.{u}}

/-- Nonvanishing loci are invariant under isomorphisms of invertible sheaves. -/
private theorem mem_nonvanishingLocus_hom_app_iff {M N : X.Modules} (hM : M.IsInvertible)
    (α : M ≅ N) (t : Γ(M, ⊤)) (x : X) :
    x ∈ nonvanishingLocus N (α.hom.app ⊤ t) ↔ x ∈ nonvanishingLocus M t := by
  obtain ⟨W, e, hxW, he⟩ := exists_isTrivializingSection hM x
  obtain ⟨g, hg⟩ := he.exists_eq_smul t
  have hg' : N.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (α.hom.app ⊤ t) =
      g • α.hom.app W e := by
    rw [← hom_app_map, hg, Scheme.Modules.Hom.app_smul]
  rw [(he.map_iso α).mem_nonvanishingLocus_iff hg' hxW, he.mem_nonvanishingLocus_iff hg hxW]

variable {k : Type u} [Field k] (q : X ⟶ Spec (CommRingCat.of k)) {L : X.Modules}
  (hL : L.IsInvertible) {n : ℕ} (s : Fin (n + 1) → Γ(L, ⊤))
  (φ : X ⟶ projectiveSpaceOverScheme n (Spec (CommRingCat.of k)))
  (hφ : φ ≫ projectiveSpaceOverSchemeProjection n _ = q)
  (e : (Scheme.Modules.pullback φ).obj (projectiveSpaceTwistingSheaf n _ 1) ≅ L)
  (he : ∀ i, e.hom.app ⊤ (pullbackGlobalSection φ (projectiveSpaceCoordinate n _ i)) = s i)

include hφ he in
/-- **Hyperplanes pull back to zero loci** (Hartshorne II, proof of Proposition 7.3). If
`φ : X ⟶ ℙⁿ_k` is defined by the sections `sᵢ` of `L`, then a point `x` lies in the nonvanishing
locus of `∑ aᵢ sᵢ` iff `φ(x)` lies off the hyperplane `∑ aᵢ xᵢ = 0`. -/
theorem mem_nonvanishingLocus_linearSystemSection_iff (a : Fin (n + 1) → k) (x : X) :
    x ∈ nonvanishingLocus L (linearSystemSection q s a) ↔
      φ x ∈ nonvanishingLocus _ (linearSection k n a) := by
  have h : linearSystemSection q s a =
      e.hom.app ⊤ (pullbackGlobalSection φ (linearSection k n a)) :=
    (iso_app_linearSection hφ e he a).symm
  rw [h, mem_nonvanishingLocus_hom_app_iff
      (isInvertible_pullback_projectiveSpaceTwistingSheaf φ) e,
    mem_nonvanishingLocus_pullbackGlobalSection_iff _
      (isInvertible_projectiveSpaceTwistingSheaf _ _ _)]

end Hyperplanes

/-! ### Separation of points makes `φ` injective -/

section Points

/-- A closed map from a Jacobson `T₀` space, injective on closed points, is injective. -/
private theorem injective_of_injOn_closedPoints {T T' : Type*} [TopologicalSpace T]
    [TopologicalSpace T'] [JacobsonSpace T] [T0Space T] {f : T → T'} (hf : Continuous f)
    (hc : IsClosedMap f) (hinj : ∀ x y : T, IsClosed {x} → IsClosed {y} → f x = f y → x = y) :
    Function.Injective f := by
  -- The closed points in `closure {x}` are determined by `f x`.
  have key : ∀ x y : T, f x = f y → closure {x} ∩ closedPoints T ⊆ closure {y} := by
    rintro x y hxy w ⟨hw, hwc⟩
    have hfw : f w ∈ closure {f y} := by
      have := image_closure_subset_closure_image hf ⟨w, hw, rfl⟩
      rwa [Set.image_singleton, hxy] at this
    have hcl : closure {f y} ⊆ f '' closure {y} :=
      closure_minimal (Set.singleton_subset_iff.mpr ⟨y, subset_closure rfl, rfl⟩)
        (hc _ isClosed_closure)
    obtain ⟨w', hw', hw'w⟩ := hcl hfw
    obtain ⟨w'', hw'', hw''c⟩ := nonempty_inter_closedPoints (Z := closure {w'})
      ⟨w', subset_closure rfl⟩ isClosed_closure.isLocallyClosed
    have hfw'' : f w'' ∈ ({f w} : Set T') := by
      have h1 := image_closure_subset_closure_image hf ⟨w'', hw'', rfl⟩
      rw [Set.image_singleton, hw'w] at h1
      have h2 : IsClosed ({f w} : Set T') := by
        simpa [Set.image_singleton] using hc _ hwc
      rwa [h2.closure_eq] at h1
    have hww : w'' = w := hinj _ _ hw''c hwc hfw''
    subst hww
    exact closure_minimal (Set.singleton_subset_iff.mpr hw') isClosed_closure hw''
  have sub : ∀ x y : T, f x = f y → closure ({x} : Set T) ⊆ closure {y} := fun x y h =>
    calc closure ({x} : Set T) = closure (closure {x}) := closure_closure.symm
      _ = closure (closure {x} ∩ closedPoints T) :=
        (JacobsonSpace.closure_inter_closedPoints_eq_closure
          isClosed_closure.isLocallyClosed).symm
      _ ⊆ closure {y} := closure_minimal (key x y h) isClosed_closure
  intro x y hxy
  exact (inseparable_iff_closure_eq.mpr ((sub x y hxy).antisymm (sub y x hxy.symm))).eq

variable {k : Type u} [Field k] {X : Scheme.{u}} (q : X ⟶ Spec (CommRingCat.of k))
  {L : X.Modules} {n : ℕ} (s : Fin (n + 1) → Γ(L, ⊤))
  (φ : X ⟶ projectiveSpaceOverScheme n (Spec (CommRingCat.of k)))
  (hφ : φ ≫ projectiveSpaceOverSchemeProjection n _ = q)
  (e : (Scheme.Modules.pullback φ).obj (projectiveSpaceTwistingSheaf n _ 1) ≅ L)
  (he : ∀ i, e.hom.app ⊤ (pullbackGlobalSection φ (projectiveSpaceCoordinate n _ i)) = s i)

include hφ he in
/-- **Separation of points makes `φ` injective on closed points** (Hartshorne II, proof of
Proposition 7.3). If the subspace `V` spanned by the sections `sᵢ` defining `φ : X ⟶ ℙⁿ_k`
separates points, then `φ(P) ≠ φ(Q)` for distinct closed points `P ≠ Q`: a section of `V`
vanishing at exactly one of them is the pullback of a hyperplane containing exactly one of
`φ(P)`, `φ(Q)`. -/
theorem eq_of_sectionsSeparatePoints (hsep : SectionsSeparatePoints (linearSystem q s))
    {P Q : X} (hP : IsClosed {P}) (hQ : IsClosed {Q}) (hPQ : φ P = φ Q) : P = Q := by
  by_contra hne
  obtain ⟨_, ⟨a, rfl⟩, h⟩ := hsep P Q hP hQ hne
  have hiff : P ∈ nonvanishingLocus L (linearSystemSection q s a) ↔
      Q ∈ nonvanishingLocus L (linearSystemSection q s a) := by
    rw [mem_nonvanishingLocus_linearSystemSection_iff q s φ hφ e he,
      mem_nonvanishingLocus_linearSystemSection_iff q s φ hφ e he, hPQ]
  simp only [germ_mem_maximalIdeal_smul_top_iff, not_not] at h
  tauto

include hφ he in
/-- **Separation of points makes `φ` injective** (Hartshorne II, proof of Proposition 7.3). Let
`X` be projective over `k`. If the subspace `V` spanned by the sections `sᵢ` defining
`φ : X ⟶ ℙⁿ_k` separates points, then `φ` is injective: it is injective on closed points, and
since `φ` is proper, hence closed, and `X` is a Jacobson space, this gives injectivity on all
points. -/
theorem injective_of_sectionsSeparatePoints (hX : Projective q)
    (hsep : SectionsSeparatePoints (linearSystem q s)) : Function.Injective φ := by
  have : IsProper q := hX.isProper
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace q
  have : IsProper (projectiveSpaceOverSchemeProjection n (Spec (CommRingCat.of k))) :=
    projectiveSpaceOverSchemeProjection_isProper n _
  have : IsProper (φ ≫ projectiveSpaceOverSchemeProjection n _) := hφ ▸ inferInstance
  have : IsProper φ := IsProper.of_comp φ (projectiveSpaceOverSchemeProjection n _)
  exact injective_of_injOn_closedPoints φ.continuous φ.isClosedMap
    fun P Q hP hQ hPQ => eq_of_sectionsSeparatePoints q s φ hφ e he hsep hP hQ hPQ

include hφ he in
/-- **`φ` is a homeomorphism onto a closed subset** (Hartshorne II, proof of Proposition 7.3).
Let `X` be projective over `k`. If the subspace `V` spanned by the sections `sᵢ` defining
`φ : X ⟶ ℙⁿ_k` separates points, then `φ` is a closed embedding of topological spaces: it is
injective and proper, hence closed. -/
theorem isClosedEmbedding_of_sectionsSeparatePoints (hX : Projective q)
    (hsep : SectionsSeparatePoints (linearSystem q s)) : Topology.IsClosedEmbedding φ := by
  have : IsProper q := hX.isProper
  have : IsProper (projectiveSpaceOverSchemeProjection n (Spec (CommRingCat.of k))) :=
    projectiveSpaceOverSchemeProjection_isProper n _
  have : IsProper (φ ≫ projectiveSpaceOverSchemeProjection n _) := hφ ▸ inferInstance
  have : IsProper φ := IsProper.of_comp φ (projectiveSpaceOverSchemeProjection n _)
  exact .of_continuous_injective_isClosedMap φ.continuous
    (injective_of_sectionsSeparatePoints q s φ hφ e he hX hsep) φ.isClosedMap

end Points

/-! ### Separation of tangent vectors gives a surjection on cotangent spaces -/

section Tangents

/-- A trivializing section generates the stalk freely: `b ε_x ∈ I L_x` iff `b ∈ I`. -/
private theorem smul_germ_mem_smul_top_iff {X : Scheme.{u}} {L : X.Modules} {U : X.Opens}
    {ε : Γ(L, U)} (hε : IsTrivializingSection L U ε) {x : X} (hx : x ∈ U)
    (I : Ideal (X.presheaf.stalk x)) (b : X.presheaf.stalk x) :
    b • L.presheaf.germ U x hx ε ∈
        I • (⊤ : Submodule (X.presheaf.stalk x) (L.presheaf.stalk x)) ↔ b ∈ I := by
  have htop : (⊤ : Submodule (X.presheaf.stalk x) (L.presheaf.stalk x)) =
      Submodule.span (X.presheaf.stalk x) {L.presheaf.germ U x hx ε} := by
    refine (Submodule.eq_top_iff'.mpr fun z => ?_).symm
    obtain ⟨c, rfl⟩ := hε.exists_smul_germ_eq hx z
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)
  rw [htop, Submodule.mem_smul_span_singleton]
  constructor
  · rintro ⟨c, hc, hce⟩
    have hsub : (c - b) • L.presheaf.germ U x hx ε = 0 := by rw [sub_smul, hce, sub_self]
    rwa [sub_eq_zero.mp (hε.eq_zero_of_smul_germ_eq_zero hx _ hsub)] at hc
  · intro hb
    exact ⟨b, hb, rfl⟩

private theorem germ_smul_module {X : Scheme.{u}} (F : X.Modules) {U : X.Opens} (x : X)
    (hx : x ∈ U) (r : Γ(X, U)) (m : Γ(F, U)) :
    F.presheaf.germ U x hx (r • m) = X.presheaf.germ U x hx r • F.presheaf.germ U x hx m :=
  let M : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat) := F.val
  PresheafOfModules.germ_smul M x U hx r m

/-- The germ of `f^#(r)` along `appLE` is the image of the germ of `r` under the stalk map. -/
private theorem germ_appLE_eq_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens}
    {V : X.Opens} (h : V ≤ f ⁻¹ᵁ U) (x : X) (hx : x ∈ V) (r : Γ(Y, U)) :
    X.presheaf.germ V x hx (f.appLE U V h r) =
      f.stalkMap x (Y.presheaf.germ U (f x) (show f x ∈ U from h hx) r) := by
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply,
    Scheme.Hom.germ_stalkMap_apply]

variable {k : Type u} [Field k] {X : Scheme.{u}} (q : X ⟶ Spec (CommRingCat.of k))
  {L : X.Modules} (hL : L.IsInvertible) {n : ℕ} (s : Fin (n + 1) → Γ(L, ⊤))
  (φ : X ⟶ projectiveSpaceOverScheme n (Spec (CommRingCat.of k)))
  (hφ : φ ≫ projectiveSpaceOverSchemeProjection n _ = q)
  (e : (Scheme.Modules.pullback φ).obj (projectiveSpaceTwistingSheaf n _ 1) ≅ L)
  (he : ∀ i, e.hom.app ⊤ (pullbackGlobalSection φ (projectiveSpaceCoordinate n _ i)) = s i)

include hφ in
/-- The constants of `𝒪_{X,P}` are the images of the constants of `𝒪_{ℙⁿ, φ(P)}`. -/
private theorem kConstStalk_eq_stalkMap (P : X) (c : k) :
    kConstStalk q P c = φ.stalkMap P ((projectiveSpaceOverScheme n _).presheaf.germ ⊤ (φ P) trivial
      (kConst (projectiveSpaceOverSchemeProjection n (Spec (CommRingCat.of k))) c)) := by
  rw [kConstStalk, RingHom.comp_apply, ← hφ, ← appTop_kConst]
  exact (Scheme.Hom.germ_stalkMap_apply φ ⊤ P trivial _).symm

include hL hφ he in
/-- On a chart `X_{sᵢ} ∋ P`, the germ of `∑ aⱼ sⱼ` is `φ^#(∑ aⱼ xⱼ/xᵢ) · (sᵢ)_P`. -/
private theorem germ_linearSystemSection_eq {P : X} (i : Fin (n + 1))
    (hPU : P ∈ nonvanishingLocusOpens hL (s i))
    (hW : φ P ∈ projectiveSpaceChart n (Spec (CommRingCat.of k)) i) (a : Fin (n + 1) → k) :
    L.presheaf.germ ⊤ P trivial (linearSystemSection q s a) =
      φ.stalkMap P (∑ l, (projectiveSpaceOverScheme n _).presheaf.germ ⊤ (φ P) trivial
          (kConst (projectiveSpaceOverSchemeProjection n (Spec (CommRingCat.of k))) (a l)) *
        (projectiveSpaceOverScheme n _).presheaf.germ _ (φ P) hW
          (projectiveSpaceChartRatio n _ i l)) •
      L.presheaf.germ _ P hPU (L.presheaf.map (homOfLE le_top).op (s i)) := by
  have hsl : ∀ l, L.presheaf.germ ⊤ P trivial (s l) =
      φ.stalkMap P ((projectiveSpaceOverScheme n _).presheaf.germ _ (φ P) hW
        (projectiveSpaceChartRatio n _ i l)) •
        L.presheaf.germ _ P hPU (L.presheaf.map (homOfLE le_top).op (s i)) := by
    intro l
    calc L.presheaf.germ ⊤ P trivial (s l)
        = L.presheaf.germ _ P hPU (L.presheaf.map (homOfLE le_top).op (s l)) :=
          (TopCat.Presheaf.germ_res_apply L.presheaf (homOfLE le_top) P hPU _).symm
      _ = _ := by rw [← appLE_projectiveSpaceChartRatio_smul hL s φ e he i l]
      _ = _ := germ_smul_module L P hPU _ _
      _ = _ := by rw [germ_appLE_eq_stalkMap]
  simp only [linearSystemSection, map_sum, Finset.sum_smul, map_mul, mul_smul]
  refine Finset.sum_congr rfl fun l _ => ?_
  refine (germ_smul_module L (U := ⊤) P trivial _ _).trans ?_
  rw [hsl, ← kConstStalk_eq_stalkMap q φ hφ]
  rfl

include hL hφ he in
/-- **Separation of tangent vectors gives a surjection on cotangent spaces** (Hartshorne II,
proof of Proposition 7.3). If the subspace `V` spanned by the sections `sᵢ` defining
`φ : X ⟶ ℙⁿ_k` separates tangent vectors, then for every closed point `P` the local map
`φ^# : 𝒪_{ℙⁿ, φ(P)} → 𝒪_{X,P}` induces a surjection `𝔪_{φ(P)} → 𝔪_P / 𝔪_P²`: on a chart
`X_{sᵢ} ∋ P`, a section `∑ aⱼ sⱼ` of `V` is `φ^#(∑ aⱼ xⱼ/xᵢ) · sᵢ`. -/
theorem maximalIdealToCotangent_surjective_of_sectionsSeparateTangentVectors
    (htan : SectionsSeparateTangentVectors q (linearSystem q s)) {P : X} (hP : IsClosed {P}) :
    letI := (φ.stalkMap P).hom.toAlgebra
    haveI : IsLocalHom (algebraMap
        ((projectiveSpaceOverScheme n (Spec (CommRingCat.of k))).presheaf.stalk (φ P))
        (X.presheaf.stalk P)) :=
      inferInstanceAs (IsLocalHom (φ.stalkMap P).hom)
    Function.Surjective (maximalIdealToCotangent
      ((projectiveSpaceOverScheme n (Spec (CommRingCat.of k))).presheaf.stalk (φ P))
      (X.presheaf.stalk P)) := by
  let _ := (φ.stalkMap P).hom.toAlgebra
  let π := projectiveSpaceOverSchemeProjection n (Spec (CommRingCat.of k))
  let f := (φ.stalkMap P).hom
  -- A chart `X_{sᵢ} = φ⁻¹(D₊(xᵢ))` containing `P`.
  obtain ⟨i, hi⟩ := exists_mem_chartPreimage φ P
  have hW : φ P ∈ projectiveSpaceChart n (Spec (CommRingCat.of k)) i := hi
  have hPU : P ∈ nonvanishingLocusOpens hL (s i) := by
    rw [← preimage_projectiveSpaceChart_eq_nonvanishingLocusOpens hL s φ e he i]
    exact hW
  have hε := isTrivializingSection_nonvanishingLocusOpens hL (s i)
  let εP := L.presheaf.germ _ P hPU (L.presheaf.map (homOfLE le_top).op (s i))
  -- The germ of `∑ aⱼ xⱼ/xᵢ` at `φ(P)`.
  let lam : (Fin (n + 1) → k) → (projectiveSpaceOverScheme n _).presheaf.stalk (φ P) := fun a =>
    ∑ l, (projectiveSpaceOverScheme n _).presheaf.germ ⊤ (φ P) trivial (kConst π (a l)) *
      (projectiveSpaceOverScheme n _).presheaf.germ _ (φ P) hW (projectiveSpaceChartRatio n _ i l)
  have hconst : ∀ c : k, kConstStalk q P c =
      f ((projectiveSpaceOverScheme n _).presheaf.germ ⊤ (φ P) trivial (kConst π c)) :=
    kConstStalk_eq_stalkMap q φ hφ P
  have hgerm : ∀ a, L.presheaf.germ ⊤ P trivial (linearSystemSection q s a) =
      f (lam a) • εP :=
    germ_linearSystemSection_eq q hL s φ hφ e he i hPU hW
  intro ω
  obtain ⟨⟨b, hb⟩, rfl⟩ := (IsLocalRing.maximalIdeal (X.presheaf.stalk P)).toCotangent_surjective ω
  have hz : b • εP ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk P) •
      (⊤ : Submodule (X.presheaf.stalk P) (L.presheaf.stalk P)) :=
    Submodule.smul_mem_smul hb Submodule.mem_top
  obtain ⟨m, c, t, ht, hrest⟩ := htan P hP _ hz
  choose a ha using fun j => (ht j).1
  have hlam : ∀ j, lam (a j) ∈
      IsLocalRing.maximalIdeal ((projectiveSpaceOverScheme n _).presheaf.stalk (φ P)) := by
    intro j
    have h1 := (ht j).2
    rw [← ha j, hgerm, smul_germ_mem_smul_top_iff hε hPU] at h1
    by_contra h
    exact (IsLocalRing.mem_maximalIdeal _).mp h1
      (((IsLocalRing.notMem_maximalIdeal).mp h).map f)
  let α := ∑ j, (projectiveSpaceOverScheme n _).presheaf.germ ⊤ (φ P) trivial (kConst π (c j)) *
    lam (a j)
  have hα : α ∈ IsLocalRing.maximalIdeal ((projectiveSpaceOverScheme n _).presheaf.stalk (φ P)) :=
    Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hlam j)
  refine ⟨⟨α, hα⟩, ?_⟩
  have hsum : ∑ j, kConstStalk q P (c j) • L.presheaf.germ ⊤ P trivial (t j) =
      f α • εP := by
    simp only [← ha, hgerm, hconst, smul_smul, ← map_mul, ← Finset.sum_smul, ← map_sum, α]
  rw [hsum, ← sub_smul, smul_germ_mem_smul_top_iff hε hPU] at hrest
  have key : f α - b ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk P) ^ 2 := by
    have := (IsLocalRing.maximalIdeal (X.presheaf.stalk P) ^ 2).neg_mem hrest
    rwa [neg_sub] at this
  exact (Ideal.toCotangent_eq _).mpr key

end Tangents


/-! ### Residue fields at closed points -/

section ResidueFields

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
  (q : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType q]

/-- The identification `κ(P) ≅ k` at a closed point is evaluation of constants. -/
private theorem residueFieldIsoBase_inv_eq (P : X) (hP : IsClosed {P}) :
    (residueFieldIsoBase q P hP).inv =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ q.appTop ≫ X.Γevaluation P := by
  have h := congrArg (fun g => g.appTop ≫ (Scheme.ΓSpecIso (X.residueField P)).hom)
    (SpecMap_residueFieldIsoBase_inv q P hP)
  simp only [Scheme.ΓSpecIso_naturality, Scheme.Hom.comp_appTop, Scheme.fromSpecResidueField,
    Category.assoc, Scheme.fromSpecStalk_appTop] at h
  rw [← Iso.eq_inv_comp] at h
  rw [h]
  simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.inv_hom_id_assoc]
  rfl

variable {n : ℕ} (φ : X ⟶ projectiveSpaceOverScheme n (Spec (CommRingCat.of k)))
  (hφ : φ ≫ projectiveSpaceOverSchemeProjection n _ = q)

include hφ in
/-- **The residue fields agree at closed points** (Hartshorne II, proof of Proposition 7.3). For a
`k`-morphism `φ : X ⟶ ℙⁿ_k` with `X` locally of finite type over an algebraically closed field
`k`, the map of residue fields `κ(φ(P)) → κ(P)` is bijective at every closed point `P`: both
contain `k`, and `κ(P) = k`. -/
theorem residueField_map_bijective_of_isClosed {P : X} (hP : IsClosed {P}) :
    letI := (φ.stalkMap P).hom.toAlgebra
    haveI : IsLocalHom (algebraMap
        ((projectiveSpaceOverScheme n (Spec (CommRingCat.of k))).presheaf.stalk (φ P))
        (X.presheaf.stalk P)) :=
      inferInstanceAs (IsLocalHom (φ.stalkMap P).hom)
    Function.Bijective (IsLocalRing.ResidueField.map (algebraMap
      ((projectiveSpaceOverScheme n (Spec (CommRingCat.of k))).presheaf.stalk (φ P))
      (X.presheaf.stalk P))) := by
  let _ := (φ.stalkMap P).hom.toAlgebra
  refine ⟨RingHom.injective _, fun z => ?_⟩
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (residueFieldIsoBase q P hP).inv).2 z
  refine ⟨(projectiveSpaceOverScheme n _).Γevaluation (φ P)
    ((projectiveSpaceOverSchemeProjection n _).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)), ?_⟩
  rw [residueFieldIsoBase_inv_eq, CommRingCat.comp_apply, CommRingCat.comp_apply, ← hφ,
    Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  exact Scheme.Γevaluation_naturality_apply φ P _

end ResidueFields


/-! ### The local step: Lemma 7.4 at closed points -/

section LocalStep

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
  (q : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType q]
  {L : X.Modules} (hL : L.IsInvertible) {n : ℕ} (s : Fin (n + 1) → Γ(L, ⊤))
  (φ : X ⟶ projectiveSpaceOverScheme n (Spec (CommRingCat.of k)))
  (hφ : φ ≫ projectiveSpaceOverSchemeProjection n _ = q)
  (e : (Scheme.Modules.pullback φ).obj (projectiveSpaceTwistingSheaf n _ 1) ≅ L)
  (he : ∀ i, e.hom.app ⊤ (pullbackGlobalSection φ (projectiveSpaceCoordinate n _ i)) = s i)

include hL hφ he in
/-- **The stalk maps are surjective at closed points, given finiteness** (Hartshorne II, proof of
Proposition 7.3, via Lemma 7.4). Let `X` be locally of finite type over an algebraically closed
field `k`, and let the subspace `V` spanned by the sections `sᵢ` defining `φ : X ⟶ ℙⁿ_k` separate
tangent vectors. If `𝒪_{X,P}` is a finite `𝒪_{ℙⁿ, φ(P)}`-module at a closed point `P`, then
`φ^# : 𝒪_{ℙⁿ, φ(P)} → 𝒪_{X,P}` is surjective: the residue fields agree and `𝔪_{φ(P)}` surjects
onto `𝔪_P / 𝔪_P²`. -/
theorem stalkMap_surjective_of_sectionsSeparateTangentVectors
    (htan : SectionsSeparateTangentVectors q (linearSystem q s)) {P : X} (hP : IsClosed {P})
    (hfin : letI := (φ.stalkMap P).hom.toAlgebra
      Module.Finite ((projectiveSpaceOverScheme n (Spec (CommRingCat.of k))).presheaf.stalk (φ P))
        (X.presheaf.stalk P)) :
    Function.Surjective (φ.stalkMap P) := by
  let _ := (φ.stalkMap P).hom.toAlgebra
  have : IsLocalHom (algebraMap
      ((projectiveSpaceOverScheme n (Spec (CommRingCat.of k))).presheaf.stalk (φ P))
      (X.presheaf.stalk P)) :=
    inferInstanceAs (IsLocalHom (φ.stalkMap P).hom)
  have : IsProper (projectiveSpaceOverSchemeProjection n (Spec (CommRingCat.of k))) :=
    projectiveSpaceOverSchemeProjection_isProper n _
  have : IsLocallyNoetherian (projectiveSpaceOverScheme n (Spec (CommRingCat.of k))) :=
    LocallyOfFiniteType.isLocallyNoetherian (projectiveSpaceOverSchemeProjection n _)
  exact localRingHom_surjective_of_residueField_bijective_of_cotangent_surjective _ _
    (residueField_map_bijective_of_isClosed q φ hφ hP)
    (maximalIdealToCotangent_surjective_of_sectionsSeparateTangentVectors q hL s φ hφ e he htan hP)

end LocalStep


/-! ### Assembling: `φ` is a closed immersion, given finiteness of the local rings -/

section Assembly

/-- Surjectivity of a stalk map at a point `P` propagates to every generization `x ⤳ P`: the stalk
`𝒪_{X,x}` is a localization of `Γ(U, 𝒪_X)` for an affine open `U ∋ P`. -/
private theorem stalkMap_surjective_of_specializes {X Y : Scheme.{u}} (f : X ⟶ Y) {x P : X}
    (h : x ⤳ P) (hP : Function.Surjective (f.stalkMap P)) : Function.Surjective (f.stalkMap x) := by
  obtain ⟨U, hU, hPU, -⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (show P ∈ ⊤ from trivial)
  have hxU : x ∈ U := h.mem_open U.isOpen hPU
  let _ : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
  have hloc := hU.isLocalization_stalk ⟨x, hxU⟩
  have key : ∀ (c : Γ(X, U)) (b : Y.presheaf.stalk (f P)),
      f.stalkMap P b = X.presheaf.germ U P hPU c →
      f.stalkMap x (Y.presheaf.stalkSpecializes (f.base.hom.map_specializes h) b) =
        X.presheaf.germ U x hxU c := by
    intro c b hb
    rw [Scheme.Hom.stalkSpecializes_stalkMap_apply, hb,
      TopCat.Presheaf.germ_stalkSpecializes_apply]
    exact h
  intro y
  obtain ⟨⟨r, t⟩, hrt⟩ :=
    IsLocalization.surj (M := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl) y
  obtain ⟨a, ha⟩ := hP (X.presheaf.germ U P hPU r)
  obtain ⟨a', ha'⟩ := hP (X.presheaf.germ U P hPU t)
  have hr := key r a ha
  have ht := key t a' ha'
  have htu : IsUnit (X.presheaf.germ U x hxU t) :=
    IsLocalization.map_units (M := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl) _ t
  rw [← ht] at htu
  have hu := isUnit_of_map_unit (f.stalkMap x).hom _ htu
  refine ⟨Y.presheaf.stalkSpecializes (f.base.hom.map_specializes h) a * ↑hu.unit⁻¹, ?_⟩
  rw [map_mul, hr]
  have hrt' : y * X.presheaf.germ U x hxU t = X.presheaf.germ U x hxU r := hrt
  rw [← hrt', ← ht, mul_assoc, ← map_mul, IsUnit.mul_val_inv, map_one, mul_one]

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
  (q : X ⟶ Spec (CommRingCat.of k))
  {L : X.Modules} (hL : L.IsInvertible) {n : ℕ} (s : Fin (n + 1) → Γ(L, ⊤))
  (φ : X ⟶ projectiveSpaceOverScheme n (Spec (CommRingCat.of k)))
  (hφ : φ ≫ projectiveSpaceOverSchemeProjection n _ = q)
  (e : (Scheme.Modules.pullback φ).obj (projectiveSpaceTwistingSheaf n _ 1) ≅ L)
  (he : ∀ i, e.hom.app ⊤ (pullbackGlobalSection φ (projectiveSpaceCoordinate n _ i)) = s i)

include hL hφ he in
/-- **Hartshorne II, Proposition 7.3, (⇐), given finiteness of the local rings.** Let `X` be
projective over an algebraically closed field `k`, and let the subspace `V` spanned by the
sections `sᵢ` defining `φ : X ⟶ ℙⁿ_k` separate points and tangent vectors. If `𝒪_{X,P}` is a
finite `𝒪_{ℙⁿ, φ(P)}`-module at every closed point `P` (Hartshorne deduces this from the coherence
of `φ_* 𝒪_X`, Corollary 5.20), then `φ` is a closed immersion. -/
theorem isClosedImmersion_of_sectionsSeparatePoints_of_moduleFinite (hX : Projective q)
    (hsep : SectionsSeparatePoints (linearSystem q s))
    (htan : SectionsSeparateTangentVectors q (linearSystem q s))
    (hfin : ∀ P : X, IsClosed {P} → letI := (φ.stalkMap P).hom.toAlgebra
      Module.Finite ((projectiveSpaceOverScheme n (Spec (CommRingCat.of k))).presheaf.stalk (φ P))
        (X.presheaf.stalk P)) :
    IsClosedImmersion φ := by
  have : IsProper q := hX.isProper
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace q
  have hemb := isClosedEmbedding_of_sectionsSeparatePoints q s φ hφ e he hX hsep
  refine @IsClosedImmersion.mk _ _ φ ⟨fun x => ?_⟩ hemb
  obtain ⟨P, hP, hPc⟩ := nonempty_inter_closedPoints (Z := closure {x})
    ⟨x, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
  exact stalkMap_surjective_of_specializes φ (specializes_iff_mem_closure.mpr hP)
    (stalkMap_surjective_of_sectionsSeparateTangentVectors q hL s φ hφ e he htan hPc (hfin P hPc))

end Assembly


/-! ### Finiteness of the local rings, via Corollary 5.20 -/

section Finiteness

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The germ maps `Γ(f⁻¹V, 𝒪_X) → 𝒪_{X,x}`, as a cocone over the neighbourhoods of `f(x)` in the
abelian presheaf underlying `f_* 𝒪_X`. -/
private def pushforwardStalkCocone (x : X) :
    Cocone ((OpenNhds.inclusion (f x)).op ⋙
      ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)).presheaf) where
  pt := AddCommGrpCat.of (X.presheaf.stalk x)
  ι :=
    { app := fun V ↦ AddCommGrpCat.ofHom
        (X.presheaf.germ (f ⁻¹ᵁ V.unop.1) x V.unop.2).hom.toAddMonoidHom
      naturality := fun V W i ↦ by
        ext s
        exact X.presheaf.germ_res_apply
          ((Opens.map f.base).map ((OpenNhds.inclusion (f x)).map i.unop)) x W.unop.2 s }

/-- The map `(f_* 𝒪_X)_{f(x)} → 𝒪_{X,x}` sending the germ of a section over `V` to its germ. -/
private def pushforwardStalkToStalk (x : X) :
    ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)).presheaf.stalk
      (f x) →+ X.presheaf.stalk x :=
  (colimit.desc _ (pushforwardStalkCocone f x)).hom

private theorem pushforwardStalkToStalk_germ (x : X) (V : Y.Opens) (hx : f x ∈ V)
    (s : Γ(X, f ⁻¹ᵁ V)) :
    pushforwardStalkToStalk f x
        (((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)).presheaf.germ
          V (f x) hx s) =
      X.presheaf.germ (f ⁻¹ᵁ V) x hx s :=
  colimit.ι_desc_apply (C := AddCommGrpCat.{u}) (pushforwardStalkCocone f x)
    (op (⟨V, hx⟩ : OpenNhds (f x))) s

private theorem pushforwardStalkToStalk_smul (x : X) (r : Y.presheaf.stalk (f x))
    (m : ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)).presheaf.stalk
      (f x)) :
    pushforwardStalkToStalk f x (r • m) = f.stalkMap x r * pushforwardStalkToStalk f x m := by
  induction r, m using FreeLocusAux.stalk_smul_induction (f x) with
  | h V hx t s =>
    rw [← schemeModules_germ_smul]
    erw [pushforwardStalkToStalk_germ f x V hx (t • s), pushforwardStalkToStalk_germ f x V hx s]
    rw [Scheme.Hom.germ_stalkMap_apply]
    exact map_mul (X.presheaf.germ _ x hx).hom (f.app V t) s

/-- For a topological embedding `f`, every germ at `x` comes from `f_* 𝒪_X`. -/
private theorem pushforwardStalkToStalk_surjective (hf : Topology.IsInducing f) (x : X) :
    Function.Surjective (pushforwardStalkToStalk f x) := by
  intro b
  obtain ⟨W, hxW, τ, rfl⟩ := X.presheaf.exists_germ_eq b
  obtain ⟨V, hV, hVW⟩ := hf.isOpen_iff.mp W.isOpen
  let V' : Y.Opens := ⟨V, hV⟩
  have hle : f ⁻¹ᵁ V' ≤ W := fun y hy => by
    change y ∈ (W : Set X)
    rw [← hVW]
    exact hy
  have hx : f x ∈ V' := by
    change x ∈ f ⁻¹' V
    rw [hVW]
    exact hxW
  exact ⟨_, (pushforwardStalkToStalk_germ f x V' hx (X.presheaf.map (homOfLE hle).op τ)).trans
    (X.presheaf.germ_res_apply (homOfLE hle) x hx τ)⟩

variable {k : Type u} [Field k] (q : X ⟶ Spec (CommRingCat.of k))
  {L : X.Modules} {n : ℕ} (s : Fin (n + 1) → Γ(L, ⊤))
  (φ : X ⟶ projectiveSpaceOverScheme n (Spec (CommRingCat.of k)))
  (hφ : φ ≫ projectiveSpaceOverSchemeProjection n _ = q)
  (e : (Scheme.Modules.pullback φ).obj (projectiveSpaceTwistingSheaf n _ 1) ≅ L)
  (he : ∀ i, e.hom.app ⊤ (pullbackGlobalSection φ (projectiveSpaceCoordinate n _ i)) = s i)

include hφ he in
/-- **The local rings are finite** (Hartshorne II, proof of Proposition 7.3). Let `X` be
projective over `k`, and let the subspace `V` spanned by the sections `sᵢ` defining
`φ : X ⟶ ℙⁿ_k` separate points. Then for every point `P`, `𝒪_{X,P}` is a finite
`𝒪_{ℙⁿ, φ(P)}`-module: `φ_* 𝒪_X` is coherent (Corollary 5.20), and since `φ` is a homeomorphism
onto its image, its stalk at `φ(P)` maps onto `𝒪_{X,P}`. -/
theorem moduleFinite_stalk_of_sectionsSeparatePoints (hX : Projective q)
    (hsep : SectionsSeparatePoints (linearSystem q s)) (P : X) :
    letI := (φ.stalkMap P).hom.toAlgebra
    Module.Finite ((projectiveSpaceOverScheme n (Spec (CommRingCat.of k))).presheaf.stalk (φ P))
      (X.presheaf.stalk P) := by
  let _ := (φ.stalkMap P).hom.toAlgebra
  have : IsProper (projectiveSpaceOverSchemeProjection n (Spec (CommRingCat.of k))) :=
    projectiveSpaceOverSchemeProjection_isProper n _
  have hproj : Projective φ :=
    Projective.of_comp φ (projectiveSpaceOverSchemeProjection n _) (by rw [hφ]; exact hX)
  have hM := isCoherent_pushforward_of_projective_of_locallyOfFiniteType k
    (projectiveSpaceOverSchemeProjection n _) φ hproj _ (isCoherent_structureSheafModule X)
  have := finite_stalk_of_isCoherent _ hM (φ P)
  let Ψ : ((Scheme.Modules.pushforward φ).obj (SheafOfModules.unit X.ringCatSheaf)).presheaf.stalk
      (φ P) →ₗ[(projectiveSpaceOverScheme n (Spec (CommRingCat.of k))).presheaf.stalk (φ P)]
      X.presheaf.stalk P :=
    { toFun := pushforwardStalkToStalk φ P
      map_add' := map_add _
      map_smul' := fun r m => pushforwardStalkToStalk_smul φ P r m }
  exact Module.Finite.of_surjective Ψ (pushforwardStalkToStalk_surjective φ
    (isClosedEmbedding_of_sectionsSeparatePoints q s φ hφ e he hX hsep).isInducing P)

end Finiteness


/-! ### Proposition 7.3, (⇐) -/

section Converse

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
  (q : X ⟶ Spec (CommRingCat.of k))
  {L : X.Modules} (hL : L.IsInvertible) {n : ℕ} (s : Fin (n + 1) → Γ(L, ⊤))
  (φ : X ⟶ projectiveSpaceOverScheme n (Spec (CommRingCat.of k)))
  (hφ : φ ≫ projectiveSpaceOverSchemeProjection n _ = q)
  (e : (Scheme.Modules.pullback φ).obj (projectiveSpaceTwistingSheaf n _ 1) ≅ L)
  (he : ∀ i, e.hom.app ⊤ (pullbackGlobalSection φ (projectiveSpaceCoordinate n _ i)) = s i)

include hL hφ he in
/-- **Hartshorne II, Proposition 7.3, (⇐).** Let `X` be projective over an algebraically closed
field `k`, and let `φ : X ⟶ ℙⁿ_k` be the morphism defined by global sections `s₀, …, sₙ` of an
invertible sheaf `L` (an isomorphism `φ^* 𝒪(1) ≅ L` carrying each `φ^* xᵢ` to `sᵢ`). If the
subspace `V` spanned by the `sᵢ` separates points and tangent vectors, then `φ` is a closed
immersion. -/
theorem isClosedImmersion_of_sectionsSeparatePoints_of_sectionsSeparateTangentVectors
    (hX : Projective q) (hsep : SectionsSeparatePoints (linearSystem q s))
    (htan : SectionsSeparateTangentVectors q (linearSystem q s)) :
    IsClosedImmersion φ :=
  isClosedImmersion_of_sectionsSeparatePoints_of_moduleFinite q hL s φ hφ e he hX hsep htan
    fun P _ => moduleFinite_stalk_of_sectionsSeparatePoints q s φ hφ e he hX hsep P

end Converse


/-! ### Proposition 7.3, (⇒): separation of points -/

section ForwardPoints

variable {k : Type u} [Field k] {n : ℕ}

/-- **Homogeneous coordinates of a `k`-point.** A `k`-point `σ` of `ℙⁿ_k` lying in `D₊(xⱼ)` is the
point `(a₀ : ⋯ : aₙ)` for some `a` with `aⱼ = 1`: on `Spec k` the section `σ^* xⱼ` trivializes
`σ^* 𝒪(1)`, and `σ^* xᵢ = aᵢ σ^* xⱼ`. -/
private theorem exists_eq_projectivePoint
    (σ : Spec (CommRingCat.of k) ⟶ projectiveSpaceOverScheme n (Spec (CommRingCat.of k)))
    (hσ : σ ≫ projectiveSpaceOverSchemeProjection n _ = 𝟙 _) (j : Fin (n + 1))
    (y : Spec (CommRingCat.of k)) (hj : σ y ∈ projectiveSpaceChart n _ j) :
    ∃ (a : Fin (n + 1) → k) (ha : a ≠ 0), a j = 1 ∧ σ = projectivePoint k a ha := by
  set M := (Scheme.Modules.pullback σ).obj (projectiveSpaceTwistingSheaf n _ 1)
  set t : Fin (n + 1) → Γ(M, ⊤) := fun i =>
    pullbackGlobalSection σ (projectiveSpaceCoordinate n _ i)
  have hM : M.IsInvertible := isInvertible_pullback_projectiveSpaceTwistingSheaf σ
  have hpre : σ ⁻¹ᵁ projectiveSpaceChart n _ j = nonvanishingLocusOpens hM (t j) :=
    preimage_projectiveSpaceChart_eq_nonvanishingLocusOpens hM t σ (Iso.refl _) (fun _ => rfl) j
  have hall : ∀ y', y' ∈ nonvanishingLocus M (t j) := by
    intro y'
    obtain rfl : y' = y := Subsingleton.elim (α := PrimeSpectrum k) _ _
    have : y' ∈ σ ⁻¹ᵁ projectiveSpaceChart n _ j := hj
    rw [hpre] at this
    exact this
  have htriv : IsTrivializingSection M ⊤ (t j) :=
    IsTrivializingSection.of_local fun y' _ => ⟨nonvanishingLocusOpens hM (t j),
      le_top, hall y', isTrivializingSection_nonvanishingLocusOpens hM _⟩
  choose r hr using fun i => htriv.exists_eq_smul (t i)
  have hr' : ∀ i, t i = r i • t j := fun i => by rw [← hr i, map_homOfLE_top]
  have hrj : r j = 1 := by
    have h := (htriv ⊤ le_rfl).1 (a₁ := r j) (a₂ := 1)
    simp only [map_homOfLE_top, one_smul] at h
    exact h (hr' j).symm
  let a : Fin (n + 1) → k := fun i => (Scheme.ΓSpecIso (CommRingCat.of k)).hom (r i)
  have haj : a j = 1 := by
    simp only [a, hrj, map_one]
  have ha : a ≠ 0 := fun h => one_ne_zero (haj.symm.trans (congrFun h j))
  have hu := isTrivializingSection_structureModuleSection_one (Spec (CommRingCat.of k))
  have e₁ : PUnit.{u + 1} ≃ ULift.{u} (Fin 1) := Equiv.ofUnique _ _
  obtain ⟨α, hα⟩ := Ringed.exists_iso_of_frames (R := (Spec (CommRingCat.of k)).sheaf)
    (fun _ : PUnit.{u + 1} => ⊤) (le_iSup (fun _ : PUnit.{u + 1} => ⊤) PUnit.unit)
    (A := M) (B := structureModuleOf (Spec (CommRingCat.of k)))
    (fun _ => t j) (fun _ => structureModuleSection _ 1)
    (fun _ => (isLocalFrame_of_isTrivializingSection htriv).reindex e₁)
    (fun _ => (isLocalFrame_of_isTrivializingSection hu).reindex e₁)
    (fun _ _ => ⟨1, by rw [one_smul], by rw [one_smul]⟩)
  let α' : M ≅ structureModuleOf (Spec (CommRingCat.of k)) := α
  have hα' : α'.hom.app ⊤ (t j) = structureModuleSection _ 1 := hα PUnit.unit
  have hsec : ∀ i, α'.hom.app ⊤ (pullbackGlobalSection σ (projectiveSpaceCoordinate n _ i)) =
      pointSections k a i := by
    intro i
    change α'.hom.app ⊤ (t i) = _
    rw [hr' i, Scheme.Modules.Hom.app_smul, hα', ← structureModuleSection_eq_smul]
    change structureModuleSection _ (r i) =
      structureModuleSection _ ((Scheme.ΓSpecIso (CommRingCat.of k)).inv
        ((Scheme.ΓSpecIso (CommRingCat.of k)).hom (r i)))
    rw [← CommRingCat.comp_apply, Iso.hom_inv_id]
    rfl
  exact ⟨a, ha, haj, eq_projectivePoint ha hσ α' hsec⟩

variable [IsAlgClosed k] {X : Scheme.{u}} (q : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType q]
  {L : X.Modules} (hL : L.IsInvertible) (s : Fin (n + 1) → Γ(L, ⊤))
  (φ : X ⟶ projectiveSpaceOverScheme n (Spec (CommRingCat.of k)))
  (hφ : φ ≫ projectiveSpaceOverSchemeProjection n _ = q)
  (e : (Scheme.Modules.pullback φ).obj (projectiveSpaceTwistingSheaf n _ 1) ≅ L)
  (he : ∀ i, e.hom.app ⊤ (pullbackGlobalSection φ (projectiveSpaceCoordinate n _ i)) = s i)

include hL hφ he in
/-- **Hartshorne II, Proposition 7.3, (⇒), for points.** Let `X` be locally of finite type over
an algebraically closed field `k`, and let `φ : X ⟶ ℙⁿ_k` be defined by the sections `sᵢ`. If
`φ` is injective (for instance a closed immersion), the subspace `V` spanned by the `sᵢ` separates
points: the closed points `φ(P) ≠ φ(Q)` are `k`-points, so some hyperplane contains exactly one of
them, and its pullback is a section of `V` vanishing at exactly one of `P`, `Q`. -/
theorem sectionsSeparatePoints_of_injective (hinj : Function.Injective φ) :
    SectionsSeparatePoints (linearSystem q s) := by
  intro P Q hP hQ hPQ
  let σP := pointOfClosedPoint q P hP ≫ φ
  let σQ := pointOfClosedPoint q Q hQ ≫ φ
  have hσP : σP ≫ projectiveSpaceOverSchemeProjection n _ = 𝟙 _ := by
    simp only [σP, Category.assoc, hφ, pointOfClosedPoint_comp]
  have hσQ : σQ ≫ projectiveSpaceOverSchemeProjection n _ = 𝟙 _ := by
    simp only [σQ, Category.assoc, hφ, pointOfClosedPoint_comp]
  have hσP_apply : ∀ y, σP y = φ P := fun y => by
    simp only [σP, Scheme.Hom.comp_apply, pointOfClosedPoint_apply]
  have hσQ_apply : ∀ y, σQ y = φ Q := fun y => by
    simp only [σQ, Scheme.Hom.comp_apply, pointOfClosedPoint_apply]
  let y₀ : Spec (CommRingCat.of k) := IsLocalRing.closedPoint k
  obtain ⟨j, hj⟩ := exists_mem_chartPreimage φ P
  have hjP : φ P ∈ projectiveSpaceChart n _ j := hj
  have hsj : ∀ x, x ∈ nonvanishingLocus L (s j) ↔ φ x ∈ projectiveSpaceChart n _ j := fun x => by
    change x ∈ nonvanishingLocusOpens hL (s j) ↔ x ∈ φ ⁻¹ᵁ projectiveSpaceChart n _ j
    rw [preimage_projectiveSpaceChart_eq_nonvanishingLocusOpens hL s φ e he j]
  by_cases hjQ : φ Q ∈ projectiveSpaceChart n _ j
  · obtain ⟨a, ha, haj, hσa⟩ :=
      exists_eq_projectivePoint σP hσP j y₀ (by rw [hσP_apply]; exact hjP)
    obtain ⟨b, hb, hbj, hσb⟩ :=
      exists_eq_projectivePoint σQ hσQ j y₀ (by rw [hσQ_apply]; exact hjQ)
    have hab : a ≠ b := by
      rintro rfl
      exact hPQ (hinj (by rw [← hσP_apply y₀, ← hσQ_apply y₀, hσa, hσb]))
    obtain ⟨l, hl⟩ := Function.ne_iff.mp hab
    let v : Fin (n + 1) → k := Pi.single l 1 - a l • Pi.single j 1
    refine ⟨linearSystemSection q s v, ⟨v, rfl⟩, Or.inl ⟨?_, ?_⟩⟩
    · rw [germ_mem_maximalIdeal_smul_top_iff,
        mem_nonvanishingLocus_linearSystemSection_iff q s φ hφ e he,
        ← hσP_apply y₀, hσa, projectivePoint_mem_nonvanishingLocus_linearSection_iff, not_not]
      simp [v, sub_dotProduct, smul_dotProduct, single_dotProduct, haj]
    · rw [germ_mem_maximalIdeal_smul_top_iff, not_not,
        mem_nonvanishingLocus_linearSystemSection_iff q s φ hφ e he,
        ← hσQ_apply y₀, hσb, projectivePoint_mem_nonvanishingLocus_linearSection_iff]
      simpa [v, sub_dotProduct, smul_dotProduct, single_dotProduct, hbj, sub_eq_zero] using hl.symm
  · refine ⟨s j, mem_linearSystem q s j, Or.inr ⟨?_, ?_⟩⟩
    · rw [germ_mem_maximalIdeal_smul_top_iff, hsj]
      exact hjQ
    · rw [germ_mem_maximalIdeal_smul_top_iff, not_not, hsj]
      exact hjP

end ForwardPoints


/-! ### Proposition 7.3, (⇒): separation of tangent vectors -/

section ForwardTangents

/-- The ratio `xⱼ/xⱼ` on `D₊(xⱼ)` is `1`. -/
private theorem projectiveSpaceChartRatio_self (n : ℕ) (Y : Scheme.{u}) (j : Fin (n + 1)) :
    projectiveSpaceChartRatio n Y j j = 1 := by
  rw [projectiveSpaceChartRatio, ratioInt, chartRatio_self, map_one, map_one]
  rfl

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- At a closed point of a scheme locally of finite type over an algebraically closed field `k`,
every element of the local ring is congruent to a constant modulo the maximal ideal. -/
private theorem exists_sub_const_mem_maximalIdeal {Z : Scheme.{u}}
    (p : Z ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] {z : Z} (hz : IsClosed {z})
    (a : Z.presheaf.stalk z) :
    ∃ c : k, a - Z.presheaf.germ ⊤ z trivial (kConst p c) ∈
      IsLocalRing.maximalIdeal (Z.presheaf.stalk z) := by
  obtain ⟨c, hc⟩ :=
    (ConcreteCategory.bijective_of_isIso (residueFieldIsoBase p z hz).inv).2
      (IsLocalRing.residue (Z.presheaf.stalk z) a)
  refine ⟨c, ?_⟩
  rw [residueFieldIsoBase_inv_eq, CommRingCat.comp_apply, CommRingCat.comp_apply] at hc
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
  exact hc.symm

variable {n : ℕ}

/-- **The maximal ideal at a closed point of `ℙⁿ_k`** (`k` algebraically closed). Let `z ∈ D₊(xⱼ)`
be closed, with coordinates `cₗ ∈ k`, `xₗ/xⱼ ≡ cₗ` modulo `𝔪_z`. Then modulo `𝔪_z²`, every element
of `𝔪_z` is a `k`-linear combination of the germs of `xₗ/xⱼ - cₗ`: the chart ring is generated by
the `xₗ/xⱼ` over `k`. -/
private theorem exists_sub_sum_mem_maximalIdeal_sq
    {z : projectiveSpaceOverScheme n (Spec (CommRingCat.of k))} (hz : IsClosed {z})
    (j : Fin (n + 1)) (hW : z ∈ projectiveSpaceChart n (Spec (CommRingCat.of k)) j)
    (α : (projectiveSpaceOverScheme n (Spec (CommRingCat.of k))).presheaf.stalk z)
    (hα : α ∈ IsLocalRing.maximalIdeal _) :
    ∃ c d : Fin (n + 1) → k,
      (∀ l, (projectiveSpaceOverScheme n _).presheaf.germ _ z hW
            (projectiveSpaceChartRatio n _ j l) -
          (projectiveSpaceOverScheme n _).presheaf.germ ⊤ z trivial
            (kConst (projectiveSpaceOverSchemeProjection n (Spec (CommRingCat.of k))) (c l)) ∈
        IsLocalRing.maximalIdeal _) ∧
      α - ∑ l, (projectiveSpaceOverScheme n _).presheaf.germ ⊤ z trivial
          (kConst (projectiveSpaceOverSchemeProjection n (Spec (CommRingCat.of k))) (d l)) *
        ((projectiveSpaceOverScheme n _).presheaf.germ _ z hW
            (projectiveSpaceChartRatio n _ j l) -
          (projectiveSpaceOverScheme n _).presheaf.germ ⊤ z trivial
            (kConst (projectiveSpaceOverSchemeProjection n (Spec (CommRingCat.of k))) (c l))) ∈
        IsLocalRing.maximalIdeal _ ^ 2 := by
  let Pn := projectiveSpaceOverScheme n (Spec (CommRingCat.of k))
  let π := projectiveSpaceOverSchemeProjection n (Spec (CommRingCat.of k))
  let W := projectiveSpaceChart n (Spec (CommRingCat.of k)) j
  have : IsProper π := projectiveSpaceOverSchemeProjection_isProper n _
  let κA : k →+* Pn.presheaf.stalk z := (Pn.presheaf.germ ⊤ z trivial).hom.comp (kConst π)
  let yA : Fin (n + 1) → Pn.presheaf.stalk z := fun l =>
    Pn.presheaf.germ W z hW (projectiveSpaceChartRatio n _ j l)
  choose c hc using fun l => exists_sub_const_mem_maximalIdeal π hz (yA l)
  let g : Fin (n + 1) → Pn.presheaf.stalk z := fun l => yA l - κA (c l)
  have hg : ∀ l, g l ∈ IsLocalRing.maximalIdeal _ := hc
  -- Every germ of a function on the chart is a constant plus a combination of the `g l`.
  have hdec : ∀ r : Γ(Pn, W), ∃ (κ : k) (w : Fin (n + 1) → Pn.presheaf.stalk z),
      Pn.presheaf.germ W z hW r = κA κ + ∑ l, w l * g l := by
    intro r
    obtain ⟨p, rfl⟩ := projectiveSpaceChartPolynomialMap_surjective n _ j r
    induction p using MvPolynomial.induction_on with
    | C a =>
      refine ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).hom a, 0, ?_⟩
      simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
      rw [projectiveSpaceChartPolynomialMap, MvPolynomial.eval₂Hom_C]
      have hinv : (Scheme.ΓSpecIso (CommRingCat.of k)).inv
          ((Scheme.ΓSpecIso (CommRingCat.of k)).hom a) = a := by
        rw [← CommRingCat.comp_apply, Iso.hom_inv_id]
        rfl
      change Pn.presheaf.germ W z hW (π.appLE ⊤ W le_top a) =
        Pn.presheaf.germ ⊤ z trivial (π.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv
          ((Scheme.ΓSpecIso (CommRingCat.of k)).hom a)))
      rw [hinv]
      exact TopCat.Presheaf.germ_res_apply Pn.presheaf (homOfLE le_top) z hW (π.app ⊤ a)
    | add p₁ p₂ h₁ h₂ =>
      obtain ⟨κ₁, w₁, e₁⟩ := h₁
      obtain ⟨κ₂, w₂, e₂⟩ := h₂
      refine ⟨κ₁ + κ₂, w₁ + w₂, ?_⟩
      rw [map_add, map_add, e₁, e₂, map_add]
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      ring
    | mul_X p l h =>
      obtain ⟨κ₁, w₁, e₁⟩ := h
      refine ⟨κ₁ * c l, fun m => w₁ m * yA l + if m = l then κA κ₁ else 0, ?_⟩
      rw [map_mul, map_mul, e₁]
      have hX : Pn.presheaf.germ W z hW (projectiveSpaceChartPolynomialMap n _ j
          (MvPolynomial.X l)) = yA l := by
        rw [projectiveSpaceChartPolynomialMap, MvPolynomial.eval₂Hom_X']
      rw [hX]
      simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true, Finset.sum_mul, map_mul]
      simp only [g]
      ring_nf
  -- Write `α = r / u` with `r, u ∈ Γ(D₊(xⱼ), 𝒪)`, `u(z) ≠ 0`.
  have hWa : IsAffineOpen W := isAffineOpen_projectiveSpaceChart n _ j
  let _ : Algebra Γ(Pn, W) (Pn.presheaf.stalk z) :=
    TopCat.Presheaf.algebra_section_stalk Pn.presheaf ⟨z, hW⟩
  have hloc := hWa.isLocalization_stalk ⟨z, hW⟩
  obtain ⟨⟨r, u⟩, hru⟩ :=
    IsLocalization.surj (M := (hWa.primeIdealOf ⟨z, hW⟩).asIdeal.primeCompl) α
  have hu : IsUnit (Pn.presheaf.germ W z hW u) :=
    IsLocalization.map_units (M := (hWa.primeIdealOf ⟨z, hW⟩).asIdeal.primeCompl) _ u
  have hru' : α * Pn.presheaf.germ W z hW u = Pn.presheaf.germ W z hW r := hru
  obtain ⟨κ, w, hr⟩ := hdec r
  have hsum : ∑ l, w l * g l ∈ IsLocalRing.maximalIdeal (Pn.presheaf.stalk z) :=
    Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hg l)
  have hκ : κ = 0 := by
    by_contra hκ
    have h1 : Pn.presheaf.germ W z hW r ∈ IsLocalRing.maximalIdeal (Pn.presheaf.stalk z) :=
      hru' ▸ Ideal.mul_mem_right _ _ hα
    rw [hr] at h1
    have h2 := Ideal.sub_mem _ h1 hsum
    rw [add_sub_cancel_right] at h2
    exact (IsLocalRing.mem_maximalIdeal _).mp h2 ((IsUnit.mk0 κ hκ).map κA)
  have hαeq : α = ∑ l, (w l * ↑hu.unit⁻¹) * g l := by
    calc α = α * Pn.presheaf.germ W z hW u * ↑hu.unit⁻¹ := by
          rw [mul_assoc, IsUnit.mul_val_inv, mul_one]
      _ = (κA κ + ∑ l, w l * g l) * ↑hu.unit⁻¹ := by rw [hru', hr]
      _ = _ := by
          rw [hκ, map_zero, zero_add, Finset.sum_mul]
          exact Finset.sum_congr rfl fun l _ => by ring
  choose d hd using fun l => exists_sub_const_mem_maximalIdeal π hz (w l * ↑hu.unit⁻¹)
  refine ⟨c, d, hg, ?_⟩
  rw [hαeq, ← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun l _ => ?_
  rw [pow_two]
  convert Ideal.mul_mem_mul (hd l) (hg l) using 1
  simp only [g, κA, yA, RingHom.comp_apply]
  ring

variable {X : Scheme.{u}} (q : X ⟶ Spec (CommRingCat.of k))
  {L : X.Modules} (hL : L.IsInvertible) (s : Fin (n + 1) → Γ(L, ⊤))
  (φ : X ⟶ projectiveSpaceOverScheme n (Spec (CommRingCat.of k)))
  (hφ : φ ≫ projectiveSpaceOverSchemeProjection n _ = q)
  (e : (Scheme.Modules.pullback φ).obj (projectiveSpaceTwistingSheaf n _ 1) ≅ L)
  (he : ∀ i, e.hom.app ⊤ (pullbackGlobalSection φ (projectiveSpaceCoordinate n _ i)) = s i)

include hL hφ he in
/-- **Hartshorne II, Proposition 7.3, (⇒), for tangent vectors.** Let `k` be algebraically closed
and let `φ : X ⟶ ℙⁿ_k`, defined by the sections `sᵢ`, be a closed immersion. Then the subspace `V`
spanned by the `sᵢ` separates tangent vectors: `𝒪_{ℙⁿ, φ(P)} → 𝒪_{X,P}` is surjective, and modulo
`𝔪²` the maximal ideal at the `k`-point `φ(P) ∈ D₊(xᵢ)` is spanned by the linear functions
`xₗ/xᵢ - cₗ`, which pull back to the sections `sₗ - cₗ sᵢ` of `V` divided by `sᵢ`. -/
theorem sectionsSeparateTangentVectors_of_isClosedImmersion [IsClosedImmersion φ] :
    SectionsSeparateTangentVectors q (linearSystem q s) := by
  intro P hP z hz
  let π := projectiveSpaceOverSchemeProjection n (Spec (CommRingCat.of k))
  let f := (φ.stalkMap P).hom
  obtain ⟨i, hi⟩ := exists_mem_chartPreimage φ P
  have hW : φ P ∈ projectiveSpaceChart n (Spec (CommRingCat.of k)) i := hi
  have hPU : P ∈ nonvanishingLocusOpens hL (s i) := by
    rw [← preimage_projectiveSpaceChart_eq_nonvanishingLocusOpens hL s φ e he i]
    exact hW
  have hε := isTrivializingSection_nonvanishingLocusOpens hL (s i)
  obtain ⟨b, rfl⟩ := hε.exists_smul_germ_eq hPU z
  replace hz := (smul_germ_mem_smul_top_iff hε hPU _ b).mp hz
  obtain ⟨α, rfl⟩ := φ.stalkMap_surjective P b
  have hmap : ∀ a, a ∈ IsLocalRing.maximalIdeal
      ((projectiveSpaceOverScheme n (Spec (CommRingCat.of k))).presheaf.stalk (φ P)) →
      f a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk P) := fun a ha =>
    (IsLocalRing.mem_maximalIdeal _).mpr
      ((map_mem_nonunits_iff f a).mpr ((IsLocalRing.mem_maximalIdeal _).mp ha))
  have hα : α ∈ IsLocalRing.maximalIdeal
      ((projectiveSpaceOverScheme n (Spec (CommRingCat.of k))).presheaf.stalk (φ P)) := by
    by_contra h
    exact (IsLocalRing.mem_maximalIdeal _).mp hz (((IsLocalRing.notMem_maximalIdeal).mp h).map f)
  have hzc : IsClosed {φ P} := by
    simpa [Set.image_singleton] using φ.isClosedEmbedding.isClosedMap _ hP
  obtain ⟨c, d, hg, hrest⟩ := exists_sub_sum_mem_maximalIdeal_sq hzc i hW α hα
  have hlam : ∀ l, (∑ m, (projectiveSpaceOverScheme n _).presheaf.germ ⊤ (φ P) trivial
        (kConst π ((Pi.single l 1 - c l • Pi.single i 1 : Fin (n + 1) → k) m)) *
      (projectiveSpaceOverScheme n _).presheaf.germ _ (φ P) hW
        (projectiveSpaceChartRatio n _ i m)) =
      (projectiveSpaceOverScheme n _).presheaf.germ _ (φ P) hW
          (projectiveSpaceChartRatio n _ i l) -
        (projectiveSpaceOverScheme n _).presheaf.germ ⊤ (φ P) trivial (kConst π (c l)) := by
    intro l
    simp only [Pi.single_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero, map_sub, sub_mul, Finset.sum_sub_distrib]
    rw [Finset.sum_eq_single l (fun m _ hm => by simp [hm]) (by simp),
      Finset.sum_eq_single i (fun m _ hm => by simp [hm]) (by simp)]
    simp [projectiveSpaceChartRatio_self]
  have hsq : ∀ x ∈ IsLocalRing.maximalIdeal
      ((projectiveSpaceOverScheme n (Spec (CommRingCat.of k))).presheaf.stalk (φ P)) ^ 2,
      f x ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk P) ^ 2 := by
    intro x hx
    rw [pow_two] at hx ⊢
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun x y hx hy => ?_)
    · rw [map_mul]
      exact Ideal.mul_mem_mul (hmap a ha) (hmap b hb)
    · rw [map_add]
      exact add_mem hx hy
  refine ⟨n + 1, d, fun l => linearSystemSection q s (Pi.single l 1 - c l • Pi.single i 1),
    fun l => ⟨⟨_, rfl⟩, ?_⟩, ?_⟩
  · rw [germ_linearSystemSection_eq q hL s φ hφ e he i hPU hW, hlam]
    exact (smul_germ_mem_smul_top_iff hε hPU _ _).mpr (hmap _ (hg l))
  · have key := (smul_germ_mem_smul_top_iff hε hPU _ _).mpr (hsq _ hrest)
    simp only [map_sub, sub_smul, map_sum, Finset.sum_smul] at key
    convert key using 2
    · rfl
    · refine Finset.sum_congr rfl fun l _ => ?_
      rw [germ_linearSystemSection_eq q hL s φ hφ e he i hPU hW, hlam,
        kConstStalk_eq_stalkMap q φ hφ, smul_smul, ← map_mul]

end ForwardTangents


/-! ### Proposition 7.3 -/

section Main

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
  (q : X ⟶ Spec (CommRingCat.of k))
  {L : X.Modules} (hL : L.IsInvertible) {n : ℕ} (s : Fin (n + 1) → Γ(L, ⊤))
  (φ : X ⟶ projectiveSpaceOverScheme n (Spec (CommRingCat.of k)))
  (hφ : φ ≫ projectiveSpaceOverSchemeProjection n _ = q)
  (e : (Scheme.Modules.pullback φ).obj (projectiveSpaceTwistingSheaf n _ 1) ≅ L)
  (he : ∀ i, e.hom.app ⊤ (pullbackGlobalSection φ (projectiveSpaceCoordinate n _ i)) = s i)

include hL hφ he in
/-- **Hartshorne II, Proposition 7.3.** Let `X` be projective over an algebraically closed field
`k` (structure morphism `q`), and let `φ : X ⟶ ℙⁿ_k` be the morphism defined by global sections
`s₀, …, sₙ` of an invertible sheaf `L`, i.e. with an isomorphism `φ^* 𝒪(1) ≅ L` carrying each
`φ^* xᵢ` to `sᵢ` (Theorem 7.1; such `sᵢ` generate `L`). Let `V ⊆ Γ(X, L)` be the subspace spanned
by the `sᵢ`. Then `φ` is a closed immersion iff `V` separates points and separates tangent
vectors. -/
theorem isClosedImmersion_iff_sectionsSeparatePoints_and_sectionsSeparateTangentVectors
    (hX : Projective q) :
    IsClosedImmersion φ ↔ SectionsSeparatePoints (linearSystem q s) ∧
      SectionsSeparateTangentVectors q (linearSystem q s) := by
  refine ⟨fun h => ?_, fun h =>
    isClosedImmersion_of_sectionsSeparatePoints_of_sectionsSeparateTangentVectors
      q hL s φ hφ e he hX h.1 h.2⟩
  have : IsProper q := hX.isProper
  exact ⟨sectionsSeparatePoints_of_injective q hL s φ hφ e he φ.isClosedEmbedding.injective,
    sectionsSeparateTangentVectors_of_isClosedImmersion q hL s φ hφ e he⟩

end Main

end Hartshorne

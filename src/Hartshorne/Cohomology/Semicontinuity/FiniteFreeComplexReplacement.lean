/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.Flatness.FlatModulesShortExactCalculus
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Homology.Embedding.HomEquiv
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Homology.Localization
import Mathlib.Algebra.Homology.Refinements
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Replacing a bounded-above complex by finite free modules

Hartshorne, *Algebraic Geometry*, III.12, Lemma 12.3 (pp. 283–284).

Let `A` be a Noetherian ring and `C` a bounded-above cochain complex of `A`-modules (here:
`C.IsStrictlyLE n`, i.e. `C^i = 0` for `i > n`) whose cohomology modules are finitely
generated. We construct a bounded-above complex `L` of finitely generated free `A`-modules
with a quasi-isomorphism `L ⟶ C`. If moreover every term of `C` is flat, then for every
`A`-module `M` the induced map `L ⊗ M ⟶ C ⊗ M` (the functor `- ⊗_A M` applied degreewise)
is again a quasi-isomorphism.

The construction is carried out on the `ℕ`-indexed chain complex obtained by restricting `C`
along `ComplexShape.embeddingUpIntLE n`, by a descending recursion choosing at each step
finitely many generators of the cohomology and of the kernel of the cohomology map
(finiteness of the latter uses that `A` is Noetherian). The tensor statement is proved by
showing that the mapping cone, a bounded-above acyclic complex of flat modules, stays acyclic
after tensoring with `M`.
-/

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace Hartshorne

universe u

namespace FiniteFreeComplexReplacement

variable {A : Type u} [CommRing A]

lemma quasiIso_iff_acyclic_mappingCone {C : Type*} [Category C] [Abelian C]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    QuasiIso f ↔ (CochainComplex.mappingCone f).Acyclic := by
  rw [← HomologicalComplex.mem_quasiIso_iff, ← HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  exact (ObjectProperty.trW_iff_of_distinguished _ _
      (HomotopyCategory.mappingCone_triangleh_distinguished f)).trans
    (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _)

lemma exists_of_exactAt (X : CochainComplex (ModuleCat.{u} A) ℤ) {i j k : ℤ}
    (hij : i + 1 = j) (hjk : j + 1 = k) (hX : X.ExactAt j) (x : X.X j)
    (hx : X.d j k x = 0) : ∃ y : X.X i, X.d i j y = x := by
  subst hij hjk
  rw [X.exactAt_iff' i (i + 1) (i + 1 + 1) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff] at hX
  exact hX x hx

lemma exactAt_of_exists (X : CochainComplex (ModuleCat.{u} A) ℤ) {i j k : ℤ}
    (hij : i + 1 = j) (hjk : j + 1 = k)
    (h : ∀ x : X.X j, X.d j k x = 0 → ∃ y : X.X i, X.d i j y = x) : X.ExactAt j := by
  subst hij hjk
  rw [X.exactAt_iff' i (i + 1) (i + 1 + 1) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  exact h

lemma flat_of_subsingleton (M : Type*) [AddCommGroup M] [Module A M] [Subsingleton M] :
    Module.Flat A M := by
  have : Module.Free A M := Module.Free.of_subsingleton A M
  infer_instance

/-- The cycle module `ker (d^i)` of a cochain complex of modules. -/
abbrev cyc (X : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) : Submodule A (X.X i) :=
  LinearMap.ker (X.d i (i + 1)).hom

/-- The differential `d^i` with codomain restricted to `ker (d^(i+1))`. -/
noncomputable abbrev toCyc (X : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) :
    X.X i →ₗ[A] cyc X (i + 1) :=
  (X.d i (i + 1)).hom.codRestrict _ (fun x => by
    change (X.d i (i + 1) ≫ X.d (i + 1) (i + 1 + 1)) x = 0
    rw [X.d_comp_d]; rfl)

lemma toCyc_surjective (X : CochainComplex (ModuleCat.{u} A) ℤ) (hX : X.Acyclic) (i : ℤ) :
    Function.Surjective (toCyc X i) := by
  rintro ⟨z, hz⟩
  obtain ⟨y, hy⟩ := exists_of_exactAt X rfl rfl (hX (i + 1)) z hz
  exact ⟨y, Subtype.ext hy⟩

lemma exact_subtype_toCyc (X : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) :
    Function.Exact (cyc X i).subtype (toCyc X i) := by
  intro x
  constructor
  · intro hx
    exact ⟨⟨x, congrArg Subtype.val hx⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    exact Subtype.ext y.2

lemma flat_cyc (X : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) [X.IsStrictlyLE n]
    (hX : X.Acyclic) (hflat : ∀ i, Module.Flat A (X.X i)) (i : ℤ) :
    Module.Flat A (cyc X i) := by
  have key : ∀ k : ℕ, ∀ i : ℤ, i = n + 1 - k → Module.Flat A (cyc X i) := by
    intro k
    induction k with
    | zero =>
      intro i hi
      have : Subsingleton (X.X i) :=
        ModuleCat.subsingleton_of_isZero (X.isZero_of_isStrictlyLE n i (by lia))
      exact flat_of_subsingleton _
    | succ k ih =>
      intro i hi
      have h1 := ih (i + 1) (by push_cast at hi; lia)
      exact (flat_shortExact_calculus (cyc X i).subtype (toCyc X i)
        (Submodule.injective_subtype _) (toCyc_surjective X hX i)
        (exact_subtype_toCyc X i)).2 ⟨hflat i, h1⟩
  by_cases hi : n < i
  · have : Subsingleton (X.X i) :=
      ModuleCat.subsingleton_of_isZero (X.isZero_of_isStrictlyLE n i hi)
    exact flat_of_subsingleton _
  · exact key (n + 1 - i).toNat i (by lia)

lemma rTensor_injective_of_exact_of_flat' {M N P : Type*} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] [Module A M] [Module A N] [Module A P] [Module.Flat A P]
    (f : N →ₗ[A] P) (hf : Function.Surjective f) (g : M →ₗ[A] N) (hg : Function.Injective g)
    (H : Function.Exact g f) (Q : Type*) [AddCommGroup Q] [Module A Q] :
    Function.Injective (g.rTensor Q) := by
  have h := LinearMap.lTensor_injective_of_exact_of_flat f hf g hg H Q
  have e : g.rTensor Q = (TensorProduct.comm A Q N).toLinearMap ∘ₗ g.lTensor Q ∘ₗ
      (TensorProduct.comm A M Q).toLinearMap := by
    apply TensorProduct.ext'
    intro m q
    simp
  rw [e, LinearMap.coe_comp, LinearMap.coe_comp]
  exact (TensorProduct.comm A Q N).injective.comp (h.comp (TensorProduct.comm A M Q).injective)

lemma acyclic_tensor (X : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) [X.IsStrictlyLE n]
    (hX : X.Acyclic) (hflat : ∀ i, Module.Flat A (X.X i)) (M : ModuleCat.{u} A) :
    (((tensorRight M).mapHomologicalComplex (ComplexShape.up ℤ)).obj X).Acyclic := by
  intro i
  obtain ⟨h, rfl⟩ : ∃ h, i = h + 1 := ⟨i - 1, by ring⟩
  apply exactAt_of_exists _ rfl rfl
  show ∀ x : TensorProduct A (X.X (h + 1)) M, (X.d (h + 1) (h + 1 + 1)).hom.rTensor M x = 0 →
    ∃ y : TensorProduct A (X.X h) M, (X.d h (h + 1)).hom.rTensor M y = x
  intro x hx
  have hfac : ∀ j : ℤ, (X.d j (j + 1)).hom = (cyc X (j + 1)).subtype ∘ₗ toCyc X j := fun j => rfl
  have : Module.Flat A (cyc X (h + 1 + 1 + 1)) := flat_cyc X n hX hflat _
  have hinj := rTensor_injective_of_exact_of_flat' (toCyc X (h + 1 + 1))
    (toCyc_surjective X hX _) (cyc X (h + 1 + 1)).subtype (Submodule.injective_subtype _)
    (exact_subtype_toCyc X _) M
  rw [hfac, LinearMap.rTensor_comp, LinearMap.comp_apply] at hx
  have hx' : (toCyc X (h + 1)).rTensor M x = 0 := hinj (by rw [hx, map_zero])
  obtain ⟨w, rfl⟩ := ((rTensor_exact M (exact_subtype_toCyc X (h + 1))
    (toCyc_surjective X hX _)) x).1 hx'
  obtain ⟨y, rfl⟩ := LinearMap.rTensor_surjective M (toCyc_surjective X hX h) w
  refine ⟨y, ?_⟩
  rw [hfac, LinearMap.rTensor_comp, LinearMap.comp_apply]

lemma quasiIso_tensor {L C : CochainComplex (ModuleCat.{u} A) ℤ} (n : ℤ) [L.IsStrictlyLE n]
    [C.IsStrictlyLE n] (f : L ⟶ C) [QuasiIso f] (hL : ∀ i, Module.Flat A (L.X i))
    (hC : ∀ i, Module.Flat A (C.X i)) (M : ModuleCat.{u} A) :
    QuasiIso (((tensorRight M).mapHomologicalComplex (ComplexShape.up ℤ)).map f) := by
  rw [quasiIso_iff_acyclic_mappingCone]
  have hcone : (CochainComplex.mappingCone f).Acyclic :=
    (quasiIso_iff_acyclic_mappingCone f).1 inferInstance
  have : (CochainComplex.mappingCone f).IsStrictlyLE n := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨L.isZero_of_isStrictlyLE n _, C.isZero_of_isStrictlyLE n _⟩
  have hflat : ∀ i, Module.Flat A ((CochainComplex.mappingCone f).X i) := by
    intro i
    let e := HomologicalComplex.homotopyCofiber.XIsoBiprod f i (i + 1) rfl ≪≫
      ModuleCat.biprodIsoProd _ _
    have : Module.Flat A (L.X (i + 1) × C.X i) :=
      (flat_shortExact_calculus (LinearMap.inl A (L.X (i + 1)) (C.X i))
        (LinearMap.snd A (L.X (i + 1)) (C.X i)) LinearMap.inl_injective
        LinearMap.snd_surjective Function.Exact.inl_snd).1 ⟨hL _, hC _⟩
    exact (Module.Flat.equiv_iff e.toLinearEquiv).2 this
  intro i
  exact (acyclic_tensor _ n hcone hflat M i).of_iso
    (CochainComplex.mappingCone.mapHomologicalComplexIso f (tensorRight M))


/-- Finitely generated homology gives finitely many cycles generating the cycles modulo
boundaries. -/
lemma exists_fin_cycles_gen {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{u} A) c) (i j k : ι) (hi : c.prev j = i)
    (hk : c.next j = k) [Module.Finite A (K.homology j)] :
    ∃ (m : ℕ) (z : Fin m → K.X j), (∀ l, K.d j k (z l) = 0) ∧
      ∀ y : K.X j, K.d j k y = 0 → ∃ (a : Fin m →₀ A) (b : K.X i),
        y = Finsupp.linearCombination A z a + K.d i j b := by
  subst hi hk
  let p := LinearMap.range (K.sc j).moduleCatToCycles
  have : Module.Finite A (K.sc j).homology := ‹Module.Finite A (K.homology j)›
  have hfin : Module.Finite A (LinearMap.ker (K.sc j).g.hom ⧸ p) :=
    Module.Finite.equiv (K.sc j).moduleCatHomologyIso.toLinearEquiv
  obtain ⟨m, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hfin.fg_top
  choose w hw using fun l => Submodule.Quotient.mk_surjective _ (s l)
  let z : Fin m → K.X j := fun l => (w l).1
  refine ⟨m, z, fun l => (w l).2, fun y hy => ?_⟩
  have hq : p.mkQ (⟨y, hy⟩ : LinearMap.ker (K.sc j).g.hom) ∈
      LinearMap.range (Finsupp.linearCombination A s) := by
    rw [Finsupp.range_linearCombination, hs]; trivial
  obtain ⟨a, ha⟩ := hq
  have hs' : s = p.mkQ ∘ w := funext fun l => (hw l).symm
  rw [hs', ← Finsupp.apply_linearCombination] at ha
  have hmem : Finsupp.linearCombination A w a - ⟨y, hy⟩ ∈ p :=
    (Submodule.Quotient.eq p).1 ha
  obtain ⟨b, hb⟩ := hmem
  refine ⟨a, -b, ?_⟩
  have hb' := congrArg Subtype.val hb
  have hlc : ((Finsupp.linearCombination A w a).1 : K.X j) =
      Finsupp.linearCombination A z a :=
    Finsupp.apply_linearCombination A (LinearMap.ker (K.sc j).g.hom).subtype w a
  simp only [Submodule.coe_sub] at hb'
  rw [hlc] at hb'
  change K.d (c.prev j) j b = _ at hb'
  have e : (K.d (c.prev j) j) (-b) = -(K.d (c.prev j) j b) := map_neg _ b
  have hb'' : K.d (c.prev j) j b = Finsupp.linearCombination A z a - y := hb'
  rw [e, hb'']
  abel


lemma d_eq_zero_of_d_next_eq_zero {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{u} A) c) {j : ι} (y : K.X j)
    (h : K.d j (c.next j) y = 0) (j' : ι) : K.d j j' y = 0 := by
  by_cases hr : c.Rel j j'
  · rw [c.next_eq' hr] at h
    exact h
  · rw [K.shape _ _ hr]
    rfl


section cover

variable (A₀ : ModuleCat.{u} A)

/-- The free module on the elements of a module. -/
noncomputable abbrev cover : ModuleCat.{u} A := ModuleCat.of A (A₀ →₀ A)

/-- The canonical epimorphism from `cover A₀`. -/
noncomputable abbrev coverπ : cover A₀ ⟶ A₀ := ModuleCat.ofHom (Finsupp.linearCombination A id)

instance : Epi (coverπ A₀) :=
  (ModuleCat.epi_iff_surjective _).2
    (Finsupp.linearCombination_surjective _ Function.surjective_id)

variable {A₀}

/-- The map out of `cover A₀` given by an arbitrary function. -/
noncomputable abbrev coverLift {X : ModuleCat.{u} A} (s : A₀ → X) : cover A₀ ⟶ X :=
  ModuleCat.ofHom (Finsupp.linearCombination A s)

lemma cover_ext {X : ModuleCat.{u} A} {f g : cover A₀ ⟶ X}
    (h : ∀ a, f (Finsupp.single a 1) = g (Finsupp.single a 1)) : f = g :=
  ModuleCat.hom_ext (Finsupp.lhom_ext' fun a => LinearMap.ext_ring (h a))

end cover

variable (K : ChainComplex (ModuleCat.{u} A) ℕ)

/-- One stage of the descending construction: a finite free module `P` in homological
degree `k`, a map `φ : P → K_k`, and the submodule `Z` of `P` that will be the cycles. -/
structure Stage (k : ℕ) where
  /-- the finite free module -/
  P : ModuleCat.{u} A
  free : Module.Free A P
  finite : Module.Finite A P
  /-- the comparison map -/
  phi : P ⟶ K.X k
  /-- the future cycles -/
  Z : Submodule A P
  h₁ : ∀ z ∈ Z, ∀ j, K.d k j (phi z) = 0
  h₂ : ∀ y : K.X k, (∀ j, K.d k j y = 0) →
    ∃ z ∈ Z, ∃ b : K.X (k + 1), phi z = y + K.d (k + 1) k b

/-- The next stage of the construction together with the differential into the previous one. -/
structure Step {k : ℕ} (S : Stage K k) where
  /-- the next stage -/
  T : Stage K (k + 1)
  /-- the differential -/
  d : T.P ⟶ S.P
  hd₁ : ∀ x, d x ∈ S.Z
  hd₂ : ∀ x, S.phi (d x) = K.d (k + 1) k (T.phi x)
  hd₃ : ∀ z ∈ S.Z, (∃ b, S.phi z = K.d (k + 1) k b) → ∃ x, d x = z
  hZ : ∀ x, x ∈ T.Z ↔ d x = 0

lemma nonempty_base (hK : ∀ k, Module.Finite A (K.homology k)) :
    Nonempty {S : Stage K 0 // S.Z = ⊤} := by
  obtain ⟨p, z, -, hgen⟩ := exists_fin_cycles_gen K 1 0 0 (by simp) (by simp)
  let S : Stage K 0 :=
    { P := ModuleCat.of A (Fin p →₀ A)
      free := inferInstance
      finite := inferInstance
      phi := ModuleCat.ofHom (Finsupp.linearCombination A z)
      Z := ⊤
      h₁ := ?_
      h₂ := ?_ }
  refine ⟨⟨S, rfl⟩⟩
  · intro x _ j
    rw [K.shape _ _ (by simp)]
    rfl
  · intro y hy
    obtain ⟨a, b, hab⟩ := hgen y (hy 0)
    refine ⟨a, trivial, -b, ?_⟩
    change Finsupp.linearCombination A z a = _
    rw [hab, map_neg]
    abel

variable [IsNoetherianRing A]

lemma nonempty_step (hK : ∀ k, Module.Finite A (K.homology k)) {k : ℕ} (S : Stage K k) :
    Nonempty (Step K S) := by
  have := S.free
  have := S.finite
  let N : Submodule A S.P := S.Z ⊓ (LinearMap.range (K.d (k + 1) k).hom).comap S.phi.hom
  have hN : N.FG := IsNoetherian.noetherian N
  obtain ⟨m, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hN
  have hsN : ∀ l, s l ∈ N := fun l => hs ▸ Submodule.subset_span ⟨l, rfl⟩
  choose bb hbb using fun l => (hsN l).2
  obtain ⟨p, z, hz, hgen⟩ := exists_fin_cycles_gen K (k + 2) (k + 1) k (by simp) (by simp)
  let v : Fin m ⊕ Fin p → S.P := Sum.elim s 0
  let P' : ModuleCat.{u} A := ModuleCat.of A ((Fin m ⊕ Fin p) →₀ A)
  let d : P' ⟶ S.P := ModuleCat.ofHom (Finsupp.linearCombination A (v))
  let φ' : P' ⟶ K.X (k + 1) := ModuleCat.ofHom (Finsupp.linearCombination A (Sum.elim bb z))
  have hd₂ : ∀ x, S.phi (d x) = K.d (k + 1) k (φ' x) := by
    have : S.phi.hom ∘ₗ Finsupp.linearCombination A (v) =
        (K.d (k + 1) k).hom ∘ₗ Finsupp.linearCombination A (Sum.elim bb z) := by
      apply Finsupp.lhom_ext
      rintro (l | l) r
      · simp only [LinearMap.comp_apply, Finsupp.linearCombination_single, map_smul, v,
          Sum.elim_inl]
        rw [hbb l]
      · simp only [LinearMap.comp_apply, Finsupp.linearCombination_single, map_smul, v,
          Sum.elim_inr, Pi.zero_apply, map_zero, smul_zero]
        change (0 : K.X k) = r • K.d (k + 1) k (z l)
        rw [hz l, smul_zero]
    exact fun x => LinearMap.congr_fun this x
  let T : Stage K (k + 1) :=
    { P := P'
      free := inferInstance
      finite := inferInstance
      phi := φ'
      Z := LinearMap.ker d.hom
      h₁ := ?_
      h₂ := ?_ }
  refine ⟨{ T := T, d := d, hd₁ := ?_, hd₂ := hd₂, hd₃ := ?_, hZ := fun x => Iff.rfl }⟩
  · intro x
    have hle : Submodule.span A (Set.range (v)) ≤ N := by
      rw [Submodule.span_le]
      rintro _ ⟨(l | l), rfl⟩
      · exact hsN l
      · exact N.zero_mem
    have hx : d x ∈ LinearMap.range (Finsupp.linearCombination A (v)) := ⟨x, rfl⟩
    rw [Finsupp.range_linearCombination] at hx
    exact (hle hx).1
  · intro y hy hb
    have hyN : y ∈ N := ⟨hy, by obtain ⟨b, hb⟩ := hb; exact ⟨b, hb.symm⟩⟩
    rw [← hs, ← Finsupp.range_linearCombination] at hyN
    obtain ⟨a, rfl⟩ := hyN
    refine ⟨Finsupp.mapDomain Sum.inl a, ?_⟩
    change Finsupp.linearCombination A (v) (Finsupp.mapDomain Sum.inl a) = _
    rw [Finsupp.linearCombination_mapDomain, Sum.elim_comp_inl]
  · intro x hx j
    by_cases hj : j = k
    · subst hj
      rw [← hd₂]
      change S.phi (d.hom x) = 0
      rw [LinearMap.mem_ker.1 hx, map_zero]
    · rw [K.shape _ _ (by simp; lia)]
      rfl
  · intro y hy
    obtain ⟨a, b, hab⟩ := hgen y (hy k)
    refine ⟨Finsupp.mapDomain Sum.inr a, ?_, -b, ?_⟩
    · change Finsupp.linearCombination A (v) (Finsupp.mapDomain Sum.inr a) = 0
      rw [Finsupp.linearCombination_mapDomain]
      simp [v]
    · change Finsupp.linearCombination A (Sum.elim bb z) (Finsupp.mapDomain Sum.inr a) = _
      rw [Finsupp.linearCombination_mapDomain, Sum.elim_comp_inr, hab, map_neg]
      abel


variable {K}

/-- The chosen next step of the construction. -/
noncomputable def step (hK : ∀ k, Module.Finite A (K.homology k)) {k : ℕ} (S : Stage K k) :
    Step K S :=
  Classical.choice (nonempty_step K hK S)

/-- The stages of the construction. -/
noncomputable def stage (hK : ∀ k, Module.Finite A (K.homology k)) : (k : ℕ) → Stage K k
  | 0 => (Classical.choice (nonempty_base K hK)).1
  | k + 1 => (step hK (stage hK k)).T

lemma stage_zero_Z (hK : ∀ k, Module.Finite A (K.homology k)) : (stage hK 0).Z = ⊤ :=
  (Classical.choice (nonempty_base K hK)).2

/-- The finite free complex. -/
noncomputable def complex (hK : ∀ k, Module.Finite A (K.homology k)) :
    ChainComplex (ModuleCat.{u} A) ℕ :=
  ChainComplex.of (fun k => (stage hK k).P) (fun k => (step hK (stage hK k)).d) (fun k => by
    ext x
    exact ((step hK (stage hK k)).hZ _).1 ((step hK (stage hK (k + 1))).hd₁ x))

lemma complex_d_succ (hK : ∀ k, Module.Finite A (K.homology k)) (k : ℕ) :
    (complex hK).d (k + 1) k = (step hK (stage hK k)).d :=
  ChainComplex.of_d (fun k => (stage hK k).P) (fun k => (step hK (stage hK k)).d) k

/-- The comparison map from the finite free complex. -/
noncomputable def toK (hK : ∀ k, Module.Finite A (K.homology k)) : complex hK ⟶ K where
  f k := (stage hK k).phi
  comm' := by
    rintro i j (rfl : j + 1 = i)
    rw [complex_d_succ]
    ext x
    exact ((step hK (stage hK j)).hd₂ x).symm

lemma d_eq_zero_of_mem_Z (hK : ∀ k, Module.Finite A (K.homology k)) {j : ℕ}
    (z : (complex hK).X j) (hz : z ∈ (stage hK j).Z) (j' : ℕ) : (complex hK).d j j' z = 0 := by
  cases j with
  | zero =>
    rw [(complex hK).shape _ _ (by simp)]
    rfl
  | succ k =>
    by_cases hj : j' = k
    · subst hj
      rw [complex_d_succ]
      exact ((step hK (stage hK j')).hZ z).1 hz
    · rw [(complex hK).shape _ _ (by simp; lia)]
      rfl

lemma mem_Z_of_d_eq_zero (hK : ∀ k, Module.Finite A (K.homology k)) {j : ℕ}
    (z : (complex hK).X j) (hz : (complex hK).d j ((ComplexShape.down ℕ).next j) z = 0) :
    z ∈ (stage hK j).Z := by
  cases j with
  | zero =>
    rw [stage_zero_Z]
    trivial
  | succ k =>
    rw [ChainComplex.next_nat_succ, complex_d_succ] at hz
    exact ((step hK (stage hK k)).hZ z).2 hz

lemma quasiIso_toK (hK : ∀ k, Module.Finite A (K.homology k)) : QuasiIso (toK hK) := by
  rw [quasiIso_iff]
  intro j
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hmono : Mono (HomologicalComplex.homologyMap (toK hK) j) := by
    rw [HomologicalComplex.mono_homologyMap_iff_up_to_refinements _ (j + 1) j _ (by simp) rfl]
    intro A₀ x₂ hx₂ y₁ fac
    have key : ∀ a : A₀, ∃ w : (complex hK).X (j + 1), (complex hK).d (j + 1) j w = x₂ a := by
      intro a
      have h1 : (complex hK).d j ((ComplexShape.down ℕ).next j) (x₂ a) = 0 := by
        simpa using ConcreteCategory.congr_hom hx₂ a
      have h2 : (stage hK j).phi (x₂ a) = K.d (j + 1) j (y₁ a) := by
        exact ConcreteCategory.congr_hom fac a
      obtain ⟨w, hw⟩ := (step hK (stage hK j)).hd₃ _ (mem_Z_of_d_eq_zero hK _ h1) ⟨_, h2⟩
      exact ⟨w, by rw [complex_d_succ]; exact hw⟩
    choose w hw using key
    refine ⟨cover A₀, coverπ A₀, inferInstance, coverLift w, cover_ext fun a => ?_⟩
    simp [hw]
  have hepi : Epi (HomologicalComplex.homologyMap (toK hK) j) := by
    rw [HomologicalComplex.epi_homologyMap_iff_up_to_refinements _ (j + 1) j _ (by simp) rfl]
    intro A₀ y₂ hy₂
    have key : ∀ a : A₀, ∃ z : (complex hK).X j, z ∈ (stage hK j).Z ∧
        ∃ b : K.X (j + 1), (stage hK j).phi z = y₂ a + K.d (j + 1) j b := by
      intro a
      have h1 : K.d j ((ComplexShape.down ℕ).next j) (y₂ a) = 0 := by
        simpa using ConcreteCategory.congr_hom hy₂ a
      obtain ⟨z, hz, b, hb⟩ := (stage hK j).h₂ _ (d_eq_zero_of_d_next_eq_zero K _ h1)
      exact ⟨z, hz, b, hb⟩
    choose z hz b hb using key
    refine ⟨cover A₀, coverπ A₀, inferInstance, coverLift z, cover_ext fun a => ?_,
      coverLift (fun a => -b a), cover_ext fun a => ?_⟩
    · simpa using d_eq_zero_of_mem_Z hK _ (hz a) _
    · have h : (stage hK j).phi.hom (z a) = y₂.hom a + (K.d (j + 1) j).hom (b a) := hb a
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_add, LinearMap.add_apply]
      simp only [toK, ModuleCat.hom_ofHom, Finsupp.linearCombination_single, one_smul, id,
        map_neg]
      have h' : (stage hK j).phi.hom (z a) + -(K.d (j + 1) j).hom (b a) = y₂.hom a := by
        rw [h, add_neg_cancel_right]
      exact h'.symm
  exact isIso_of_mono_of_epi _


lemma complex_free (hK : ∀ k, Module.Finite A (K.homology k)) (k : ℕ) :
    Module.Free A ((complex hK).X k) :=
  (stage hK k).free

lemma complex_finite (hK : ∀ k, Module.Finite A (K.homology k)) (k : ℕ) :
    Module.Finite A ((complex hK).X k) :=
  (stage hK k).finite

end FiniteFreeComplexReplacement

open FiniteFreeComplexReplacement in
/-- **Hartshorne III, Lemma 12.3.** Let `A` be a Noetherian ring and `C` a bounded-above
cochain complex of `A`-modules (`C^i = 0` for `i > n`) with finitely generated cohomology
modules. Then there are a bounded-above complex `L` (again `L^i = 0` for `i > n`) of finitely
generated free `A`-modules and a quasi-isomorphism `f : L ⟶ C`. If moreover every term of `C`
is flat over `A`, then for every `A`-module `M` the map `f ⊗ M : L ⊗_A M ⟶ C ⊗_A M` is a
quasi-isomorphism, i.e. `H^i(L ⊗_A M) ⟶ H^i(C ⊗_A M)` is an isomorphism for every `i`. -/
theorem exists_finiteFree_quasiIso_of_isStrictlyLE
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (C : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) [C.IsStrictlyLE n]
    (hC : ∀ i, Module.Finite A (C.homology i)) :
    ∃ (L : CochainComplex (ModuleCat.{u} A) ℤ) (f : L ⟶ C),
      L.IsStrictlyLE n ∧ (∀ i, Module.Free A (L.X i)) ∧ (∀ i, Module.Finite A (L.X i)) ∧
      QuasiIso f ∧
      ((∀ i, Module.Flat A (C.X i)) → ∀ M : ModuleCat.{u} A,
        QuasiIso (((tensorRight M).mapHomologicalComplex (ComplexShape.up ℤ)).map f)) := by
  let e := ComplexShape.embeddingUpIntLE n
  let K : ChainComplex (ModuleCat.{u} A) ℕ := C.restriction e
  have hlift : e.HasLift (𝟙 K) := fun j hj => (hj.false_of_isTruncLE).elim
  let ι : C ⟶ K.extend e := e.liftExtend (𝟙 K) hlift
  have hι : ∀ i, IsIso (ι.f i) := by
    intro i
    by_cases hi : ∃ k, e.f k = i
    · obtain ⟨k, hk⟩ := hi
      rw [e.isIso_liftExtend_f_iff (𝟙 K) hlift hk]
      infer_instance
    · have hi' : ∀ k, e.f k ≠ i := fun k hk => hi ⟨k, hk⟩
      have hni : n < i := (ComplexShape.notMem_range_embeddingUpIntLE_iff n i).1 hi'
      exact isIso_of_source_target_iso_zero _
        (C.isZero_of_isStrictlyLE n i hni).isoZero (K.isZero_extend_X e i hi').isoZero
  have : IsIso ι := HomologicalComplex.Hom.isIso_of_components ι
  have hK : ∀ k, Module.Finite A (K.homology k) := by
    intro k
    let φ : C.homology (e.f k) ≅ K.homology k :=
      (HomologicalComplex.homologyFunctor _ _ (e.f k)).mapIso (asIso ι) ≪≫
        K.extendHomologyIso e rfl
    exact Module.Finite.equiv φ.toLinearEquiv
  let L := (complex hK).extend e
  let f : L ⟶ C := HomologicalComplex.extendMap (toK hK) e ≫ inv ι
  have : QuasiIso (toK hK) := quasiIso_toK hK
  have hfree : ∀ i, Module.Free A (L.X i) ∧ Module.Finite A (L.X i) := by
    intro i
    by_cases hi : ∃ k, e.f k = i
    · obtain ⟨k, hk⟩ := hi
      have := complex_free hK k
      have := complex_finite hK k
      let φ := (complex hK).extendXIso e hk
      exact ⟨Module.Free.of_equiv φ.toLinearEquiv.symm,
        Module.Finite.equiv φ.toLinearEquiv.symm⟩
    · have : Subsingleton (L.X i) := ModuleCat.subsingleton_of_isZero
        ((complex hK).isZero_extend_X e i fun k hk => hi ⟨k, hk⟩)
      exact ⟨inferInstance, inferInstance⟩
  refine ⟨L, f, inferInstance, fun i => (hfree i).1, fun i => (hfree i).2, inferInstance,
    fun hflat M => ?_⟩
  have : ∀ i, Module.Flat A (L.X i) := fun i => by
    have := (hfree i).1
    infer_instance
  exact quasiIso_tensor n f this hflat M

end Hartshorne

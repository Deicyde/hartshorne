/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.RingedSpace.GradedSheafSections
import Hartshorne.Scheme.GeometricVectorBundle
import Hartshorne.Scheme.RelativeProj

/-!
# Projective bundles

Hartshorne, *Algebraic Geometry*, II.7, p. 162: for a Noetherian scheme `X` and a locally free
`𝒪_X`-module `E` of finite rank, the *projective bundle* is `P(E) = Proj_X S(E)`, the relative
`Proj` of the symmetric algebra `S(E) = ⊕_{d ≥ 0} S^d(E)`, which satisfies condition (†) of p. 160.

## The symmetric algebra as a quasi-coherent graded algebra

Relative `Proj` (`Hartshorne.RelativeProjData.relativeProj`) takes the sections of a
quasi-coherent graded algebra over the affine opens of `X`. For `S(E)`:

* the rings `Γ(U, S(E))` with their restriction maps and the structure maps `r ↦ r • 1` are those
  of the quasi-coherent algebra of the commutative sheaf of algebras `S(E)`
  (`Hartshorne.ModuleSheafAlgebra.toQuasiCoherentAlgebra`), which satisfies
  `Γ(D(r), S(E)) = Γ(U, S(E))_r` by Lemma II.5.3;
* the grading `Γ(U, S(E)) = ⊕_d Γ(U, S^d(E))` over an affine (so quasi-compact) open `U`
  (`Scheme.Modules.symmetricGrading`) is the direct sum decomposition of the sections of a graded
  sheafification over a quasi-compact open
  (`Hartshorne.SheafAlgebraOperations.PresheafAlgebra.IsGraded.isInternal_sections`).

The result is `Scheme.Modules.symmetricGradedAlgebra`.
-/

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

open Hartshorne Hartshorne.SheafAlgebraOperations Hartshorne.ModuleSheafAlgebra

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}} (E : X.Modules)

/-- The homogeneous sections of degree `d` of `S(E)` over an open `U`: the image of
`Γ(U, S^d(E)) → Γ(U, S(E))`, as an additive subgroup of the ring `Γ(U, S(E))`. -/
def symmetricGrading (U : X.Opens) (d : ℕ) : AddSubgroup (E.symSections U) :=
  (LinearMap.range ((moduleSheafSymmetricAlgebraι (R := X.sheaf) d E).val.app (op U)).hom).toAddSubgroup

lemma mem_symmetricGrading {U : X.Opens} {d : ℕ} {x : E.symSections U} :
    x ∈ E.symmetricGrading U d ↔ ∃ a : Γ(E.symmetricPower d, U),
      (moduleSheafSymmetricAlgebraι (R := X.sheaf) d E).val.app (op U) a = ofSectionsRing _ x :=
  LinearMap.mem_range (f := ((moduleSheafSymmetricAlgebraι (R := X.sheaf) d E).val.app (op U)).hom)
    (x := ofSectionsRing _ x)

lemma one_mem_symmetricGrading (U : X.Opens) : (1 : E.symSections U) ∈ E.symmetricGrading U 0 :=
  E.mem_symmetricGrading.2 ⟨_, E.symmetricPowerZeroIso_inv_one (op U)⟩

lemma mul_mem_symmetricGrading {U : X.Opens} {i j : ℕ} {a b : E.symSections U}
    (ha : a ∈ E.symmetricGrading U i) (hb : b ∈ E.symmetricGrading U j) :
    a * b ∈ E.symmetricGrading U (i + j) := by
  obtain ⟨a', ha'⟩ := E.mem_symmetricGrading.1 ha
  obtain ⟨b', hb'⟩ := E.mem_symmetricGrading.1 hb
  refine E.mem_symmetricGrading.2
    ⟨_, (moduleSheafSymmetricAlgebra_mul_ι (R := X.sheaf) i E j (op U) a' b').symm.trans ?_⟩
  rw [ha', hb']
  rfl

lemma smul_mem_symmetricGrading {U : X.Opens} {d : ℕ} (r : Γ(X, U)) {a : E.symSections U}
    (ha : a ∈ E.symmetricGrading U d) :
    toSectionsRing _ (r • ofSectionsRing _ a) ∈ E.symmetricGrading U d := by
  obtain ⟨a', ha'⟩ := E.mem_symmetricGrading.1 ha
  exact E.mem_symmetricGrading.2 ⟨r • a', by rw [_root_.map_smul, ha']; rfl⟩

lemma unitRingHom_mem_symmetricGrading (U : X.Opens) (r : Γ(X, U)) :
    unitRingHom E.symmetricAlgebraStructure_isCommutative U r ∈ E.symmetricGrading U 0 :=
  E.smul_mem_symmetricGrading r (E.one_mem_symmetricGrading U)

lemma sectionsRestrict_mem_symmetricGrading {U V : X.Opens} (i : V ⟶ U) {d : ℕ}
    {a : E.symSections U} (ha : a ∈ E.symmetricGrading U d) :
    sectionsRestrict E.symmetricAlgebraStructure_isCommutative i a ∈
      E.symmetricGrading V d := by
  obtain ⟨a', ha'⟩ := E.mem_symmetricGrading.1 ha
  refine E.mem_symmetricGrading.2 ⟨(E.symmetricPower d).val.map i.op a',
    (PresheafOfModules.naturality_apply (moduleSheafSymmetricAlgebraι (R := X.sheaf) d E).val
      i.op a').trans ?_⟩
  rw [ha']
  rfl

/-- **Over an affine open `U`, `Γ(U, S(E)) = ⊕_d Γ(U, S^d(E))`.** -/
theorem symmetricGrading_isInternal {U : X.Opens} (hU : IsCompact (U : Set X)) :
    DirectSum.IsInternal (E.symmetricGrading U) :=
  (moduleSheafSymmetricAlgebraPresheaf_isGraded (R := X.sheaf) E).isInternal_sections hU

/-- `Γ(U, S(E))` is a graded ring over a quasi-compact open `U`. -/
@[instance_reducible]
def symmetricGradedRing {U : X.Opens} (hU : IsCompact (U : Set X)) :
    GradedRing (E.symmetricGrading U) :=
  { (E.symmetricGrading_isInternal hU).chooseDecomposition with
    one_mem := E.one_mem_symmetricGrading U
    mul_mem := fun _ _ _ _ => E.mul_mem_symmetricGrading }

variable {E}

/-- **`S(E)` as a quasi-coherent graded `𝒪_X`-algebra**, for a locally free `E` of finite rank:
over an affine open `U`, the graded ring `Γ(U, S(E)) = ⊕_d Γ(U, S^d(E))` with the structure map
`r ↦ r • 1`. -/
def symmetricGradedAlgebra (hE : E.IsLocallyFree) (hfin : ∀ x, E.rankAt x < Cardinal.aleph0) :
    QuasiCoherentGradedAlgebra X :=
  haveI := symmetricAlgebra_isQuasicoherent hE hfin
  { obj := sectionsFunctor E.symmetricAlgebraStructure_isCommutative
    structureMap := sectionsStructureMap E.symmetricAlgebraStructure_isCommutative
    coequifibered := coequifibered_structureMap E.symmetricAlgebraStructure_isCommutative
    grading U := E.symmetricGrading U.toOpens
    gradedRing U := E.symmetricGradedRing U.2.isCompact
    map_mem _ _ _ hx := E.sectionsRestrict_mem_symmetricGrading _ hx
    structureMap_mem U r := E.unitRingHom_mem_symmetricGrading U.toOpens r }

variable (hE : E.IsLocallyFree) (hfin : ∀ x, E.rankAt x < Cardinal.aleph0)

lemma symmetricGradedAlgebra_grading (U : X.AffineZariskiSite) :
    (symmetricGradedAlgebra hE hfin).grading U = E.symmetricGrading U.toOpens := rfl

/-! ### Condition (†) for `S(E)` -/

variable (E) in
/-- The degree-one sections `Γ(U, E) → Γ(U, S(E))` are homogeneous of degree one. -/
lemma symDegreeOne_mem_symmetricGrading (U : X.Opens) (s : Γ(E, U)) :
    E.symDegreeOne U s ∈ E.symmetricGrading U 1 := by
  refine E.mem_symmetricGrading.2 ⟨(sheafifyUnit (moduleSheafSymmetricPowerPresheaf
    (R := X.sheaf) 1 E)).app (op U) (Submodule.Quotient.mk
      (PiTensorProduct.tprod _ fun _ : Fin 1 => s)), ?_⟩
  refine (sheafifyMap_unit _ _ _).trans ?_
  change _ = (sheafifyUnit (moduleSheafSymmetricAlgebraPresheaf (R := X.sheaf) E)).app (op U)
    (SymmetricAlgebra.algHom _ _ (TensorAlgebra.ι _ s))
  rw [SheafTensorOperations.ι_eq_toTensorAlgebra]
  rfl

/-- **`S(E)₀ = 𝒪_X`**: over every affine open `U`, the structure map `Γ(U, 𝒪_X) → Γ(U, S(E))₀` is
bijective. -/
theorem symmetricGradedAlgebra_degreeZero :
    (symmetricGradedAlgebra hE hfin).DegreeZeroIsStructureSheaf := by
  intro U
  have hG := moduleSheafSymmetricAlgebraPresheaf_isGraded (R := X.sheaf) E
  have key : ∀ r : Γ(X, U.toOpens), (moduleSheafSymmetricAlgebraι (R := X.sheaf) 0 E).val.app
      (op U.toOpens) (E.symmetricPowerZeroIso.inv.val.app (op U.toOpens) r) =
      ofSectionsRing _ ((symmetricGradedAlgebra hE hfin).structureMap.app (op U) r) := fun r =>
    moduleSheafSymmetricAlgebraι_zero_apply (R := X.sheaf) E (op U.toOpens) r
  refine ⟨(injective_iff_map_eq_zero _).2 fun r hr => ?_, fun ⟨y, hy⟩ => ?_⟩
  · have h0 : ofSectionsRing _ ((symmetricGradedAlgebra hE hfin).structureMap.app (op U) r) = 0 :=
      congrArg Subtype.val hr
    rw [← key] at h0
    have h1 := congrArg ((hG.sheafProj 0).val.app (op U.toOpens)) h0
    rw [map_zero] at h1
    have h2 := hG.sheafProj_ι_self 0 (op U.toOpens)
      (E.symmetricPowerZeroIso.inv.val.app (op U.toOpens) r)
    change (hG.sheafProj 0).val.app (op U.toOpens) ((moduleSheafSymmetricAlgebraι (R := X.sheaf) 0
      E).val.app (op U.toOpens) _) = _ at h2
    rw [h2] at h1
    have h3 : E.symmetricPowerZeroIso.hom.val.app (op U.toOpens)
        (E.symmetricPowerZeroIso.inv.val.app (op U.toOpens) r) = r :=
      congrArg (fun φ : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf =>
        φ.val.app (op U.toOpens) r) E.symmetricPowerZeroIso.inv_hom_id
    rw [← h3, h1, map_zero]
  · obtain ⟨a, ha⟩ := E.mem_symmetricGrading.1 hy
    refine ⟨E.symmetricPowerZeroIso.hom.val.app (op U.toOpens) a, Subtype.ext ?_⟩
    change ofSectionsRing _ ((symmetricGradedAlgebra hE hfin).structureMap.app (op U) _) =
      ofSectionsRing _ y
    rw [← key, ← ha]
    exact congrArg ((moduleSheafSymmetricAlgebraι (R := X.sheaf) 0 E).val.app (op U.toOpens))
      (congrArg (fun φ : E.symmetricPower 0 ⟶ E.symmetricPower 0 => φ.val.app (op U.toOpens) a)
        E.symmetricPowerZeroIso.hom_inv_id)

/-- **`S(E)₁` is coherent**: over every affine open `U`, `Γ(U, S(E))₁` is a finitely generated
`Γ(U, 𝒪_X)`-module. -/
theorem symmetricGradedAlgebra_degreeOneCoherent [IsNoetherian X] :
    (symmetricGradedAlgebra hE hfin).DegreeOneCoherent := by
  intro U
  have hfg := (forall_affine_finite_of_isCoherent _ (symmetricPower_isCoherent hE hfin 1)
    ⟨U.toOpens, U.2⟩).1
  obtain ⟨k, m, hm⟩ := Module.Finite.exists_fin (R := Γ(X, U.toOpens))
    (M := Γ(E.symmetricPower 1, U.toOpens))
  refine ⟨k, fun i => toSectionsRing _ ((moduleSheafSymmetricAlgebraι (R := X.sheaf) 1 E).val.app
    (op U.toOpens) (m i)), fun i => E.mem_symmetricGrading.2 ⟨m i, rfl⟩, fun x hx => ?_⟩
  obtain ⟨a, rfl⟩ := E.mem_symmetricGrading.1 hx
  have ha : a ∈ Submodule.span Γ(X, U.toOpens) (Set.range m) := hm ▸ Submodule.mem_top
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 ha
  refine ⟨c, Eq.trans ?_ (Finset.sum_congr rfl fun i _ => (unitRingHom_mul _ U.toOpens (c i) _).symm)⟩
  show (moduleSheafSymmetricAlgebraι (R := X.sheaf) 1 E).val.app (op U.toOpens) (∑ i, c i • m i) =
    ∑ i, c i • (moduleSheafSymmetricAlgebraι (R := X.sheaf) 1 E).val.app (op U.toOpens) (m i)
  rw [map_sum]
  simp only [_root_.map_smul]

/-! ### Generation in degree one -/

variable (E) in
/-- `E` has a finite frame over the basic open `D(f)`. -/
private def HasFrameOn {U : X.Opens} (f : Γ(X, U)) : Prop :=
  ∃ (r : ℕ) (e : ULift.{u} (Fin r) → Γ(E, X.basicOpen f)),
    Ringed.IsLocalFrame (R := X.sheaf) E (X.basicOpen f) e

include hE hfin in
/-- The basic opens of an affine open `U` on which `E` has a finite frame cover `U`. -/
private lemma span_hasFrameOn {U : X.Opens} (hU : IsAffineOpen U) :
    Ideal.span {f : Γ(X, U) | E.HasFrameOn f} = ⊤ := by
  have hfl := (isFiniteLocallyFree_iff E).2 ⟨hE, hfin⟩
  refine hU.self_le_iSup_basicOpen_iff.1 fun y hy => ?_
  obtain ⟨W, hyW, r, ⟨α⟩⟩ := hfl y
  obtain ⟨f, hfW, hyf⟩ := hU.exists_basicOpen_le (V := W) ⟨y, hyW⟩ hy
  exact Opens.mem_iSup.2
    ⟨⟨f, r, _, (Ringed.isLocalFrame_of_over_iso (R := X.sheaf) α).restrictLE hfW⟩, hyf⟩

variable (E) in
/-- The subring of `Γ(U, S(E))` generated by the homogeneous sections of degrees `0` and `1`. -/
private abbrev degreeOneClosure (U : X.Opens) : Subring (E.symSections U) :=
  Subring.closure ((E.symmetricGrading U 0 : Set (E.symSections U)) ∪ E.symmetricGrading U 1)

private lemma unitRingHom_mem_degreeOneClosure (U : X.Opens) (r : Γ(X, U)) :
    unitRingHom E.symmetricAlgebraStructure_isCommutative U r ∈ E.degreeOneClosure U :=
  Subring.subset_closure (Or.inl (E.unitRingHom_mem_symmetricGrading U r))

include hE hfin in
/-- Over a basic open `D(f)` of an affine open `U` on which `E` has a frame, every section of
`S(E)` over `U` becomes, after multiplication by a power of `f`, a polynomial in sections of degree
at most one. -/
private lemma exists_pow_mul_mem_degreeOneClosure {U : X.Opens} (hU : IsAffineOpen U)
    {f : Γ(X, U)} (hf : E.HasFrameOn f) (x : E.symSections U) :
    ∃ n : ℕ, unitRingHom E.symmetricAlgebraStructure_isCommutative U f ^ n * x ∈
      E.degreeOneClosure U := by
  have := symmetricAlgebra_isQuasicoherent hE hfin
  have : SheafOfModules.IsQuasicoherent.{u, u, u} E :=
    Ringed.IsFiniteLocallyFree.isQuasicoherent ((isFiniteLocallyFree_iff E).2 ⟨hE, hfin⟩)
  obtain ⟨r, e, he⟩ := hf
  let hS := E.symmetricAlgebraStructure_isCommutative
  let ρ : X.basicOpen f ⟶ U := homOfLE (X.basicOpen_le f)
  let res := sectionsRestrict hS ρ
  let u := unitRingHom hS U f
  have hu : res u = unitRingHom hS _ (X.presheaf.map ρ.op f) := unitRingHom_naturality hS ρ f
  have hu0 : u ∈ E.degreeOneClosure U := unitRingHom_mem_degreeOneClosure U f
  let G : Set (E.symSections (X.basicOpen f)) :=
    {z | ∃ n : ℕ, ∃ b ∈ E.degreeOneClosure U, z * res u ^ n = res b}
  have hadd : ∀ z w, z ∈ G → w ∈ G → z + w ∈ G := by
    rintro z w ⟨n, b, hb, hz⟩ ⟨m, c, hc, hw⟩
    refine ⟨n + m, b * u ^ m + c * u ^ n,
      add_mem (mul_mem hb (pow_mem hu0 _)) (mul_mem hc (pow_mem hu0 _)), ?_⟩
    rw [map_add, map_mul, map_mul, map_pow, map_pow, ← hz, ← hw]
    ring
  have hmul : ∀ z w, z ∈ G → w ∈ G → z * w ∈ G := by
    rintro z w ⟨n, b, hb, hz⟩ ⟨m, c, hc, hw⟩
    refine ⟨n + m, b * c, mul_mem hb hc, ?_⟩
    rw [map_mul, ← hz, ← hw]
    ring
  have hC : ∀ a, unitRingHom hS _ a ∈ G := by
    intro a
    have := hU.isLocalization_basicOpen f
    obtain ⟨⟨c, _, n, rfl⟩, hc⟩ := IsLocalization.surj (Submonoid.powers f) a
    refine ⟨n, unitRingHom hS U c, unitRingHom_mem_degreeOneClosure U c, ?_⟩
    rw [hu, ← map_pow, ← map_mul, unitRingHom_naturality]
    congr 1
    rw [← map_pow]
    exact hc
  have hX : ∀ k, E.symDegreeOne _ (e k) ∈ G := by
    intro k
    obtain ⟨m, t, ht⟩ := exists_pow_smul_extension_of_isAffineOpen E hU f (e k)
    refine ⟨m, E.symDegreeOne U t,
      Subring.subset_closure (Or.inr (E.symDegreeOne_mem_symmetricGrading U t)), ?_⟩
    change _ = sectionsRestrict hS ρ _
    rw [E.symDegreeOne_naturality, ht, symDegreeOne_smul, hu, map_pow, mul_comm]
  have hchart : ∀ p, E.chartRingHom _ e p ∈ G := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => rw [chartRingHom_C]; exact hC a
    | add p q hp hq => rw [map_add]; exact hadd _ _ hp hq
    | mul_X p k hp => rw [map_mul, chartRingHom_X]; exact hmul _ _ hp (hX k)
  obtain ⟨p, hp⟩ := (E.chartRingHom_bijective (hU.basicOpen f) he).2 (res x)
  have hx := hchart p
  rw [hp] at hx
  obtain ⟨n, b, hb, hxb⟩ := hx
  have h0 : res (x * u ^ n - b) = 0 := by
    rw [map_sub, map_mul, map_pow, hxb, sub_self]
  obtain ⟨m, hm⟩ := exists_pow_smul_eq_zero_of_isAffineOpen E.symmetricAlgebra hU f
    (ofSectionsRing hS (x * u ^ n - b)) h0
  have hm' : u ^ m * (x * u ^ n - b) = 0 := by
    rw [← map_pow]
    exact (unitRingHom_mul hS U (f ^ m) _).trans (congrArg (toSectionsRing hS) hm)
  refine ⟨m + n, ?_⟩
  have : u ^ (m + n) * x = u ^ m * b := by
    rw [mul_sub, sub_eq_zero] at hm'
    rw [← hm', pow_add]
    ring
  rw [this]
  exact mul_mem (pow_mem hu0 _) hb

include hE hfin in
/-- **`S(E)` is generated by `S(E)₁` as an `S(E)₀`-algebra**: over an affine open `U`, the ring
`Γ(U, S(E))` is generated by its homogeneous sections of degrees `0` and `1`. -/
theorem symmetricGrading_generated {U : X.Opens} (hU : IsAffineOpen U) :
    Subring.closure ((E.symmetricGrading U 0 : Set (E.symSections U)) ∪
      E.symmetricGrading U 1) = ⊤ := by
  let : Algebra Γ(X, U) (E.symSections U) :=
    (unitRingHom E.symmetricAlgebraStructure_isCommutative U).hom.toAlgebra
  let M' : Submodule Γ(X, U) (E.symSections U) :=
    { carrier := E.degreeOneClosure U
      add_mem' := add_mem
      zero_mem' := zero_mem _
      smul_mem' := fun c x hx => by
        rw [Algebra.smul_def]
        exact mul_mem (unitRingHom_mem_degreeOneClosure U c) hx }
  refine eq_top_iff.2 fun x _ => ?_
  refine M'.mem_of_span_eq_top_of_smul_pow_mem _ (span_hasFrameOn hE hfin hU) x fun ⟨f, hf⟩ => ?_
  obtain ⟨n, hn⟩ := exists_pow_mul_mem_degreeOneClosure hE hfin hU hf x
  refine ⟨n, ?_⟩
  rw [Algebra.smul_def, map_pow]
  exact hn

/-- **`S(E)` satisfies Hartshorne's condition (†)** (II.7, p. 160) on a Noetherian scheme: it is a
quasi-coherent graded `𝒪_X`-algebra with `S(E)₀ = 𝒪_X`, `S(E)₁` coherent, and generated by
`S(E)₁` as an `S(E)₀`-algebra. -/
def symmetricRelativeProjData [IsNoetherian X] : RelativeProjData X where
  algebra := symmetricGradedAlgebra hE hfin
  degreeZero := symmetricGradedAlgebra_degreeZero hE hfin
  degreeOne_coherent := symmetricGradedAlgebra_degreeOneCoherent hE hfin
  generated U := symmetricGrading_generated hE hfin U.2

/-- **The projective bundle** `P(E) = Proj_X S(E)` of a locally free `𝒪_X`-module `E` of finite
rank on a Noetherian scheme `X` (Hartshorne II.7, p. 162). -/
def projectiveBundle [IsNoetherian X] : Scheme.{u} :=
  (symmetricRelativeProjData hE hfin).relativeProj

/-- The projection `π : P(E) ⟶ X`. -/
def projectiveBundleProj [IsNoetherian X] : projectiveBundle hE hfin ⟶ X :=
  (symmetricRelativeProjData hE hfin).projection

end

end AlgebraicGeometry.Scheme.Modules

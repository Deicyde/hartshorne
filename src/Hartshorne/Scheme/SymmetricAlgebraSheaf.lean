/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Sym.Card
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Hartshorne.Scheme.SheafTensorAlgebras
import Hartshorne.RingedSpace.PicardGroup

/-!
# The graded symmetric-algebra sheaf of a finite locally free module

Scratch.
-/

universe u

open CategoryTheory TopologicalSpace Opposite Limits
open scoped TensorProduct

namespace Hartshorne

namespace SheafTensorOperations

section SymmetricPowerBasis

variable {A : Type u} [CommRing A] {M : Type u} [AddCommGroup M] [Module A M]
  {ι : Type u} [LinearOrder ι] (d : ℕ)

variable (ι) in
/-- The monotone words of length `d` in `ι`; they index the monomials of degree `d` in
variables indexed by `ι`. -/
abbrev MonotoneWord := {w : Fin d → ι // Monotone w}

noncomputable instance [Finite ι] : Fintype (MonotoneWord ι d) := Fintype.ofFinite _

/-- The monotone rearrangement of a word. -/
noncomputable def MonotoneWord.sort (w : Fin d → ι) : MonotoneWord ι d :=
  ⟨w ∘ Tuple.sort w, Tuple.monotone_sort w⟩

/-- The multiset of letters of a monotone word. -/
def MonotoneWord.toSym (w : MonotoneWord ι d) : Sym ι d :=
  ⟨(List.ofFn w.1 : Multiset ι), by simp⟩

theorem MonotoneWord.toSym_injective : Function.Injective (MonotoneWord.toSym (ι := ι) d) := by
  intro w w' h
  have h' : List.ofFn w.1 = List.ofFn w'.1 :=
    List.Perm.eq_of_pairwise' w.2.sortedLE_ofFn.pairwise w'.2.sortedLE_ofFn.pairwise
      (Multiset.coe_eq_coe.mp (congrArg Subtype.val h))
  exact Subtype.ext (List.ofFn_injective h')

theorem MonotoneWord.toSym_surjective : Function.Surjective (MonotoneWord.toSym (ι := ι) d) := by
  intro s
  let l := s.1.sort (· ≤ ·)
  have hl : l.length = d := by simp [l, Multiset.length_sort]
  have hmono : Monotone l.get :=
    List.sortedLE_iff_pairwise.mpr (Multiset.pairwise_sort _ _)
  refine ⟨⟨fun i => l.get (Fin.cast hl.symm i), fun i j hij => hmono hij⟩, ?_⟩
  apply Subtype.ext
  change ((List.ofFn fun i => l.get (Fin.cast hl.symm i) : List ι) : Multiset ι) = s.1
  have : (List.ofFn fun i => l.get (Fin.cast hl.symm i)) = l := by
    apply List.ext_get (by simp [hl])
    intro n h1 h2
    simp
  rw [this]
  exact Multiset.sort_eq _ _

/-- Monotone words of length `d` correspond to multisets of size `d`. -/
noncomputable def MonotoneWord.equivSym : MonotoneWord ι d ≃ Sym ι d :=
  Equiv.ofBijective _ ⟨MonotoneWord.toSym_injective d, MonotoneWord.toSym_surjective d⟩

/-- **Stars and bars.** There are `C(n + d - 1, d)` monotone words of length `d` in `n` letters. -/
theorem MonotoneWord.card [Fintype ι] :
    Fintype.card (MonotoneWord ι d) = (Fintype.card ι + d - 1).choose d := by
  classical
  rw [Fintype.card_congr (MonotoneWord.equivSym d), Sym.card_sym_eq_choose]

variable (A M) in
/-- The monomial `b_{w 1} ⋯ b_{w d}` in `Sym^d M` attached to a family `b` and a monotone word
`w`. -/
noncomputable def symmetricMonomial (b : ι → M) (w : MonotoneWord ι d) :
    SymmetricPowerQuotient A M d :=
  symmetricPowerTprod A M d (b ∘ w.1)

theorem symmetricPowerTprod_comp_eq_monomial (b : ι → M) (w : Fin d → ι) :
    symmetricPowerTprod A M d (b ∘ w) = symmetricMonomial A M d b (MonotoneWord.sort d w) :=
  (symmetricPowerTprod_perm d (Tuple.sort w) (b ∘ w)).symm

theorem symmetricPowerMap_symmetricMonomial {B N : Type u} [CommRing B] [AddCommGroup N]
    [Module B N] (σ : A →+* B) (f : M →ₛₗ[σ] N) (b : ι → M) (w : MonotoneWord ι d) :
    symmetricPowerMap d σ f (symmetricMonomial A M d b w) = symmetricMonomial B N d (f ∘ b) w :=
  symmetricPowerMap_tprod d σ f _

/-- The exponent vector of the monomial attached to a monotone word. -/
noncomputable def MonotoneWord.exponent (w : MonotoneWord ι d) : ι →₀ ℕ :=
  ∑ i, Finsupp.single (w.1 i) 1

theorem MonotoneWord.exponent_injective :
    Function.Injective (MonotoneWord.exponent (ι := ι) d) := by
  intro w w' h
  apply MonotoneWord.toSym_injective d
  apply Subtype.ext
  have key : ∀ v : MonotoneWord ι d, Finsupp.toMultiset (MonotoneWord.exponent d v) =
      (MonotoneWord.toSym d v).1 := by
    intro v
    simp only [MonotoneWord.exponent, map_sum, Finsupp.toMultiset_single, one_nsmul,
      MonotoneWord.toSym]
    rw [← Fin.univ_val_map, Finset.sum_eq_multiset_sum]
    conv_rhs => rw [← Multiset.sum_map_singleton (Multiset.map _ _), Multiset.map_map]
    rfl
  rw [← key, ← key, h]

variable [Fintype ι]

/-- **`Sym^d` of a free module is free on the monomials of degree `d`.** If `b` is a basis of `M`
(the linear combination map `(ι → A) → M` is bijective), then the monomials
`b_{w 1} ⋯ b_{w d}`, for monotone words `w` of length `d`, form a basis of `Sym^d M`. -/
theorem symmetricMonomial_bijective {b : ι → M}
    (hb : Function.Bijective (Fintype.linearCombination A b)) :
    Function.Bijective (Fintype.linearCombination A (symmetricMonomial A M d b)) := by
  classical
  let L := LinearEquiv.ofBijective _ hb
  have hm : ∀ m : M, m = ∑ j, L.symm m j • b j := fun m => by
    conv_lhs => rw [← L.apply_symm_apply m]
    exact Fintype.linearCombination_apply _ _ _
  have hLb : ∀ j, L.symm (b j) = Pi.single j 1 := fun j => by
    rw [LinearEquiv.symm_apply_eq]
    change b j = Fintype.linearCombination A b (Pi.single j 1)
    rw [Fintype.linearCombination_apply_single, one_smul]
  constructor
  · rw [← linearIndependent_iff_injective_fintypeLinearCombination]
    let g : M →ₗ[A] MvPolynomial ι A :=
      Fintype.linearCombination A (fun j => MvPolynomial.X j) ∘ₗ L.symm.toLinearMap
    have hg : ∀ j, g (b j) = MvPolynomial.X j := fun j => by
      change Fintype.linearCombination A _ (L.symm (b j)) = _
      rw [hLb, Fintype.linearCombination_apply_single, one_smul]
    let φ : MultilinearMap A (fun _ : Fin d => M) (MvPolynomial ι A) :=
      (MultilinearMap.mkPiAlgebra A (Fin d) (MvPolynomial ι A)).compLinearMap (fun _ => g)
    have hφ : ∀ (e : Equiv.Perm (Fin d)) (m : Fin d → M), φ (m ∘ e) = φ m := fun e m => by
      simp only [φ, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
        Function.comp_apply]
      exact Equiv.prod_comp e (fun i => g (m i))
    let Ψ := symmetricPowerLift d φ hφ
    have hΨ : Ψ ∘ symmetricMonomial A M d b =
        (MvPolynomial.basisMonomials ι A) ∘ MonotoneWord.exponent d := by
      funext w
      simp only [Function.comp_apply, Ψ, symmetricMonomial, symmetricPowerLift_tprod, φ,
        MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply, hg,
        MvPolynomial.coe_basisMonomials, MonotoneWord.exponent, MvPolynomial.monomial_sum_one]
      rfl
    refine LinearIndependent.of_comp Ψ ?_
    rw [hΨ]
    exact (MvPolynomial.basisMonomials ι A).linearIndependent.comp _
      (MonotoneWord.exponent_injective d)
  · rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, eq_top_iff,
      ← span_symmetricPowerTprod d, Submodule.span_le]
    rintro _ ⟨m, rfl⟩
    rw [show m = fun i => ∑ j, L.symm (m i) j • b j from funext fun i => hm (m i),
      MultilinearMap.map_sum]
    refine Submodule.sum_mem _ fun r _ => ?_
    rw [MultilinearMap.map_smul_univ]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨MonotoneWord.sort d r, ?_⟩)
    exact (symmetricPowerTprod_comp_eq_monomial d b r).symm

end SymmetricPowerBasis

end SheafTensorOperations

namespace Ringed

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

open SheafAlgebraOperations ModuleSheafTensor SheafTensorOperations

section FrameSheafify

variable {P : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)} {U : Opens X}
  {ι : Type u} [Fintype ι] (c : ι → P.obj (op U))

/-- The restrictions `c_i|_V` of a family of sections over `U` to an open `V ⊆ U`. -/
noncomputable def presheafRestrictFamily {V : Opens X} (h : V ≤ U) : ι → P.obj (op V) :=
  fun i => P.map (homOfLE h).op (c i)

/-- The map `(a_i) ↦ ∑ a_i c_i|_V` for a family of sections `c` of a presheaf of modules over `U`
and an open `V ⊆ U`. -/
noncomputable def presheafFrameMap {V : Opens X} (h : V ≤ U) :
    (ι → (R.obj ⋙ forget₂ CommRingCat RingCat).obj (op V)) →ₗ[
      (R.obj ⋙ forget₂ CommRingCat RingCat).obj (op V)] P.obj (op V) :=
  Fintype.linearCombination _ (presheafRestrictFamily c h)

theorem presheafFrameMap_restrict {V W : Opens X} (h : V ≤ U) (hWV : W ≤ V)
    (a : ι → (R.obj ⋙ forget₂ CommRingCat RingCat).obj (op V)) :
    P.map (homOfLE hWV).op (presheafFrameMap c h a) =
      presheafFrameMap c (hWV.trans h)
        (fun i => ((R.obj ⋙ forget₂ CommRingCat RingCat).map (homOfLE hWV).op).hom (a i)) := by
  rw [presheafFrameMap, presheafFrameMap, Fintype.linearCombination_apply,
    Fintype.linearCombination_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine (PresheafOfModules.map_smul P (homOfLE hWV).op (a i)
    (presheafRestrictFamily c h i)).trans ?_
  congr 1
  exact (PresheafOfModules.map_comp_apply P _ _ (c i)).symm

/-- The images in the sheafification of a family of sections of a presheaf of modules. -/
noncomputable def sheafifyFamily : ι → (sheafify P).val.presheaf.obj (op U) :=
  fun i => (sheafifyUnit P).app (op U) (c i)

/-- If a family of sections `c` of a presheaf of modules over `U` restricts to a basis over every
open `V ⊆ U`, its image in the sheafification is a local frame over `U`. -/
theorem isLocalFrame_sheafify
    (hc : ∀ (V : Opens X) (h : V ≤ U), Function.Bijective (presheafFrameMap c h)) :
    IsLocalFrame (sheafify P) U (sheafifyFamily c) := by
  have key : ∀ (V : Opens X) (h : V ≤ U) a,
      localFrameMap (sheafify P) (sheafifyFamily c) h a =
        (sheafifyUnit P).app (op V) (presheafFrameMap c h a) := by
    intro V h a
    rw [localFrameMap_apply, presheafFrameMap, Fintype.linearCombination_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    congr 1
    rw [presheafRestrictFamily]
    exact (PresheafOfModules.naturality_apply (sheafifyUnit P) (homOfLE h).op (c i)).symm
  have hinj : ∀ (V : Opens X) (h : V ≤ U) a b,
      (sheafifyUnit P).app (op V) (presheafFrameMap c h a) =
        (sheafifyUnit P).app (op V) (presheafFrameMap c h b) → a = b := by
    intro V h a b hab
    funext i
    apply TopCat.Presheaf.section_ext R V
    intro x hx
    have hg : sectionGerm P x V hx (presheafFrameMap c h a) =
        sectionGerm P x V hx (presheafFrameMap c h b) := by
      apply (stalkMap_sheafifyUnit_bijective P x).1
      rw [stalkMap_germ, stalkMap_germ, hab]
    obtain ⟨W, hxW, iW, iW', he⟩ := TopCat.Presheaf.germ_eq P.presheaf x hx hx _ _ hg
    have hWV : W ≤ V := leOfHom iW
    have he' : P.map (homOfLE hWV).op (presheafFrameMap c h a) =
        P.map (homOfLE hWV).op (presheafFrameMap c h b) := he
    rw [presheafFrameMap_restrict, presheafFrameMap_restrict] at he'
    have hi := congrFun ((hc W (hWV.trans h)).1 he') i
    rw [← TopCat.Presheaf.germ_res_apply R.obj (homOfLE hWV) x hxW,
      ← TopCat.Presheaf.germ_res_apply R.obj (homOfLE hWV) x hxW]
    exact congrArg _ hi
  intro V h
  constructor
  · intro a b hab
    rw [key, key] at hab
    exact hinj V h a b hab
  · intro s
    change (sheafify P).val.obj (op V) at s
    have hloc : ∀ x : V, ∃ (W : Opens X) (_ : x.1 ∈ W) (i : W ⟶ V) (p : P.obj (op W)),
        (sheafifyUnit P).app (op W) p = (sheafify P).val.map i.op s :=
      fun x => exists_unit_eq_map P s x.2
    choose W hxW iW p hp using hloc
    have hWU : ∀ x, W x ≤ U := fun x => (leOfHom (iW x)).trans h
    choose a ha using fun x => (hc (W x) (hWU x)).2 (p x)
    have hcompat : ∀ x y,
        (fun i => ((R.obj ⋙ forget₂ CommRingCat RingCat).map
          (homOfLE (inf_le_left : W x ⊓ W y ≤ W x)).op).hom (a x i)) =
        (fun i => ((R.obj ⋙ forget₂ CommRingCat RingCat).map
          (homOfLE (inf_le_right : W x ⊓ W y ≤ W y)).op).hom (a y i)) := by
      intro x y
      apply hinj (W x ⊓ W y) (inf_le_left.trans (hWU x))
      rw [← presheafFrameMap_restrict c (hWU x) inf_le_left,
        ← presheafFrameMap_restrict c (hWU y) inf_le_right, ha, ha,
        PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply, hp, hp,
        ← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply]
      exact PresheafOfModules.congr_map_apply _ (Subsingleton.elim _ _) s
    have hglue : ∀ i, ∃ g : R.obj.obj (op V), ∀ x, R.obj.map (iW x).op g = a x i := by
      intro i
      obtain ⟨g, hg, -⟩ := TopCat.Sheaf.existsUnique_gluing' R W V iW
        (fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxW _⟩) (fun x => a x i)
        (fun x y => congrFun (hcompat x y) i)
      exact ⟨g, hg⟩
    choose g hg using hglue
    refine ⟨g, ?_⟩
    rw [key]
    apply sheaf_section_ext (sheafify P)
    intro x hx
    refine ⟨W ⟨x, hx⟩, hxW _, iW _, ?_⟩
    rw [← hp, ← PresheafOfModules.naturality_apply]
    congr 1
    rw [← ha]
    refine (presheafFrameMap_restrict c h (leOfHom (iW ⟨x, hx⟩)) g).trans ?_
    congr 1
    funext i
    exact hg i ⟨x, hx⟩

end FrameSheafify

section SymmetricPowerFrame

variable {E : SheafOfModules.{u} (ringCatSheafOf R)} {U : Opens X} {ι : Type u} [Fintype ι]
  [LinearOrder ι] (e : ι → E.val.presheaf.obj (op U)) (d : ℕ)

/-- The monomials of degree `d` in a family of sections `e` of `E` over `U`, as sections over `U`
of the presheaf `V ↦ Sym^d E(V)`. -/
noncomputable def symmetricPowerMonomials :
    MonotoneWord ι d → (moduleSheafSymmetricPowerPresheaf d E).obj (op U) :=
  symmetricMonomial _ (E.val.obj (op U)) d e

/-- The monomials of degree `d` in a family of sections `e` of `E` over `U`, as sections over `U`
of `S^d E`. -/
noncomputable def moduleSheafSymmetricPowerFrame :
    MonotoneWord ι d → (moduleSheafSymmetricPower d E).val.presheaf.obj (op U) :=
  sheafifyFamily (symmetricPowerMonomials e d)

/-- **The symmetric powers of a module with a local frame have a local frame.** If `e` is a
frame of `E` over `U`, the monomials of degree `d` in `e` form a frame of `S^d E` over `U`. -/
theorem IsLocalFrame.moduleSheafSymmetricPower {e : ι → E.val.presheaf.obj (op U)}
    (he : IsLocalFrame E U e) (d : ℕ) :
    IsLocalFrame (moduleSheafSymmetricPower d E) U (moduleSheafSymmetricPowerFrame e d) := by
  refine isLocalFrame_sheafify _ fun V h => ?_
  have hfam : presheafRestrictFamily (symmetricPowerMonomials e d) h =
      symmetricMonomial _ (E.val.obj (op V)) d
        (fun i => E.val.presheaf.map (homOfLE h).op (e i)) := by
    funext w
    exact symmetricPowerMap_symmetricMonomial d _ (E.val.restrictₛₗ (homOfLE h).op) e w
  rw [presheafFrameMap, hfam]
  exact symmetricMonomial_bijective d (he V h)

end SymmetricPowerFrame

section LocallyFree

variable {E : SheafOfModules.{u} (ringCatSheafOf R)}

/-- **Symmetric powers of a locally free module of rank `n`.** If `E` is locally free of rank `n`,
then `S^d E` is locally free of rank `C(n + d - 1, d)`. -/
theorem IsLocallyFreeOfRank.moduleSheafSymmetricPower {n : ℕ} (hE : IsLocallyFreeOfRank E n)
    (d : ℕ) : IsLocallyFreeOfRank (moduleSheafSymmetricPower d E) ((n + d - 1).choose d) := by
  apply isLocallyFreeOfRank_of_isLocalFrame
  intro x
  obtain ⟨U, e, hx, he⟩ := exists_isLocalFrame_of_isLocallyFreeOfRank hE x
  let : LinearOrder (ULift.{u} (Fin n)) :=
    LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective
  have hcard : Fintype.card (ULift.{u} (Fin ((n + d - 1).choose d))) =
      Fintype.card (MonotoneWord (ULift.{u} (Fin n)) d) := by
    rw [MonotoneWord.card]
    simp
  exact ⟨U, _, hx, (he.moduleSheafSymmetricPower d).reindex (Fintype.equivOfCardEq hcard)⟩

/-- **Symmetric powers of a locally free module of finite rank are locally free of finite
rank.** -/
theorem IsFiniteLocallyFree.moduleSheafSymmetricPower (hE : IsFiniteLocallyFree E) (d : ℕ) :
    IsFiniteLocallyFree (moduleSheafSymmetricPower d E) := by
  classical
  intro x
  obtain ⟨U, hx, n, ⟨α⟩⟩ := hE x
  let : LinearOrder (ULift.{u} (Fin n)) :=
    LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective
  have he := (isLocalFrame_of_over_iso α).moduleSheafSymmetricPower d
  let N := Fintype.card (MonotoneWord (ULift.{u} (Fin n)) d)
  have hcard : Fintype.card (ULift.{u} (Fin N)) =
      Fintype.card (MonotoneWord (ULift.{u} (Fin n)) d) := by simp [N]
  exact ⟨U, hx, N,
    nonempty_over_iso_free_of_isLocalFrame (he.reindex (Fintype.equivOfCardEq hcard))⟩

set_option backward.isDefEq.respectTransparency false in
private lemma isIso_ofEpi_free_π {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {S : Sheaf J RingCat.{u}} [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] {N : SheafOfModules.{u} S} {I : Type u}
    (β : SheafOfModules.free I ≅ N) :
    IsIso ((SheafOfModules.free.generatingSections I).ofEpi β.hom).π := by
  rw [SheafOfModules.GeneratingSections.ofEpi_π]
  infer_instance

/-- A module sheaf which is locally free of finite rank is of finite presentation: locally it is
a finite free module, with no relations. -/
theorem IsFiniteLocallyFree.isFinitePresentation {M : SheafOfModules.{u} (ringCatSheafOf R)}
    (hM : IsFiniteLocallyFree M) : SheafOfModules.IsFinitePresentation.{u, u, u} M := by
  choose U hxU n α using hM
  let q : M.LocalGeneratorsData :=
    { I := X
      X := U
      coversTop := by
        rw [Opens.coversTop_iff, IsOpenCover, eq_top_iff]
        exact fun x _ => Opens.mem_iSup.mpr ⟨x, hxU x⟩
      generators := fun x =>
        (SheafOfModules.free.generatingSections (ULift.{u} (Fin (n x)))).ofEpi
          (α x).some.symm.hom }
  have : q.IsLocallyFreeData := by
    constructor
    intro x
    exact isIso_ofEpi_free_π (α x).some.symm
  have hq : q.quasiCoherentData.IsFinitePresentation := by
    constructor
    intro x
    constructor
    · exact ⟨inferInstanceAs (Finite (ULift.{u} (Fin (n x))))⟩
    · exact ⟨inferInstanceAs (Finite (ULift.{u} Empty))⟩
  exact SheafOfModules.IsFinitePresentation.mk.{u, u, u} ⟨q.quasiCoherentData, hq⟩

end LocallyFree

end Ringed

end Hartshorne

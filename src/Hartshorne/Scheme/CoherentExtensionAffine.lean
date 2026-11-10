/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.IdealPowerProduct
import Hartshorne.Scheme.QcqsPushforwardQuasicoherent

/-!
# Extension of coherent subsheaves on an affine Noetherian scheme

Hartshorne, *Algebraic Geometry*, II, Exercise 5.15 (pp. 126–127).

## The submodule sheaf spanned by global sections

For an `𝒪_X`-module `E` and a set `S` of global sections, `spanSheaf S` is the submodule sheaf of
`E` of sections lying, near every point, in the span of the restrictions of `S` over an affine
open. If `E` is quasi-coherent:

* `sub_spanSheaf_eq`: over every affine open `V` its sections are exactly the span of `S|_V`;
* `isQuasicoherent_spanSheaf`: it is quasi-coherent;
* `isCoherent_spanSheaf`: it is coherent when `S` is finite and `X` is locally Noetherian.

## Extension from an open subset

Let `X` be an affine Noetherian scheme and `E` a quasi-coherent `𝒪_X`-module.

* `exists_finite_mem_spanSheaf`: every section of `E` over an open is a section of the span of
  finitely many global sections, so `E` is the directed union of coherent subsheaves (the content
  of Exercise 5.15(a));
* `exists_isCoherent_extension`: if `U ⊆ X` is open and `N ⊆ E` is a submodule sheaf whose
  restriction to `U` is coherent, there is a coherent `N' ⊆ E` agreeing with `N` on every open
  `V ⊆ U` (Exercise 5.15(c));
* `exists_isCoherent_restrict_iso`: every coherent sheaf on an open `U ⊆ X` is the restriction of
  a coherent sheaf on `X` (Exercise 5.15(b)), by the previous item applied to the pushforward of
  the sheaf to `X`, which is quasi-coherent.

For the second, cover `U` by finitely many basic opens `D(g) ⊆ U` and choose generators `t` of the
finitely generated `Γ(X, D(g))`-modules `N(D(g))`. Some `gⁿ t` is the restriction of a global
section `s` of `E` (II.5.3(b) for `E`); a further power of `g` puts `s` in `N` over each `D(g')`
of the cover (II.5.3 for `N` on `D(g')` and for `E`), hence in `N` over `U`
(`exists_global_extension`). The span of these finitely many `s` is the required `N'`.

The extension lemma for `N` uses only that `N` is quasi-coherent on the affine open in question
(`exists_pow_smul_extension_of_isLocalizing`).
-/

noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace Hartshorne

universe u

open ArtinReesKernelSheaf

variable {X : Scheme.{u}} {E : X.Modules}

/-! ### The submodule sheaf spanned by global sections -/

/-- Restriction maps the span of the restrictions of `S` to the span of the restrictions of
`S`. -/
lemma res_mem_span {V W : X.Opens} (h : W ≤ V) (S : Set Γ(E, ⊤)) {s : Γ(E, V)}
    (hs : s ∈ Submodule.span Γ(X, V) (res E (le_top : V ≤ ⊤) '' S)) :
    res E h s ∈ Submodule.span Γ(X, W) (res E (le_top : W ≤ ⊤) '' S) := by
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ht, rfl⟩ := hx
    rw [res_res]
    exact Submodule.subset_span ⟨t, ht, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hx

/-- The family `V ↦ span (S|_V)` on affine opens. -/
def spanFamily (S : Set Γ(E, ⊤)) : AffineFamily E where
  obj V := Submodule.span Γ(X, V) (res E le_top '' S)
  res_mem h _ hs := res_mem_span h S hs

/-- The submodule sheaf of `E` spanned by a set `S` of global sections: the sections lying, near
every point, in the span of `S|_V` on an affine open `V`. -/
def spanSheaf (S : Set Γ(E, ⊤)) : E.val.Submodule :=
  (spanFamily S).closure

lemma isLocal_spanSheaf (S : Set Γ(E, ⊤)) : IsLocal (spanSheaf S) :=
  AffineFamily.isLocal_closure _

lemma span_le_sub_spanSheaf (S : Set Γ(E, ⊤)) (V : X.affineOpens) :
    Submodule.span Γ(X, V) (res E le_top '' S) ≤ sub (spanSheaf S) V := fun _ hs x hx =>
  ⟨V, le_rfl, hx, by rwa [res_refl]⟩

lemma spanSheaf_mono {S S' : Set Γ(E, ⊤)} (h : S ⊆ S') : spanSheaf S ≤ spanSheaf S' :=
  AffineFamily.closure_mono fun _ => Submodule.span_mono (Set.image_mono h)

/-- The sections over `D(g)` which, after multiplication by a power of `g`, are restrictions of
elements of a submodule `P` of the sections over the affine open `V`. -/
def powSmulRes (V : X.affineOpens) (g : Γ(X, V)) (P : Submodule Γ(X, V) Γ(E, V)) :
    Submodule Γ(X, X.basicOpen g) Γ(E, X.basicOpen g) where
  carrier := {t | ∃ (n : ℕ) (p : Γ(E, V)), p ∈ P ∧
    (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom g ^ n • t =
      res E (X.basicOpen_le g) p}
  zero_mem' := ⟨0, 0, zero_mem _, by rw [smul_zero, map_zero]⟩
  add_mem' := by
    rintro t₁ t₂ ⟨n₁, p₁, hp₁, h₁⟩ ⟨n₂, p₂, hp₂, h₂⟩
    refine ⟨n₁ + n₂, g ^ n₂ • p₁ + g ^ n₁ • p₂,
      add_mem (Submodule.smul_mem _ _ hp₁) (Submodule.smul_mem _ _ hp₂), ?_⟩
    rw [map_add, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, ← h₁, ← h₂, map_pow, map_pow,
      smul_add, smul_smul, smul_smul, ← pow_add, ← pow_add, add_comm n₂ n₁]
  smul_mem' := by
    rintro c t ⟨n, p, hp, h⟩
    have hloc : IsLocalization.Away g Γ(X, X.basicOpen g) := V.2.isLocalization_basicOpen g
    obtain ⟨⟨a, _, m, rfl⟩, hc⟩ :=
      IsLocalization.surj (R := Γ(X, V)) (S := Γ(X, X.basicOpen g)) (Submonoid.powers g) c
    change c * (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom (g ^ m) =
      (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom a at hc
    refine ⟨n + m, a • p, Submodule.smul_mem _ _ hp, ?_⟩
    rw [LinearMap.map_smulₛₗ, ← h, ← hc, smul_smul, smul_smul, map_pow]
    congr 1
    ring

lemma span_le_powSmulRes (S : Set Γ(E, ⊤)) (V : X.affineOpens) (g : Γ(X, V)) :
    Submodule.span Γ(X, X.basicOpen g) (res E le_top '' S) ≤
      powSmulRes V g (Submodule.span Γ(X, V) (res E le_top '' S)) := by
  rw [Submodule.span_le]
  rintro _ ⟨t, ht, rfl⟩
  refine ⟨0, res E le_top t, Submodule.subset_span ⟨t, ht, rfl⟩, ?_⟩
  rw [pow_zero, one_smul, res_res]

/-- The local step: if the restriction of `s` to a basic open `D(g)` of the affine open `V` lies
in the span of `S|_{D(g)}`, then `g ^ n s` lies in the span of `S|_V` for some `n`. -/
theorem exists_pow_smul_mem_span [E.IsQuasicoherent] (S : Set Γ(E, ⊤)) (V : X.affineOpens)
    (g : Γ(X, V)) {s : Γ(E, V)}
    (hs : res E (X.basicOpen_le g) s ∈ Submodule.span Γ(X, X.basicOpen g) (res E le_top '' S)) :
    ∃ n : ℕ, g ^ n • s ∈ Submodule.span Γ(X, V) (res E le_top '' S) := by
  obtain ⟨n, p, hp, h⟩ := span_le_powSmulRes S V g hs
  have hres : res E (X.basicOpen_le g) (g ^ n • s - p) = 0 := by
    rw [map_sub, LinearMap.map_smulₛₗ, map_pow, h, sub_self]
  obtain ⟨m, hm⟩ := exists_pow_smul_eq_zero_of_isAffineOpen E V.2 g _ hres
  rw [smul_sub, sub_eq_zero, smul_smul, ← pow_add] at hm
  exact ⟨m + n, hm ▸ Submodule.smul_mem _ _ hp⟩

/-- **Sections of the span sheaf on an affine open.** If `E` is quasi-coherent, then over every
affine open `V` the sections of `spanSheaf S` are exactly the span of `S|_V`. -/
theorem sub_spanSheaf_eq [E.IsQuasicoherent] (S : Set Γ(E, ⊤)) (V : X.affineOpens) :
    sub (spanSheaf S) V = Submodule.span Γ(X, V) (res E le_top '' S) := by
  refine le_antisymm (fun s hs => ?_) (span_le_sub_spanSheaf S V)
  set P := Submodule.span Γ(X, V) (res E (le_top : (V : X.Opens) ≤ ⊤) '' S)
  let T : Set Γ(X, V) := {g | ∃ n : ℕ, g ^ n • s ∈ P}
  have hT : Ideal.span T = ⊤ := by
    rw [← V.2.self_le_iSup_basicOpen_iff]
    intro x hxV
    obtain ⟨W, hWV, hxW, hW⟩ := hs x hxV
    have hWV' : (W : X.Opens) ≤ V := hWV
    obtain ⟨g, hgW, hxg⟩ := V.2.exists_basicOpen_le ⟨x, hxW⟩ hxV
    have hD := res_mem_span (V := W) (W := X.basicOpen g) hgW S hW
    rw [res_res] at hD
    exact Opens.mem_iSup.2 ⟨⟨g, exists_pow_smul_mem_span S V g hD⟩, hxg⟩
  exact Submodule.mem_of_span_eq_top_of_smul_pow_mem P T hT s fun g => g.2

/-- **The span sheaf is quasi-coherent** when `E` is. -/
theorem isQuasicoherent_spanSheaf [E.IsQuasicoherent] (S : Set Γ(E, ⊤)) :
    (toModules (spanSheaf S) (isLocal_spanSheaf S)).IsQuasicoherent := by
  refine isQuasicoherent_of_pow_smul _ (fun U g s hs => ?_) (fun U g t => ?_)
  · let s' : (spanSheaf S).obj (op (U : X.Opens)) := s
    have hs' := congrArg (fun x : (spanSheaf S).obj (op (X.basicOpen g)) => x.1) hs
    obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_isAffineOpen E U.2 g s'.1 hs'
    exact ⟨n, Subtype.ext hn⟩
  · let t' : (spanSheaf S).obj (op (X.basicOpen g)) := t
    have ht : t'.1 ∈ Submodule.span Γ(X, X.basicOpen g) (res E le_top '' S) :=
      (sub_spanSheaf_eq S (X.affineBasicOpen g)).le t'.2
    obtain ⟨n, p, hp, h⟩ := span_le_powSmulRes S U g ht
    exact ⟨n, (⟨p, span_le_sub_spanSheaf S U hp⟩ : (spanSheaf S).obj (op (U : X.Opens))),
      Subtype.ext h.symm⟩

/-- **The span of finitely many global sections is coherent**, for a quasi-coherent `E` on a
locally Noetherian scheme. -/
theorem isCoherent_spanSheaf [IsLocallyNoetherian X] [E.IsQuasicoherent] (S : Set Γ(E, ⊤))
    (hS : S.Finite) : IsCoherent (toModules (spanSheaf S) (isLocal_spanSheaf S)) := by
  have hiso := ((quasicoherent_affine_local_tfae _).out 0 2).mp (isQuasicoherent_spanSheaf S)
  refine ((coherent_affine_local_tfae _).out 3 0).mp ?_
  intro U
  refine ⟨?_, hiso U⟩
  change Module.Finite Γ(X, U) (sub (spanSheaf S) U)
  rw [sub_spanSheaf_eq S U]
  exact Module.Finite.span_of_finite _ (hS.image _)

/-! ### Extension from an open subset of an affine Noetherian scheme -/

/-- A unit multiple of `y` lying in a submodule forces `y` into it. -/
lemma mem_of_isUnit_smul_mem {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (P : Submodule R M) {c : R} (hc : IsUnit c) {y : M} (h : c • y ∈ P) : y ∈ P := by
  obtain ⟨u, rfl⟩ := hc
  have := P.smul_mem (↑u⁻¹ : R) h
  rwa [smul_smul, Units.inv_mul, one_smul] at this

variable {U : X.Opens} {N : E.val.Submodule}

/-- The extension property of a quasi-coherent submodule sheaf `N` over the affine opens contained
in `U`: a section of `N` over a basic open `D(g)` of such an affine open `V` extends to `V` after
multiplication by a power of `g`. -/
def ExtendsOver (U : X.Opens) (N : E.val.Submodule) : Prop :=
  ∀ (V : X.affineOpens), (V : X.Opens) ≤ U → ∀ (g : Γ(X, V)) (t : Γ(E, X.basicOpen g)),
    t ∈ sub N (X.basicOpen g) → ∃ (n : ℕ) (u : Γ(E, V)), u ∈ sub N V ∧
      res E (X.basicOpen_le g) u = (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom g ^ n • t

/-- If a global section `s₀` of a quasi-coherent `E` on an affine scheme lies in `N` over `D(g)`,
then some `g ^ k s₀` lies in `N` over `D(g')`, for every `D(g') ⊆ U`. -/
theorem exists_pow_smul_res_mem [IsAffine X] [E.IsQuasicoherent] (hext : ExtendsOver U N)
    {g' : Γ(X, ⊤)} (hg' : X.basicOpen g' ≤ U) (g : Γ(X, ⊤)) {s₀ : Γ(E, ⊤)}
    (hs₀ : res E (X.basicOpen_le g) s₀ ∈ sub N (X.basicOpen g)) :
    ∃ k : ℕ, res E (X.basicOpen_le g') (g ^ k • s₀) ∈ sub N (X.basicOpen g') := by
  let T : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  let V : X.affineOpens := X.affineBasicOpen (U := T) g'
  let h : Γ(X, V) := (X.presheaf.map (homOfLE (X.basicOpen_le g')).op).hom g
  have hDh : X.basicOpen h ≤ X.basicOpen g := by
    change X.basicOpen ((X.presheaf.map (homOfLE (X.basicOpen_le g')).op) g) ≤ _
    rw [Scheme.basicOpen_res]
    exact inf_le_right
  let s₁ : Γ(E, V) := res E (X.basicOpen_le g') s₀
  have hr : res E (X.basicOpen_le h) s₁ ∈ sub N (X.basicOpen h) := by
    have := res_mem N hDh hs₀
    rw [res_res] at this
    rw [show res E (X.basicOpen_le h) s₁ = res E (hDh.trans (X.basicOpen_le g)) s₀ from
      res_res E (X.basicOpen_le g') (X.basicOpen_le h) s₀]
    exact this
  obtain ⟨k, u, hu, e⟩ := hext V hg' h _ hr
  have hres : res E (X.basicOpen_le h) (h ^ k • s₁ - u) = 0 := by
    rw [map_sub, LinearMap.map_smulₛₗ, map_pow, e, sub_self]
  obtain ⟨l, hl⟩ := exists_pow_smul_eq_zero_of_isAffineOpen E V.2 h _ hres
  rw [smul_sub, sub_eq_zero, smul_smul, ← pow_add] at hl
  refine ⟨l + k, ?_⟩
  rw [LinearMap.map_smulₛₗ, map_pow]
  change h ^ (l + k) • s₁ ∈ _
  rw [hl]
  exact Submodule.smul_mem _ _ hu

/-- **Extending a local section of `N` to a global section of `E`.** On an affine scheme, a
section `t` of `N` over `D(g)` is, after multiplication by a power of `g`, the restriction of a
global section of `E` which lies in `N` over each of finitely many basic opens `D(g') ⊆ U`. -/
theorem exists_global_extension [IsAffine X] [E.IsQuasicoherent] (hext : ExtendsOver U N)
    (G : Finset Γ(X, ⊤)) (hG : ∀ g' ∈ G, X.basicOpen g' ≤ U) (g : Γ(X, ⊤))
    {t : Γ(E, X.basicOpen g)} (ht : t ∈ sub N (X.basicOpen g)) :
    ∃ (n : ℕ) (s : Γ(E, ⊤)),
      res E (X.basicOpen_le g) s = (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom g ^ n • t ∧
      ∀ g' ∈ G, res E (X.basicOpen_le g') s ∈ sub N (X.basicOpen g') := by
  obtain ⟨m, s₀, hs₀⟩ := exists_pow_smul_extension_of_isAffineOpen E (isAffineOpen_top X) g t
  replace hs₀ : res E (X.basicOpen_le g) s₀ =
      (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom g ^ m • t := hs₀
  have hs₀N : res E (X.basicOpen_le g) s₀ ∈ sub N (X.basicOpen g) := by
    rw [hs₀]
    exact Submodule.smul_mem _ _ ht
  choose k hk using fun (g' : Γ(X, ⊤)) (hg' : g' ∈ G) =>
    exists_pow_smul_res_mem hext (hG g' hg') g hs₀N
  let K : ℕ := ∑ g' ∈ G.attach, k g'.1 g'.2
  refine ⟨K + m, g ^ K • s₀, ?_, fun g' hg' => ?_⟩
  · rw [LinearMap.map_smulₛₗ, map_pow, hs₀, smul_smul, ← pow_add]
  · have hle : k g' hg' ≤ K :=
      Finset.single_le_sum (f := fun g'' : G => k g''.1 g''.2) (fun _ _ => Nat.zero_le _)
        (Finset.mem_attach _ ⟨g', hg'⟩)
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le' hle
    rw [hj, pow_add, ← smul_smul, LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ (hk g' hg')

/-- The core of `exists_isCoherent_extension`, with the coherence of `N` on `U` given by the
sections of `N` over the affine opens `V ⊆ U`: `N(V)` is a finitely generated `Γ(X, V)`-module and
sections over basic opens of `V` extend to `V` after multiplication by a power. Then, for `X`
affine Noetherian and `E` quasi-coherent, there is a coherent submodule sheaf `N' ⊆ E` with
`N'(V) = N(V)` for every open `V ⊆ U`. -/
theorem exists_isCoherent_eq_on [IsAffine X] [IsNoetherian X] [E.IsQuasicoherent]
    (hN : IsLocal N) (hext : ExtendsOver U N)
    (hfin : ∀ V : X.affineOpens, (V : X.Opens) ≤ U → Module.Finite Γ(X, V) (sub N V)) :
    ∃ (N' : E.val.Submodule) (hN' : IsLocal N'), IsCoherent (toModules N' hN') ∧
      ∀ V : X.Opens, V ≤ U → sub N' V = sub N V := by
  classical
  let T : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  -- A finite cover of `U` by basic opens `D(g) ⊆ U`.
  have hcov : ∀ x : U, ∃ g : Γ(X, ⊤), X.basicOpen g ≤ U ∧ (x : X) ∈ X.basicOpen g :=
    fun x => (isAffineOpen_top X).exists_basicOpen_le x trivial
  choose gx hgxU hgx using hcov
  obtain ⟨F, hF⟩ := (NoetherianSpace.isCompact (U : Set X)).elim_finite_subcover
    (fun x : U => (X.basicOpen (gx x) : Set X)) (fun _ => (X.basicOpen _).isOpen)
    (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hgx _⟩)
  let G : Finset Γ(X, ⊤) := F.image gx
  have hG : ∀ g ∈ G, X.basicOpen g ≤ U := by
    intro g hg
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hg
    exact hgxU x
  have hGcov : ∀ x ∈ U, ∃ g ∈ G, x ∈ X.basicOpen g := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (hF hx)
    exact ⟨gx y, Finset.mem_image_of_mem _ hy, hxy⟩
  -- Finite generating sets of `N` over the `D(g)`.
  have hfin' : ∀ g ∈ G, Module.Finite Γ(X, X.basicOpen g) (sub N (X.basicOpen g)) :=
    fun g hg => hfin (X.affineBasicOpen (U := T) g) (hG g hg)
  choose Tg hTgfin hTgspan using fun (g : Γ(X, ⊤)) (hg : g ∈ G) =>
    Submodule.fg_def.1 (Module.Finite.iff_fg.1 (hfin' g hg))
  have hTgN : ∀ g (hg : g ∈ G), ∀ t ∈ Tg g hg, t ∈ sub N (X.basicOpen g) := fun g hg t ht =>
    hTgspan g hg ▸ Submodule.subset_span ht
  choose n s hsA hsB using fun (g : Γ(X, ⊤)) (hg : g ∈ G) (t : Γ(E, X.basicOpen g))
    (ht : t ∈ Tg g hg) => exists_global_extension hext G hG g (hTgN g hg t ht)
  let S : Set Γ(E, ⊤) := Set.range fun p : Σ g : G, Tg g.1 g.2 => s p.1.1 p.1.2 p.2.1 p.2.2
  have hS : S.Finite := by
    have : ∀ g : G, Finite (Tg g.1 g.2) := fun g => (hTgfin g.1 g.2).to_subtype
    exact Set.finite_range _
  -- The elements of `S` lie in `N` over every open `V ⊆ U`.
  have hSN : ∀ s' ∈ S, ∀ V : X.Opens, V ≤ U → res E (le_top : V ≤ ⊤) s' ∈ sub N V := by
    rintro _ ⟨⟨⟨g, hg⟩, ⟨t, ht⟩⟩, rfl⟩ V hVU
    refine hN V _ fun x hx => ?_
    obtain ⟨g', hg', hxg'⟩ := hGcov x (hVU hx)
    refine ⟨V ⊓ X.basicOpen g', inf_le_left, ⟨hx, hxg'⟩, ?_⟩
    have := res_mem N (inf_le_right : V ⊓ X.basicOpen g' ≤ X.basicOpen g') (hsB g hg t ht g' hg')
    rw [res_res] at this
    rwa [res_res]
  -- The generators of `N(D(g))` lie in the span of `S` over `D(g)`.
  have hTgS : ∀ g (hg : g ∈ G), sub N (X.basicOpen g) ≤
      Submodule.span Γ(X, X.basicOpen g) (res E le_top '' S) := by
    intro g hg
    rw [← hTgspan g hg, Submodule.span_le]
    intro t ht
    have hu : IsUnit ((X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom g ^ n g hg t ht) :=
      (isUnit_res_of_le_basicOpen g (X.basicOpen_le g) le_rfl).pow _
    refine mem_of_isUnit_smul_mem _ hu ?_
    rw [← hsA g hg t ht]
    exact Submodule.subset_span ⟨_, ⟨⟨⟨g, hg⟩, ⟨t, ht⟩⟩, rfl⟩, rfl⟩
  refine ⟨spanSheaf S, isLocal_spanSheaf S, isCoherent_spanSheaf S hS, fun V hVU => ?_⟩
  refine le_antisymm (fun a ha => ?_) (fun a ha => ?_)
  · refine hN V a fun x hx => ?_
    obtain ⟨W, hWV, hxW, hW⟩ := ha x hx
    refine ⟨W, hWV, hxW, ?_⟩
    have hle : Submodule.span Γ(X, W) (res E le_top '' S) ≤ sub N W := by
      rw [Submodule.span_le]
      rintro _ ⟨s', hs', rfl⟩
      exact hSN s' hs' W (hWV.trans hVU)
    exact hle hW
  · intro x hx
    obtain ⟨g, hg, hxg⟩ := hGcov x (hVU hx)
    let D : X.affineOpens := X.affineBasicOpen (U := T) g
    obtain ⟨h, hhV, hxh⟩ := D.2.exists_basicOpen_le (V := V ⊓ X.basicOpen g) ⟨x, hx, hxg⟩ hxg
    let W : X.affineOpens := X.affineBasicOpen (U := D) h
    have hWV : X.basicOpen h ≤ V := hhV.trans inf_le_left
    refine ⟨W, hWV, hxh, ?_⟩
    have hr : res E hWV a ∈ sub N (X.basicOpen h) := res_mem N hWV ha
    obtain ⟨k, u, hu, e⟩ := hext D (hG g hg) h _ hr
    have huS := res_mem_span (X.basicOpen_le h) S (hTgS g hg hu)
    rw [e] at huS
    have hunit : IsUnit ((X.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom h ^ k) :=
      (isUnit_res_of_le_basicOpen h (X.basicOpen_le h) le_rfl).pow _
    change res E hWV a ∈ Submodule.span Γ(X, X.basicOpen h) (res E le_top '' S)
    exact mem_of_isUnit_smul_mem _ hunit huS

/-- Over the affine opens contained in `U`, a submodule sheaf which is the tilde of a module there
has the extension property `ExtendsOver`. -/
theorem extendsOver_of_forall_tilde {hN : IsLocal N}
    (hF : ∀ V : X.affineOpens, (V : X.Opens) ≤ U → ∃ M : ModuleCat.{u} Γ(X, (V : X.Opens)),
      Nonempty ((tilde.functor Γ(X, (V : X.Opens))).obj M ≅ specRestriction (toModules N hN) V)) :
    ExtendsOver U N := by
  intro V hVU g t ht
  obtain ⟨M, ⟨e⟩⟩ := hF V hVU
  have : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
  have hloc : IsLocalizing (modulesSpecToSheaf.obj ((toModules N hN).restrict V.2.fromSpec)) :=
    isLocalizing_of_iso (modulesSpecToSheaf.mapIso e) (isLocalizing_tilde M)
  obtain ⟨n, u, hu⟩ := exists_pow_smul_extension_of_isLocalizing (toModules N hN) V.2 hloc g
    (⟨t, ht⟩ : N.obj (op (X.basicOpen g)))
  exact ⟨n, (u : N.obj (op (V : X.Opens))).1, (u : N.obj (op (V : X.Opens))).2,
    congrArg Subtype.val hu⟩

/-- **Extension of coherent subsheaves from an open subset of an affine Noetherian scheme**
(Hartshorne II, Exercise 5.15(c)). Let `X` be an affine Noetherian scheme, `E` a quasi-coherent
`𝒪_X`-module, `U ⊆ X` open, and `N ⊆ E` a submodule sheaf whose restriction to `U` is coherent:
over every affine open `V ⊆ U`, `N|_V ≅ M̃` for a finitely generated `Γ(X, V)`-module `M`. Then
there is a coherent submodule sheaf `N' ⊆ E` with `N'(V) = N(V)` for every open `V ⊆ U`, that is,
`N'|_U = N|_U` as subsheaves of `E|_U`.

A subsheaf `F ⊆ E|_U` is given here as the restriction to `U` of a submodule sheaf `N ⊆ E`; every
`F` arises so, for instance from `N(V) = {s | s|_{V ∩ U} ∈ F(V ∩ U)}`, and only the values of `N`
on opens contained in `U` enter the hypotheses and the conclusion. -/
theorem exists_isCoherent_extension [IsAffine X] [IsNoetherian X] [E.IsQuasicoherent]
    (hN : IsLocal N)
    (hF : ∀ V : X.affineOpens, (V : X.Opens) ≤ U → ∃ M : ModuleCat.{u} Γ(X, (V : X.Opens)),
      Module.Finite Γ(X, (V : X.Opens)) M ∧
        Nonempty ((tilde.functor Γ(X, (V : X.Opens))).obj M ≅ specRestriction (toModules N hN) V)) :
    ∃ (N' : E.val.Submodule) (hN' : IsLocal N'), IsCoherent (toModules N' hN') ∧
      ∀ V : X.Opens, V ≤ U → sub N' V = sub N V := by
  refine exists_isCoherent_eq_on hN
    (extendsOver_of_forall_tilde fun V hVU => (hF V hVU).imp fun _ h => h.2) fun V hVU => ?_
  obtain ⟨M, hM, ⟨e⟩⟩ := hF V hVU
  obtain ⟨ei⟩ := module_linearEquiv_sections_of_tilde_iso (toModules N hN) V M e
  exact Module.Finite.equiv ei

/-- **Every local section lies in a coherent subsheaf** (the content of Hartshorne II,
Exercise 5.15(a)). On an affine Noetherian scheme, every section of a quasi-coherent `E` over an
open `V` is a section of the span of finitely many global sections, which is coherent
(`isCoherent_spanSheaf`); these span sheaves form a directed family (`spanSheaf_mono`), so `E` is
the directed union of its coherent subsheaves. -/
theorem exists_finite_mem_spanSheaf [IsAffine X] [IsNoetherian X] [E.IsQuasicoherent]
    (V : X.Opens) (s : Γ(E, V)) : ∃ S : Set Γ(E, ⊤), S.Finite ∧ s ∈ sub (spanSheaf S) V := by
  classical
  let T : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  have hcov : ∀ x : V, ∃ g : Γ(X, ⊤), X.basicOpen g ≤ V ∧ (x : X) ∈ X.basicOpen g :=
    fun x => (isAffineOpen_top X).exists_basicOpen_le x trivial
  choose gx hgxV hgx using hcov
  obtain ⟨F, hF⟩ := (NoetherianSpace.isCompact (V : Set X)).elim_finite_subcover
    (fun x : V => (X.basicOpen (gx x) : Set X)) (fun _ => (X.basicOpen _).isOpen)
    (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hgx _⟩)
  choose n t ht using fun x : V => exists_pow_smul_extension_of_isAffineOpen E
    (isAffineOpen_top X) (gx x) (res E (hgxV x) s)
  refine ⟨Set.range fun x : F => t x.1, Set.finite_range _, fun y hy => ?_⟩
  obtain ⟨x, hxF, hyx⟩ := Set.mem_iUnion₂.1 (hF hy)
  let W : X.affineOpens := X.affineBasicOpen (U := T) (gx x)
  refine ⟨W, hgxV x, hyx, ?_⟩
  change res E (hgxV x) s ∈ Submodule.span Γ(X, X.basicOpen (gx x)) (res E le_top '' _)
  have hu : IsUnit ((X.presheaf.map (homOfLE (X.basicOpen_le (gx x))).op).hom (gx x) ^ n x) :=
    (isUnit_res_of_le_basicOpen (gx x) (X.basicOpen_le _) le_rfl).pow _
  have key : res E (le_top : X.basicOpen (gx x) ≤ ⊤) (t x) ∈
      Submodule.span Γ(X, X.basicOpen (gx x))
        (res E le_top '' Set.range fun x : F => t x.1) :=
    Submodule.subset_span ⟨t x, ⟨⟨x, hxF⟩, rfl⟩, rfl⟩
  have e : res E (le_top : X.basicOpen (gx x) ≤ ⊤) (t x) =
      (X.presheaf.map (homOfLE (X.basicOpen_le (gx x))).op).hom (gx x) ^ n x •
        res E (hgxV x) s := ht x
  rw [e] at key
  exact mem_of_isUnit_smul_mem _ hu key

/-- **Extension of coherent sheaves from an open subset of an affine Noetherian scheme**
(Hartshorne II, Exercise 5.15(b)). Let `X` be an affine Noetherian scheme, `U ⊆ X` open and `F` a
coherent sheaf on `U`. Then there is a coherent sheaf `F'` on `X` with `F'|_U ≅ F`. It is a
coherent submodule sheaf of the pushforward of `F` to `X` (`exists_isCoherent_eq_on`). -/
theorem exists_isCoherent_restrict_iso [IsAffine X] [IsNoetherian X] (U : X.Opens)
    (F : U.toScheme.Modules) (hF : IsCoherent F) :
    ∃ F' : X.Modules, IsCoherent F' ∧ Nonempty (F'.restrict U.ι ≅ F) := by
  have h4F := ((coherent_affine_local_tfae F).out 0 3).mp hF
  have : F.IsQuasicoherent := ((quasicoherent_affine_local_tfae _).out 2 0).mp fun W =>
    (h4F W).2
  obtain ⟨E, hE, ⟨e⟩⟩ : ∃ E : X.Modules, E.IsQuasicoherent ∧ Nonempty (E.restrict U.ι ≅ F) :=
    ⟨_, isQuasicoherent_pushforward_of_qcqs U.ι F,
      ⟨(Scheme.Modules.restrictFunctorAdjCounitIso U.ι).app F⟩⟩
  have himage : ∀ V : X.Opens, V ≤ U → U.ι ''ᵁ U.ι ⁻¹ᵁ V = V := fun V hVU => by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.2 hVU]
  have hfin : ∀ V : X.affineOpens, (V : X.Opens) ≤ U →
      Module.Finite Γ(X, V) (sub (⊤ : E.val.Submodule) V) := by
    intro V hVU
    have hW : IsAffineOpen (U.ι ⁻¹ᵁ (V : X.Opens)) :=
      V.2.preimage_of_isOpenImmersion U.ι (by rwa [Scheme.Opens.opensRange_ι])
    have h1 : Module.Finite Γ(U, U.ι ⁻¹ᵁ (V : X.Opens)) Γ(F, U.ι ⁻¹ᵁ (V : X.Opens)) :=
      (h4F ⟨_, hW⟩).1
    let W := U.ι ⁻¹ᵁ (V : X.Opens)
    let f : Γ(F, W) ≃ₗ[Γ(U, W)] Γ(E.restrict U.ι, W) :=
      { toFun := e.inv.app W
        invFun := e.hom.app W
        map_add' := map_add _
        map_smul' := fun r x => Scheme.Modules.Hom.app_smul e.inv r x
        left_inv := fun a => (congrArg (fun φ : F ⟶ F => φ.app W a) e.inv_hom_id :)
        right_inv := fun a =>
          (congrArg (fun φ : E.restrict U.ι ⟶ E.restrict U.ι => φ.app W a) e.hom_inv_id :) }
    have h2 : Module.Finite Γ(U, W) Γ(E.restrict U.ι, W) := Module.Finite.equiv f
    rw [CoherentAux.finite_restrict_iff, CoherentAux.finite_congr_opens E (himage V hVU)] at h2
    exact Module.Finite.equiv
      (Submodule.topEquiv (R := Γ(X, (V : X.Opens))) (M := Γ(E, (V : X.Opens)))).symm
  have hext : ExtendsOver U (⊤ : E.val.Submodule) := fun V _ g t _ => by
    obtain ⟨n, u, hu⟩ := exists_pow_smul_extension_of_isAffineOpen E V.2 g t
    exact ⟨n, u, trivial, hu⟩
  obtain ⟨N', hN', hcoh, heq⟩ := exists_isCoherent_eq_on (isLocal_top (E := E)) hext hfin
  let φ : toModules N' hN' ⟶ E := ⟨N'.ι⟩
  have : IsIso ((Scheme.Modules.restrictFunctor U.ι).map φ) := by
    rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
    intro W
    have hsub : sub N' (U.ι ''ᵁ W) = ⊤ :=
      (heq _ ((U.ι.image_le_opensRange W).trans (Scheme.Opens.opensRange_ι U).le)).trans rfl
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨fun a b h => Subtype.ext h, fun y => ⟨⟨y, ?_⟩, rfl⟩⟩
    change (show Γ(E, U.ι ''ᵁ W) from y) ∈ sub N' (U.ι ''ᵁ W)
    rw [hsub]
    exact Submodule.mem_top
  exact ⟨toModules N' hN', hcoh, ⟨asIso ((Scheme.Modules.restrictFunctor U.ι).map φ) ≪≫ e⟩⟩

end Hartshorne
